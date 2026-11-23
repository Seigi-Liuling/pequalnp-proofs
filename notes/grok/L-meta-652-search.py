#!/usr/bin/env python3
"""Exhaustive search for official L-meta-652 shard 1 (BitVec encoding).

Shard 1 of 2: exclude a joint FanInTwo circuit of size at most 14 for the
three cyclic matchings of K(3,3).

Semantics match PEqualNP.CircuitLowerBounds and MetaComplexity.FanInTwo
at upstream 633410bb850f9e0b3d6a46387bd2b7c24fad2423, independently
checked by a Lean-faithful evaluator:

AND [] = True, OR [] = False, NOT [] = True, NOT ignores later inputs,
missing wires read False, size = number of gates, ops in {and,or,not},
fan-in <= 2.

Existence is complete: every Lean FanInTwo circuit of size k reduces to
one in this encoding by replacing out-of-range inputs with a virtual
FALSE source, 0-ary AND/NOT with virtual TRUE, and 0-ary OR with virtual
FALSE.  AND/OR arguments may be swapped (they are commutative).
"""

from __future__ import annotations

import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from z3 import And, BitVec, BitVecVal, Bool, If, Not, Or, Solver, sat, unsat, unknown

N_IN = 6
ALL_T = range(64)
MASK = (1 << 64) - 1


def bit(t: int, j: int) -> int:
    return (t >> j) & 1


def target_tables() -> tuple[int, int, int]:
    m0 = m1 = m2 = 0
    for t in ALL_T:
        x = [bit(t, j) for j in range(6)]
        if (x[0] and x[3]) or (x[1] and x[4]) or (x[2] and x[5]):
            m0 |= 1 << t
        if (x[0] and x[4]) or (x[1] and x[5]) or (x[2] and x[3]):
            m1 |= 1 << t
        if (x[0] and x[5]) or (x[1] and x[3]) or (x[2] and x[4]):
            m2 |= 1 << t
    return m0, m1, m2


def eval_op(op: str, in_vals: list[bool]) -> bool:
    if op == "and":
        return all(in_vals)
    if op == "or":
        return any(in_vals)
    if op == "not":
        return not (in_vals[0] if in_vals else False)
    raise ValueError(op)


@dataclass(frozen=True)
class Gate:
    op: str
    inputs: tuple[int, ...]


@dataclass
class Circuit:
    gates: list[Gate]


def wires(c: Circuit, x: list[bool]) -> list[bool]:
    w = list(x)
    for g in c.gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in g.inputs]
        w.append(eval_op(g.op, vals))
    return w


def circuit_tables(c: Circuit) -> list[int]:
    tables = [0] * (N_IN + len(c.gates))
    for t in ALL_T:
        x = [bool(bit(t, j)) for j in range(N_IN)]
        wvals = wires(c, x)
        for i, v in enumerate(wvals):
            if v:
                tables[i] |= 1 << t
    return tables


def matches_targets(c: Circuit, targets: tuple[int, int, int]) -> tuple[bool, list[int] | None]:
    tables = circuit_tables(c)
    outs = []
    for tgt in targets:
        try:
            outs.append(tables.index(tgt))
        except ValueError:
            return False, None
    return True, outs


def explicit_15() -> Circuit:
    gs: list[Gate] = []
    triples = [
        ((0, 3), (1, 4), (2, 5)),
        ((0, 4), (1, 5), (2, 3)),
        ((0, 5), (1, 3), (2, 4)),
    ]
    for (a, b), (c, d), (e, f) in triples:
        i0 = N_IN + len(gs)
        gs.append(Gate("and", (a, b)))
        i1 = N_IN + len(gs)
        gs.append(Gate("and", (c, d)))
        i2 = N_IN + len(gs)
        gs.append(Gate("and", (e, f)))
        j0 = N_IN + len(gs)
        gs.append(Gate("or", (i0, i1)))
        gs.append(Gate("or", (j0, i2)))
    return Circuit(gs)


# Source layout for gate g: 0=FALSE, 1=TRUE, then wires 0..N_IN+g-1
# Lean input indices are recovered by: FALSE/TRUE become a 0-ary gate, or
# we emit a real out-of-range index for FALSE and a 0-ary AND/NOT for TRUE.


def encode_size(k: int, targets: tuple[int, int, int], timeout_ms: int | None) -> tuple[str, Circuit | None, float]:
    s = Solver()
    if timeout_ms is not None:
        s.set("timeout", timeout_ms)

    false_bv = BitVecVal(0, 64)
    true_bv = BitVecVal(MASK, 64)
    wire_bv = [BitVecVal(sum((bit(t, j) << t) for t in ALL_T), 64) for j in range(N_IN)]
    # gate bitvectors
    gate_bv = [BitVec(f"g_{g}", 64) for g in range(k)]

    is_and, is_or, is_not = [], [], []
    # selectors: for each gate, two sources among nsrc = 2 + N_IN + g
    sel0: list[list] = []
    sel1: list[list] = []

    def sources(g: int):
        # [FALSE, TRUE, *inputs, *earlier gates]
        return [false_bv, true_bv] + wire_bv + gate_bv[:g]

    for g in range(k):
        a, o, n = Bool(f"and_{g}"), Bool(f"or_{g}"), Bool(f"not_{g}")
        s.add(Or(a, o, n))
        s.add(Or(Not(a), Not(o)), Or(Not(a), Not(n)), Or(Not(o), Not(n)))
        is_and.append(a); is_or.append(o); is_not.append(n)
        nsrc = 2 + N_IN + g
        r0 = [Bool(f"s0_{g}_{i}") for i in range(nsrc)]
        r1 = [Bool(f"s1_{g}_{i}") for i in range(nsrc)]
        s.add(Or(r0))
        s.add(Or(r1))
        for i in range(nsrc):
            for j in range(i + 1, nsrc):
                s.add(Or(Not(r0[i]), Not(r0[j])))
                s.add(Or(Not(r1[i]), Not(r1[j])))
        # AND/OR: source0 index <= source1 index (commutativity)
        for i in range(nsrc):
            for j in range(i):
                s.add(Or(Not(a), Not(r0[i]), Not(r1[j])))
                s.add(Or(Not(o), Not(r0[i]), Not(r1[j])))
        sel0.append(r0)
        sel1.append(r1)

        srcs = sources(g)
        src0 = false_bv
        src1 = false_bv
        for i, bv in enumerate(srcs):
            src0 = If(r0[i], bv, src0)
            src1 = If(r1[i], bv, src1)
        and_v = src0 & src1
        or_v = src0 | src1
        not_v = ~src0
        s.add(gate_bv[g] == If(a, and_v, If(o, or_v, not_v)))

    # Outputs may be FALSE (all-zero table — not our targets), TRUE, an input, or a gate.
    # Targets have popcount 37, so they are not TRUE/FALSE or single inputs (popcount 32).
    all_bvs = [false_bv, true_bv] + wire_bv + gate_bv
    out_sel = []
    for r in range(3):
        row = [Bool(f"out_{r}_{i}") for i in range(len(all_bvs))]
        s.add(Or(row))
        for i in range(len(all_bvs)):
            for j in range(i + 1, len(all_bvs)):
                s.add(Or(Not(row[i]), Not(row[j])))
        out_sel.append(row)
        acc = false_bv
        for i, bv in enumerate(all_bvs):
            acc = If(row[i], bv, acc)
        s.add(acc == BitVecVal(targets[r], 64))

    t0 = time.perf_counter()
    res = s.check()
    dt = time.perf_counter() - t0
    if res == sat:
        m = s.model()

        def chosen(row):
            for i, b in enumerate(row):
                if bool(m.evaluate(b, model_completion=True)):
                    return i
            raise RuntimeError("no selector")

        gates = []
        for g in range(k):
            if bool(m.evaluate(is_and[g], model_completion=True)):
                op = "and"
            elif bool(m.evaluate(is_or[g], model_completion=True)):
                op = "or"
            else:
                op = "not"
            i0 = chosen(sel0[g])
            i1 = chosen(sel1[g])

            def to_lean_index(src_i: int, g: int) -> int | None:
                # 0=FALSE, 1=TRUE, 2..= inputs and earlier gates
                if src_i == 0:
                    return None  # virtual FALSE
                if src_i == 1:
                    return "TRUE"  # type: ignore
                return src_i - 2

            def emit_input(src_i: int, g: int) -> int:
                mapped = to_lean_index(src_i, g)
                if mapped is None:
                    return N_IN + k + 10  # out of range -> False
                if mapped == "TRUE":
                    return "TRUE"  # placeholder
                return mapped

            a = emit_input(i0, g)
            b = emit_input(i1, g)
            if op == "not":
                if a == "TRUE":
                    # NOT TRUE = 0-ary OR? NOT [] = True, we need False: OR []
                    # We'll represent NOT TRUE by a 0-ary OR (constant False) if this happens
                    # as a NOT gate... actually we need a NOT of something true.
                    # Constant False as a NOT-gate: not representable as NOT[] (that's True).
                    # Use OR [] instead — but then the op in the model is NOT.
                    # Safer: introduce a 0-ary OR in this position; evaluator only cares
                    # about the computed table, but we must keep the same op if we can.
                    # NOT of out-of-range (False) is True, not False.
                    # Represent constant False as OR [].
                    gates.append(Gate("or", tuple()))
                elif a is None or (isinstance(a, int) and a >= N_IN + k + 10):
                    gates.append(Gate("not", tuple()))  # NOT [] = True? Wait NOT of False = True. Wrong.
                    # FALSE source: NOT FALSE = TRUE. So this NOT gate is constant True: NOT []
                    gates[-1] = Gate("not", tuple())
                else:
                    gates.append(Gate("not", (a,)))
            else:
                ins = []
                for src in (a, b):
                    if src == "TRUE":
                        ins.append("TRUE")
                    elif src is None or (isinstance(src, int) and src >= N_IN + k + 10):
                        ins.append(None)
                    else:
                        ins.append(src)
                # Rewrite 0-ary / unary using virtuals so the Lean gate matches
                if op == "and":
                    # AND with FALSE is FALSE = OR []; AND with TRUE is the other input (or AND[] if both TRUE)
                    if None in ins:
                        gates.append(Gate("or", tuple()))  # const False
                    else:
                        real = [x for x in ins if x != "TRUE"]
                        if len(real) == 0:
                            gates.append(Gate("and", tuple()))  # const True
                        elif len(real) == 1:
                            gates.append(Gate("and", (real[0],)))  # identity, still valid FanInTwo
                        else:
                            gates.append(Gate("and", (real[0], real[1])))
                else:  # or
                    if "TRUE" in ins:
                        gates.append(Gate("and", tuple()))  # const True
                    else:
                        real = [x for x in ins if x is not None]
                        if len(real) == 0:
                            gates.append(Gate("or", tuple()))
                        elif len(real) == 1:
                            gates.append(Gate("or", (real[0],)))
                        else:
                            gates.append(Gate("or", (real[0], real[1])))
        circ = Circuit(gates)
        ok, found = matches_targets(circ, targets)
        if not ok:
            raise RuntimeError(f"SAT model of size {k} failed independent evaluator: {circ}")
        return "sat", circ, dt
    if res == unsat:
        return "unsat", None, dt
    return "unknown", None, dt


def circuit_json(c: Circuit, outs: list[int] | None) -> dict:
    return {
        "size": len(c.gates),
        "gates": [{"op": g.op, "inputs": list(g.inputs)} for g in c.gates],
        "outputs": outs,
    }


def main() -> int:
    out_dir = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    out_dir.mkdir(parents=True, exist_ok=True)
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    targets = target_tables()
    report: dict = {
        "task_id": "L-meta-652",
        "shard": 1,
        "shards": 2,
        "encoding": "bitvec64_onehot_virtual_true_false",
        "started_utc": started,
        "targets": {"m0": targets[0], "m1": targets[1], "m2": targets[2]},
        "sanity": {},
        "sizes": {},
    }
    c15 = explicit_15()
    ok, outs = matches_targets(c15, targets)
    report["sanity"]["explicit_15_matches"] = ok
    report["sanity"]["explicit_15_outputs"] = outs
    report["sanity"]["explicit_15_size"] = len(c15.gates)
    print("sanity explicit_15", ok, "outs", outs, "size", len(c15.gates), flush=True)
    if not ok:
        (out_dir / "search-652-report.json").write_text(json.dumps(report, indent=2) + "\n")
        return 2

    timeout_ms = 15 * 60 * 1000
    found_le14 = None
    for k in range(14, -1, -1):
        print(f"=== SAT size {k} start ===", flush=True)
        status, circ, dt = encode_size(k, targets, timeout_ms)
        entry = {"status": status, "seconds": round(dt, 3)}
        if circ is not None:
            ok, outs = matches_targets(circ, targets)
            entry["evaluator_ok"] = ok
            entry["circuit"] = circuit_json(circ, outs)
            found_le14 = entry
            print(f"size {k} SAT in {dt:.3f}s outs={outs}", flush=True)
            report["sizes"][str(k)] = entry
            break
        print(f"size {k} {status} in {dt:.3f}s", flush=True)
        report["sizes"][str(k)] = entry
        if status == "unknown":
            report["incomplete"] = f"solver unknown at size {k}"
            break
        (out_dir / "search-652-report.json").write_text(json.dumps(report, indent=2) + "\n")

    report["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if found_le14 is not None:
        report["conclusion"] = "WITNESS_SIZE_LE_14"
    elif report.get("incomplete"):
        report["conclusion"] = "INCOMPLETE"
    elif all(report["sizes"].get(str(k), {}).get("status") == "unsat" for k in range(0, 15)):
        report["conclusion"] = "EXHAUSTED_NO_SIZE_LE_14"
    else:
        report["conclusion"] = "UNEXPECTED"
    (out_dir / "search-652-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("CONCLUSION", report["conclusion"], flush=True)
    return 0 if report["conclusion"] in {"EXHAUSTED_NO_SIZE_LE_14", "WITNESS_SIZE_LE_14"} else 1


if __name__ == "__main__":
    sys.exit(main())
