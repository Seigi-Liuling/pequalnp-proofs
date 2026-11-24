# L-meta-1692: global charging pressure test, not a64-gate proof

The official task remains unproved here. This batch adds no Lean proof and opens no official PR. The previous local optimum9 is unchanged and kernel-verified in the sibling research files. The executable results below are finite audits, not substitutes for generic theorems.

## Exact failed candidate

For each unordered pair of points p,q (78 choices), retain these2 point inputs and the7 lines meeting at least one of them, and set all other inputs false. Evaluate every wire on ALL512 assignments. Delete constants and semantically equal earlier-wire aliases; delete dead gates. Let R_P(C) be the sum of the remaining gate counts. Define R_L dually for pairs of lines. This is **deletion/alias normalization**, not optimal local circuit resynthesis.

The tested candidate was:

    R_P(C) <= 12*size(C) - 66.

Together with the proved local9 lower bound (78*9=702), this would imply size>=64. Earlier the67-gate absorption-redundant example disproved the version using only ordinary pruning. The stronger semantic-pruning version is also false, much more decisively:

| Correct separator | gates | R_P | R_L | RHS |
|---|---:|---:|---:|---:|
| Point-centered13-star circuit |64|702|1092|702|
| Line-centered13-star circuit |64|1092|702|702|
| Mixed cover, move2 edges at P0 to an extra point star |65|1086|725|714|
| Mixed cover, move3 edges |65|1077|735|714|
| Mixed cover, move4 edges |65|1068|744|714|

Both64-gate circuits compute the exact incidence function by distributivity. Each line-centered circuit restricted to a point pair has one common-line branch costing2 gates, six private-leaf ANDs, and six output ORs:14 total. No two retained wire functions coincide, and no retained gate is equal in function to either operand. Every one of the64 gates, replaced in ALL readers/output by0,1,or either original operand, destroys at least one of the286 official samples (256 explicit tests per circuit). Thus dead-code, constant, alias, and one-gate sample-bypass normalization cannot repair the candidate.

The65-gate mixed circuits also pass all286 samples and all260 one-gate bypass tests. They refute even `min(R_P,R_L) <= 12*size-66` under this local irredundancy condition. They are NOT globally size-minimal: the64-gate star circuit is already known. No false claim of minimality is made.

### Adding GLOBAL size-minimality does not save the universal fixed-orientation claim

Let m be the minimum number of gates among all official separators; m<=64 by the explicit star circuit. Every point-window restriction of any correct separator admits a no-larger9-input AND/OR circuit, so the previous local theorem gives R_P>=702 (instantiating the generic restriction compiler is not yet Lean-formalized here).

* If m<=63, every minimum separator violates R_P<=12*m-66.
* If m=64, the line-star circuit is itself minimum, and1092>702 violates the same inequality.

Consequently, **the statement for ALL globally minimum separators is untenable**, not merely missing an absorption hypothesis. This is a paper deduction from the local lower bound and explicit constructions; no new Lean acceptance is claimed.

The existential weakening, "there is SOME minimum separator with R_P<=12*m-66", is equivalent to m=64: the bound forces m>=64, while if m=64 the point-star circuit supplies the witness. This does not rule out proving a genuinely new normal-form theorem; it means that theorem is substantial, not a free normalization assumption.

### Sample-only junk is different from full-function redundancy

F OR threshold4(the13 line bits) still rejects every negative because each has only3 true line inputs. Its131-gate DP implementation has R_P=2585>1506 even after exact local semantic pruning. The extra branch changes the full Boolean function but can be removed while preserving the official samples. The audit explicitly confirms root bypass to F. Thus a sample-minimality argument must not silently use full-function minimality, or vice versa.

## A narrower constructive normalization worth pursuing

The failed oriented charge is abandoned. A separate, precise possible step is to hoist a **negative-safe internal AND**, directly matching `cleanNormalize` in the still-open reduction PR4249:

https://github.com/brilliant-hq/pequalnp-proofs/pull/4249

Working lemma, for an arbitrary binary read-back AND/OR circuit C and chosen gate g with a later reader:

1. Keep the prefix computing the actual value G of g, for a separate saved output wire.
2. In g's OLD readers, set g to0, propagate constants, and compact the suffix.
3. Output the OR of the compacted old output and saved G.

The resulting Boolean function is exactly F_C OR G, by splitting on G=false/true. If G is false on all forbidden samples, correctness of every official sample is preserved; full-function equality is NOT required. The first old reader of g simplifies away (AND with0 or OR with0), saving at least1 gate; the new output costs at most1 gate, so size does not increase.

If g is an AND with an AND descendant, use the number of ALL ordered AND-ancestor pairs, `PEqualNP.TopForm.andPairs`, as a strict descent measure. All new ANDs originate injectively from old ANDs; compaction introduces no ancestor relation absent before; g has no AND descendants after hoisting. At least the old chosen pair disappears. Generic proof of this origin/ancestor injection is STILL TODO, not inferred from random tests. Counting only DIRECT AND readers is insufficient: AND -> OR -> AND has nesting but zero direct AND-to-AND edges.

Iterating such a verified step would put every negative-safe AND above all other ANDs (`CleanTop`), although unsafe nested ANDs may remain. This is only one normalization premise, not the full64-gate counting theorem. Current PR4312 also assumes a hard nesting-decrease child, rather than proving it:

https://github.com/brilliant-hq/pequalnp-proofs/pull/4312

### What the prototype actually checked

* Deterministic seed1692;400 small random binary circuits;303 had a chosen nested AND. On every input of each selected circuit: new function=old output OR chosen wire; size never increased; full AND-pair count strictly decreased.
* The67-gate absorption example normalized to64 in13 steps.
* A68-gate example has G=L0 AND L4 AND L10, old output F OR(P0 AND G). G is negative-safe but NOT below the full old output. One hoist gives67 gates, preserves all286 samples, changes the output on the three-line-only input, and decreases AND pairs3->1. One UNSAFE nested pair remains, showing why CleanTop is not flatness.

These are executable tests on **binary** circuits, not a generic proof. Official fan-in<=2 also needs constants/unary preprocessing in the formal statement.

## Formalization plan, not assumed results

Existing `MetaComplexity/Helpers/Elim.lean` supplies `elim_len_lt` (a constant wire read saves a gate), `inv_elim` (the compiler's semantic invariant), and `elim_ok`. Initialize its accumulator with the already computed prefix; the chosen wire's old status is `Stat.const false`, while retaining its actual gate for the saved output. This avoids a new compiler. Remaining tasks are:

1. Preserve exactly-two-input AND/OR/read-back syntax through the pass; first remove nullary/unary gates from the official <=2 model without increasing size.
2. Complete the prefix-cut invariant and final-output reconstruction, giving sample correctness and the size bound.
3. Prove the origin injection and strict `andPairs` decrease; random evidence is not enough.
4. Iterate by well-founded induction to obtain CleanTop. A further, still unknown global OR-sharing/unsafe-AND repair charge is required for64.

No PR should be opened for the official task on the strength of this prototype.

## Reproduction

    python3 notes/grok/1692-charging-audit/charging_stress.py
    python3 notes/grok/1692-charging-audit/safe_hoist_stress.py

Every retained9-input DAG is independently re-evaluated on all512 assignments. Both scripts are bounded, use only the Python standard library, perform no network requests, and overwrite only their deterministic adjacent JSON result files.

## Exact next statement (well-typed, NOT proved)

`safe-hoist-target.txt` records the proposed generic one-step proposition in the existing official definitions. Its type was checked against Mathlib+PEqualNP.Defs; defining a proposition is NOT proving it and no original-checker acceptance is claimed. It requires exact binary AO/read-back syntax, a valid AND gate and a valid AND descendant; concludes an AO/read-back circuit of no greater size, fewer `andPairs`, and full function `old output OR saved gate`. Negative-sample safety is then a separate immediate application.

For the formal compiler, `Elim` can retain all prefix gates; dead-code removal is optional. The initial old-wire status list maps each earlier prefix wire to itself and maps the chosen last prefix wire to constant false. The prefix's ACTUAL chosen wire remains available only to the new output. Every generated suffix gate has an original source gate; the strictly increasing origin map should inject all new AND-ancestor pairs into old pairs, except that no new pair can originate at the saved AND. This is the principal missing generic proof obligation, not another local-window counting exercise.

In the exact binary model, only the constant false needs to be introduced into statuses; the compiler cannot generate constant true from binary AO and false statuses. So a constant-true final status is impossible, and reconstruction uses either the saved wire directly or one final binary OR. The official <=2 model first needs the existing constant/unary elimination pass; positivity and at least one negative exclude a constant final function.

Scope caution: the direct-AND-read measure in PR4312 is zero for the3-gate list `AND(0,1); OR(previous,2); AND(previous,3)` although the full AND-ancestor measure is1. This is NOT a refutation of that reduction (its child has additional <64/correctness hypotheses); it means a generic hoisting proof should use the full `andPairs` measure rather than silently identify the two.
