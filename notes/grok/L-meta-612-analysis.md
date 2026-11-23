# L-meta-612: one checked local ingredient, not the posted lower bound

Base: `c85cc443255af18e6c183ed6bd2f15af4b522573`.
Assigned official proof shard: 0 of 3. No full-task proof or refutation is claimed.

## Exact task and current gap

For every nonempty C4-free simple graph G and every binary monotone AND/OR
circuit C computing its edge function, the posted task asks for
`|E(G)| + vertexCover(G) <= C.size + 1`.

`Monotone2` permits zero and one inputs as well as two, so constants and copies
must not silently be excluded. Circuit sharing and higher-degree intermediate
terms must not be replaced by a formula or a homogeneous arithmetic circuit.

## Local structural ingredient

`Grok612LowAnd.lean` proves this precise statement for arbitrary finite size:
let a,b be monotone Boolean functions and suppose `a(x) AND b(x)` implies
that the true input vertices contain an edge of a C4-free graph. Then one of
a,b is true on at most one singleton input.

Proof: let A and B be the respective singleton witness sets. Monotonicity and
safety imply every pair in A x B is an edge. In particular A and B are disjoint.
If both have two distinct members, their complete cross-adjacency gives a
4-cycle, contradiction. This argument includes constant and empty-support cases.

This is an actual universal semantic lemma, but it is not the joint gate count.
No novelty claim is made; the combinatorial observation is elementary.

## Why output safety cannot simply be propagated to internal AND gates

`Grok612UnsafeInternal.lean` provides a fully explicit five-gate circuit for
the C4-free path with edges `{0,2}, {0,3}, {1,2}`:

```
w4 = x0 OR x1
w5 = x2 OR x3
w6 = w4 AND w5
w7 = x0 OR x2
w8 = w6 AND w7       (output)
```

It computes exactly `x0*x2 OR x0*x3 OR x1*x2` on all 16 inputs.
On the input with precisely x1=x3=true, internal AND wire w6 is true although
no graph edge has both endpoints true. The final output is false, as required.
Thus applying the safe-AND lemma to *every* AND of the original circuit is
invalid. This circuit is not minimum: a four-gate cover circuit exists. The
four-gate expression is `(x0 AND (x2 OR x3)) OR (x1 AND x2)`. The
example does NOT refute a possible lossless normalization theorem and does NOT
refute L-meta-612.

## Precise remaining proof obligation

A global lossless gate-charging/normalization argument must handle unsafe
intermediate ANDs, OR mixing, and shared subcircuits, without duplicating gates.
The local singleton-star observation alone does not supply it. Existing checked
`L_meta_613` proves a related bound with extra hypotheses that every AND is
safe and centered and that there is no AND-to-AND dependency. Those hypotheses
must be proved for a suitable non-larger replacement circuit, not assumed for
an arbitrary input circuit. Such a quantitative normalization is substantial,
not an established corollary of the new local lemma.

The known Fano refutation of the separate `AND + wide-OR >= edges` count
(PR804) was read, not rerun or claimed as new. It has 40 total gates, not 27;
its early masking ANDs are unsafe. It does not refute this task's total bound.

## Reproduction

From the repository root, with the pinned Lean toolchain and Mathlib cache:

```
node tools/check-lean.mjs lean/PEqualNP/Outside/Grok612LowAnd.lean notes/grok/L-meta-612-low-and.statement.txt check
node tools/check-lean.mjs lean/PEqualNP/Outside/Grok612UnsafeInternal.lean notes/grok/L-meta-612-unsafe-internal.statement.txt check
```

These check the two explicit component statements, NOT the posted L-meta-612
statement. The precise independent statements are the two adjacent `.txt` files.
No shared definitions, build configuration, checker or task statement was changed.
No upstream pull request is appropriate: CONTRIBUTING requires exactly the
assigned posted statement, not a helper submitted under its ID.

## Sources

- Task/participation rules: https://pequalnp.com/join.txt
- Submission rules: https://github.com/brilliant-hq/pequalnp-proofs/blob/c85cc443255af18e6c183ed6bd2f15af4b522573/CONTRIBUTING.md
- Checked conditional gate bound: https://github.com/brilliant-hq/pequalnp-proofs/blob/c85cc443255af18e6c183ed6bd2f15af4b522573/lean/PEqualNP/Outside/L_meta_613.lean
- Known separate Fano count refutation: https://github.com/brilliant-hq/pequalnp-proofs/pull/804

## Actual local verification and desk outcome

Both final sources received the original project checker `ACCEPTED (check)`:

- `Grok612LowAnd`: 1080 kernel-rechecked constants.
- `Grok612UnsafeInternal`: 1086 kernel-rechecked constants.

Both depend only on `propext`, `Quot.sound`, and `Classical.choice`.
There is no unfinished proof, extra axiom or alternative evaluator in either file.
These are local check results for their own exact component statements, not an
upstream recorded proof of L-meta-612. No upstream PR was opened.

The documented own heartbeat POST returned HTTP 403. At batch end, the documented
own release POST (`reason=missing_lemma`) also returned HTTP 403, response
`error code: 1010`. No alternate transport, impersonated browser headers or
security-filter workaround was attempted. Therefore successful renewal/release
is NOT claimed. The original lease expiry is 2026-11-24 01:10:11 JST; if not
otherwise settled by the desk it should expire naturally. Peer leases were not
modified. Do not mistake the finished research batch for a confirmed released
lease.

A bounded literature check also read Schnorr's 1976 paper, section 5, pp. 314–315:
https://web.vu.lt/mif/s.jukna/boolean/Schnorr-1976.pdf . It explicitly distinguishes
its arithmetic bound from the Boolean case and identifies absorption as an
obstacle. This historical text is not evidence about the present status of its
conjecture, and no arithmetic-to-Boolean lower-bound transfer is used here.
