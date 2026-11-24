# L-meta-1692: local research, not a completed official proof

Base:4da2f0456c50716aa775ef77aa729d96fb388e07. Branch:grok/L-meta-1692.

The official assertion is the64-gate lower bound for fan-in-two AND/OR circuits separating all52 incident point-line inputs from234 quadrangle negatives of the order3 projective plane. It is NOT proved here. No upstream PR has been opened. The official skeleton is intentionally not included in this research commit.

## Checked auxiliary sources

- `lean/PEqualNP/Outside/Grok1692TwoHotBridge.lean`: any AND/OR circuit rejecting the quadrangle negatives rejects every nonincident two-hot input, including repeated indices (singleton inputs). The finite geometry certificate itself is kernel-checked; Python is only a certificate generator. Original checker ACCEPTED1636 constants.
- `lean/PEqualNP/Outside/Grok1692FirstMixedGate.lean`: a full fold-prefix induction, not a flat-circuit assumption. For an accepting combined trace with both component singleton traces rejected, a first mixed gate exists and is a binary AND whose operands have complementary singleton support. Original checker ACCEPTED1630 constants.
- `lean/PEqualNP/Outside/Grok1692EdgeFirstAND.lean`: self-contained composition, specialized to the EXACT official point/line input encoding and all52 incidents. The exact52-incident specialization passed the unchanged original checker: 1665 constants, only the three standard axioms. Its predecessor for arbitrary accepted two-hot inputs passed1660 constants. Final source SHA256:a613a4bf2f46e698fbdab8481a914514b67461f23a6d314f593a8ced0938c4a3.

Each accepted theorem uses only propext, Classical.choice, Quot.sound; no holes or additional axioms. These are partial tools, not the posted64-gate conclusion. Standalone statement files and full verifier logs are retained in the private batch-019 notes; the statement to check is the type of each last, fully-qualified top-level theorem.

Reproduction, from the repository root with the pinned Lean toolchain on PATH:

    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692TwoHotBridge.lean notes/grok/L-meta-1692-checkstatements/bridge.txt check
    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692FirstMixedGate.lean notes/grok/L-meta-1692-checkstatements/firstmix.txt check
    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692EdgeFirstAND.lean notes/grok/L-meta-1692-checkstatements/edge52.txt check

The checker, definitions root and toolchain were not edited.

## Real remaining obstacle

A single point-star AND creates four incident pair certificates. Distinct edges therefore do not inject into gates. An intermediate gate can also create nonedge pairs that later ANDs filter out. Counting certificate trees duplicates shared OR gates. A global savings-versus-repair account for reused OR subcircuits is still missing; do not assume every internal AND is safe.

The samples do not force the full incidence function: the extra term L0 AND L4 AND L10 is zero on every official sample but true on its three-line-only input. Adding it to the true incidence function preserves the samples and changes the global function (not a counterexample to64: the obvious construction has67 gates).

## Focused continuation

A bounded two-star replacement search for8 gates on9 inputs timed out after40 seconds; this is NOT UNSAT. A pinned known9-gate construction was SAT and independently re-evaluated on all64 distinct projected samples. No search process remains.

Paper argument to formalize next: all9 inputs of the two-star window are essential; an8-gate fan-in-two circuit on9 essential inputs must be read-once. A read-once monotone formula rejecting singletons and having a connected two-hot graph using every variable has a complete-bipartite two-hot graph (an OR root disconnects it; an AND root gives a biclique). The two-star graph contains an induced P4 and is not a biclique, so it needs at least9 gates even with nested ANDs. This argument is not yet Lean-verified. Existing `MetaComplexity/Helpers/Support.lean` provides `cnt_step`, `cnt_suppsFrom`, `dep_lower`; its equality case is the useful next target. This local lower bound alone would still NOT imply64 globally.

Other finite audits: all234 negative supports are maximal independent7-sets. A vertex-cover OR clause rejecting one must be its19-vertex complement, so a pure CNF needs234 different clauses (at least467 gates including binary AND combination); this restricted-class argument is not a general-circuit lower bound. Two translation orbits of quadrangles {0,1,4,6} and {0,1,5,11} give an optimal26-negative cover of all273 nonedge pairs and26 singletons; the compact26-cover is Python-verified only, distinct from the accepted bridge certificate.

## Batch020: strict support sharing is not free

`Grok1692OverlapSupport.lean` strengthens the usual joint-support count. After t binary-or-smaller gates, if two DISTINCT frontier wires share any original input, their joint syntactic support has size at most t+1 rather than t+2. It proves a stronger invariant for arbitrary frontiers: any shared support makes the ordinary bound STRICT. The induction replaces a fresh gate by its at-most-two operands; either frontier size loses slack immediately, or an overlap witness survives into the expanded frontier.

The same checked theorem also proves the semantic equality case: a fan-in-at-most-two circuit depending essentially on all n inputs and using exactly n-1 gates (n>=2) must output its final binary gate, whose two DISTINCT operand supports are disjoint and cover all n inputs. This holds for arbitrary gate operations and even permits default-false/forward references; no hidden monotonicity or internal-safety premise is used. Essentiality is linked to syntactic support by a full fold-prefix agreement proof, not assumed from support membership.

The final, stronger conjunction was ACCEPTED by the unchanged original checker:1661 project constants; only propext, Quot.sound, Classical.choice. Source SHA256:de751ab8f919e12873d9adb3f1ecccd3d76ba1ee8ac0e47524fbfc671df8ba86. The earlier1638-constant acceptance checked only the first overlap conclusion, not this final conjunction.

    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692OverlapSupport.lean notes/grok/L-meta-1692-checkstatements/overlap.txt check

This is the missing equality-case premise of the nine-input/two-star argument. It does NOT yet prove9 for that window or64 for the official task. The intended next step is to exclude both disjoint-support root operations using the connected, non-biclique two-hot graph. Most importantly, this one-unit support penalty cannot be added across overlapping windows without a new global accounting lemma. Such addition would double-count gates, exactly the unresolved main obstacle.

## Batch020: the two-star nine-gate lower bound is now formal

`Grok1692TwoStarLower.lean` proves that any fan-in-at-most-two AND/OR circuit on9 inputs, false at zero and correct on all repeated/ordinary two-hot pairs of two four-edge stars with one common leaf, uses at least9 gates. The unchanged original checker ACCEPTED1701 constants with only the standard3 axioms. Source SHA256:3d196d2dffa95cf2fed8861c597c63e9e0f73a6b3ebd583bf77c3827033d20ab.

This replaces the earlier8-gate SAT TIMEOUT with an actual proof of impossibility. It permits arbitrary circuit depth, arbitrary behavior on weight>=3 inputs, unsafe internal gates, and even default-false forward reads. It does NOT assume the circuit computes the full graph function. The proof derives essentiality from positive edges and rejected singletons, applies the newly proved tight-budget root partition, and rules out OR by connectivity and AND by the non-biclique pattern. The graph argument uses explicit paths, not a large exhaustive partition certificate.

    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692TwoStarLower.lean notes/grok/L-meta-1692-checkstatements/twostar9.txt check
    python3 notes/grok/L-meta-1692-two-star-audit.py

The audit independently checks the exact embedding: local indices0,1 are P0,P1 and2..8 are L0,L12,L4,L10,L1,L5,L11. This matches point-minus-line in {0,1,3,9}. It also independently checks a matching explicit9-gate circuit on all512 inputs. The upper construction is the obvious OR of the two AND/star expressions; it is separate from the lower-bound proof.

**Still missing:** no theorem lets us sum these local9 costs across the13 overlapping stars of the full plane. The official64 bound remains unproved, no official task-closing PR has been opened. A genuine next target is an overlap-aware amortization invariant, not more isolated windows or another reduction that assumes the desired global bound.

### Matching upper bound also kernel-verified

`Grok1692TwoStarUpper.lean` constructs9 AND/OR gates and proves the exact two-star Boolean function on ALL inputs, not just512 sampled evaluations. Original checker ACCEPTED1620 constants, standard3 axioms; source SHA256:011df032170807dfc0830cdb3ff3b0dd64c47b2688df130fec3a8efb43031277. Together with the independently checked lower theorem this settles the local optimum at9, while the official64 bound remains open.

    node tools/check-lean.mjs lean/PEqualNP/Outside/Grok1692TwoStarUpper.lean notes/grok/L-meta-1692-checkstatements/twostar9upper.txt check

### Concrete global accounting obstruction (finite audit, NOT a new Lean theorem)

There are78 two-point/star windows. The canonical64-gate circuit simplifies to9 live gates in each window, hence702 total local gate occurrences. A tempting sufficient global inequality would be `sum(local_live_gates) <= 12*S - 66`; together with the new local9 lower bound this would yield S>=64. **This inequality is FALSE for ordinary constant/idempotency/dead-code pruning.** Add3 gates to the canonical circuit: `h=L0 OR L1`, then output `F AND (F OR h)`. By Boolean absorption it is still the same valid incidence function, now67 gates, but the ordinary pruning sum becomes849, exceeding12*67-66=738. This is a counterexample to the accounting shortcut, NOT to the official64 lower bound. An absorption-aware normalization removes this particular obstruction; no valid general normalization/amortization theorem has been proved.

    python3 notes/grok/L-meta-1692-restriction-obstruction.py

A more geometry-specific audit: for any two distinct lines, their OR survives in21 pair windows:12 contain the lines' intersection point and9 select one private point from each line. Thus a blanket per-gate multiplicity bound of12 is also false. Those9 cross-private windows are potential leak/repair contexts if the shared OR feeds the two point stars; the finite count alone does NOT prove9 repair gates are necessary. The genuinely needed next theorem must charge shared-OR savings against repairs in a size-minimal/appropriately normalized circuit, allowing nested AND filters. Repeating more isolated9-window bounds cannot close this gap.

## Batch021: oriented global charge disproved; scoped normalizer prototyped

See `1692-charging-audit/README.md` for exact definitions, reproductions and limitations. The deletion-normalized window inequality `R_P<=12*S-66` fails on the dual64-gate line-star circuit (1092>702), which also passes all256 single-gate0/1/operand bypass tests. This is not just the earlier redundant67-gate absorption example. A case split on the unknown minimum size shows that the inequality cannot hold for ALL global minimum separators either. Choosing the better point/line orientation does not fix it for merely locally irredundant circuits: mixed65-gate examples give725,735,744>714. These65-gate circuits are not claimed globally minimum.

A distinct constructive route remains: hoist an internal AND that rejects every forbidden sample by retaining its actual output, setting its OLD uses to0, simplifying the suffix and OR-ing the saved wire into the output. Finite tests give nonincreasing size and strictly fewer full AND-ancestor pairs; the desired generic compiler theorem is precisely recorded but NOT proved. It would support the open CleanTop normalization child, not by itself the64-gate bound. The prototype passes303 selected small full-truth-table cases, reduces67->64 in13 steps, and gives a68->67 example that preserves all286 samples while intentionally changing the full function. No new Lean theorem or official PR is claimed this batch.
