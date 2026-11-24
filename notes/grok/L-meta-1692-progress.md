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
