# L-meta-651: bounded proof-shard analysis

**Status: no proof of the assigned lower bound, no counterexample, and no upstream PR.**
This note records reproducible computational analysis of official desk proof shard 2:
"gate elimination from a least circuit, using the symmetry of the graph".
It is not a claim of mathematical novelty or a machine-checked Lean theorem.

## Exact target

The desk asks for the nonexistence of an AND/OR (fan-in at most two) and NOT circuit
with at most 19 gates computing the edge function of this labeled Petersen graph:

```
01 12 23 34 40 05 16 27 38 49 57 79 96 68 85
```

Inputs are 0 through 9. A satisfying proof must establish the full posted
`not (HasCircuitSize 10 edgeFunction 19)` statement, including NOT gates. None of
the computations below is such a proof.

## Checks performed

`L-meta-651-gate-elimination.py` uses Python's standard library only.

- Enumerates all 1024 vertex subsets: minimum vertex cover size is 6;
  independence number is 4; there are 5 minimum vertex covers.
- Enumerates graph automorphisms, checking adjacency and nonadjacency: 120
  automorphisms, acting transitively on all 10 vertices.
- Builds an explicit monotone 20-gate circuit from a minimum cover and checks its
  output on all 1024 inputs. The full wire list is in the JSON output. This only
  reproduces the already-known upper bound; it is not a 19-gate refutation.
- Explores 4678 distinct restriction states of the form
  `OR(A) OR edge(G[R])`, with isolated vertices removed from `R`.
- Checks all 49840 essential-variable restriction identities for these states
  using exact 1024-bit truth tables, not random sampling.

## Precise limitation of the elementary elimination route

The numerical recurrence uses only:

1. the general essential-support bound `number_of_essential_inputs - 1`;
2. the known forest graph-function value `|A| + |E| + tau - 1`;
3. one eliminated gate per fixed essential variable when the restricted function
   is nonconstant, as in the existing project lemma `L014`.

Both fixed values and every essential variable are tried. The strongest bound
obtainable from this specified recurrence at the Petersen root is **11**, not 20.
This is a computational fact about this proof template, **not** an upper bound on
all possible gate-elimination proofs and **not** a proof that Petersen's circuit
complexity is 11.

For every choice of first vertex, fixing it false gives child-bound 10 and fixing
it true gives child-bound 9. Vertex symmetry therefore identifies equivalent
cases, but cannot by itself strengthen this particular recurrence. One best path
fixes vertices 0, 1, 2 and 8 false, reaching a forest with known bound 7, and hence
`4 + 7 = 11`.

The missing mathematical ingredient is a stronger *multi-gate charging or
elimination lemma*, or stronger certified lower bounds for the nonforest
restrictions. Merely chaining the existing one-gate rule and using vertex
transitivity leaves a numerical gap of **9 gates**. Proving a monotone-only bound
would also not discharge the stated AND/OR/NOT target.

## Reproduce

```
python3 notes/grok/L-meta-651-gate-elimination.py
```

The program writes `L-meta-651-gate-elimination.result.json` beside itself and
prints the same report. Timing fields may vary. There is no random search, no
external solver, no download, and no claim that Python output is a Lean kernel
certificate.

No `sorry` proof or altered target is being submitted. The official lease is to
be released with `missing_lemma`, not `exhausted`: this is a proof shard, not an
exhaustively searched circuit shard.
