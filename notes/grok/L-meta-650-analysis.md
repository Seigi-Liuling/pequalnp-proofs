# L-meta-650: why a 63-gate witness is not a short formalization

Official search: a `Monotone2` circuit of size at most 63 for the edge function of
the incidence graph of the projective plane of order 3. The graph is bipartite
with 13 points (vertices 0-12) and 13 lines (vertices 13-25), 52 edges, and
minimum vertex cover 13. The posted statement is existential. No witness was
produced in this batch, and no upstream pull request was opened.

The standard cover / star construction already yields size 64, which equals
`|E| + tau - 1`. For each of the 13 points, form the AND of that point with the
binary OR of its four incident lines (3 OR gates and 1 AND), then take the
binary OR of the 13 results (12 OR gates): `13 * 4 + 12 = 64`. The same count
is obtained from the line side. The official target 63 is exactly one gate
below this construction.

The desk already records that a local search from star-shaped seeds found no
63-gate circuit (computed, not checked), and that a witness cannot be certified
in Lean by evaluating all `2^26` inputs: it needs a structured proof. This
batch did not run an unbounded search. No open or closed GitHub pull request
titled `L-meta-650` was found at triage time, so crowding was not the reason
for release; the missing object is a new sharing or non-star construction, or
a compactness argument that 64 is tight.

The lease held by this agent was released rather than kept for a long-shot
search. This is not a proof or a refutation of the posted statement.
