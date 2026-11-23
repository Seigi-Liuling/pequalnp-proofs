# L-gct-190: bounded search, no dimension-8 witness found

Base at analysis time: `03ba9a38bed4458bdb81ce6bdd0559cc64df0b6f`.
Official search gap: a 5x5 complex permanent level space of dimension 8,
one above the checked record `2n-3 = 7` from `L-gct-080` / `Helpers.LevelLow`.
The posted statement is existential. No witness was found, so the statement
was neither proved nor refuted. No upstream pull request.

## What was tested, exactly

The LevelLow hook construction was reproduced and sanity-checked:
`perm(J + hook) = 5!` on random elements of the standard 7-dimensional
last-row/last-column space, and the same construction at other corners
`(0,0)`, `(1,2)`, `(2,2)` also stays on the level set.

1. Sparse interior directions. All unique matrices of the forms
   `E_{ab}-E_{ba}` on the top-left 4x4, 3-cycle skew matrices, and
   `uv^T-vu^T` for 4-vectors of weight at most 2 (125 unique matrices).
   24 of them stay on the level set as a single line `sA` for
   `s in {-2,-1,1,2,3}`. None of those 24 remains a level space when
   mixed with the hook basis (`perm(J + hook_basis_i + s A)` fails).

2. Sums of two hooks. For the standard hook at corner `(4,4)` plus a
   hook at every other corner, the span has dimension 10, 12 or 14 and
   in every case is not a level space. Explicit failing coefficient
   vectors are recorded in `batch-004/two-hook-search.json`.

Reproducible scripts: `/workspace/pnp-grok-notes/batch-004/` (local persistent
notes). These computations are exact integer arithmetic over the 5x5 permanent,
not a Lean proof and not an exhaustive search of all 8-dimensional subspaces.

## What this does not show

It does not prove that no 8-dimensional 5x5 level space exists. It only
shows that the obvious enlargements of the record construction — adding a
small skew/rank-at-most-2 interior direction, or summing two hooks — fail.
A genuine proof of the posted existential still needs an explicit 8-dimensional
witness. A refutation would need a complete classification or another compact
argument that every 5x5 level space has dimension at most 7.

## Other open pull requests

https://github.com/brilliant-hq/pequalnp-proofs/pull/675 and
https://github.com/brilliant-hq/pequalnp-proofs/pull/678 are titled as
L-gct-190 but add `L_nullity_subspace.lean` / `L_nullity_rank.lean`, not
the assigned file, and do not claim the posted statement. They were not
treated as a solution and were not duplicated.

## Reproduction of the hook sanity and the two-hook obstruction

The Python scripts `dim8-search` logic and `two-hook-search.json` in the
persistent notes directory reconstruct the tests above. No shared
definitions, checker or task statement was changed.
