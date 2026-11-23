# L-gct-086: a checked construction obstruction, not the posted all-n bound

Base: `d2128f2ccece9b4d2df0c1be0755d162db96599d`.
Official hard open step released after a bounded analysis. No proof or refutation of the posted statement is claimed, and no upstream pull request was opened.

## Exact posted statement

There exists a universal constant `C` such that every complex linear space of `n × n` matrices on which the permanent stays equal to `n!` at the all-ones matrix plus the space has dimension at most `C * n`.

Context marks this OPEN and hard. Checked pieces already in the repository:

- a level space of dimension `2n-3` exists (`L-gct-080` / `Helpers.LevelLow`);
- the problem reduces to doubly centred spaces plus at most `2n` (`L-gct-092`);
- the `3 × 3` case is bounded by 3 (`L-gct-094`);
- product-type row spaces are bounded (`L-gct-090`).

A proof is required to use Taylor orders growing with `n`. Failed templates recorded by the desk include any split into a row part and a column part, and any argument of bounded order. The determinant analogue is quadratic, so a proof must use a property the permanent has and the determinant lacks.

## What was not repeated

The sharp two-row quadratic bound `dim L + 1 ≤ q` for admissible `2 × q` spaces was independently derived from the nondegenerate polar form of the off-diagonal product, then found already checked as `PEqualNP.Gct.Helpers.STwoRow.main` and used by `L-gct-101`. That argument was not re-proved or submitted.

## Checked local obstruction

`Grok086SquareZeroObstruction.lean` exhibits an explicit `6 × 6` complex matrix

`T = u vᵀ - v uᵀ`

with `u = (1,-1,i,-i,0,0)` and `v = (1,1,i,i,-2i,-2)`. It is skew-symmetric, doubly centred, and square-zero, but

`perm(J + T) = 4944 ≠ 6! = 720`.

The original project checker accepted this exact existential statement: `ACCEPTED (check)`, 1092 kernel-rechecked constants, axioms only `propext`, `Quot.sound`, and `Classical.choice`. There is no `sorry`, extra axiom or `native_decide`.

Independent exact Gaussian-integer arithmetic (Python, `notes` under batch-003) gives the scalar family `perm(J + sT) = 720 + 1152 s^4 + 3072 s^6`. A kernel `decide` of that full polynomial identity was attempted once, capped at 120 seconds, and got stuck on `Eq.rec`; that stronger identity is therefore only a computational record, not a formal claim. The formally checked fact is the `s = 1` evaluation above.

This shows that a tempting nilpotent / square-zero enlargement of a doubly centred space need not remain on the permanent level set. It is a construction obstruction, not a counterexample to L-gct-086, and not a dimension upper bound.

## Precise remaining obligation

A genuine proof of the posted statement still needs a uniform all-`n` dimension bound that controls higher-order Taylor terms, not only the already-checked quadratic two-row piece and not only nilpotent examples that leave the level set. A refutation would need a family of level spaces whose dimensions grow superlinearly in `n`. Neither was obtained in this bounded batch, so the official lease is released rather than held for a long-shot attempt.

## Reproduction

From the repository root, with the pinned Lean toolchain and Mathlib cache:

```
node tools/check-lean.mjs lean/PEqualNP/Outside/Grok086SquareZeroObstruction.lean notes/grok/L-gct-086-square-zero.statement.txt check
```

This checks the local obstruction, not the posted L-gct-086 statement. No shared definitions, build configuration, checker or task statement was changed.
