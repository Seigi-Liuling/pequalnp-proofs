# L-meta-652 shard 1 analysis (Grok Bot, 2026-11-24)

Official task: three cyclic matchings of K(3,3), joint FanInTwo circuit size exactly 15.
This batch held official shard 1 of 2: exclude a joint circuit of size at most 14 by exhaustive search.

Base commit: 633410bb850f9e0b3d6a46387bd2b7c24fad2423 (includes already-merged L-meta-700, not our work).

## Statement (exact)

There exists a FanInTwo circuit of size <= 15 with three wires equal to

- m0 = (x0 && x3) || (x1 && x4) || (x2 && x5)
- m1 = (x0 && x4) || (x1 && x5) || (x2 && x3)
- m2 = (x0 && x5) || (x1 && x3) || (x2 && x4)

and there is no such circuit of size <= 14.

FanInTwo means AND, OR and NOT gates of fan-in at most two, with the official empty-input rules
(AND [] = true, OR [] = false, NOT [] = true). Six inputs, 64 assignments. Each target function
is true on 37 of the 64 inputs (inclusion-exclusion on three pairwise 16-point ANDs).

## Upper bound 15

The three matchings can be computed separately: each is three ANDs and two ORs, 5 gates, 15 in all.
An independent Lean-faithful evaluator accepts this construction; the three outputs appear at
wires 10, 15 and 20.

## Search in this batch

- No upstream PR for L-meta-652 was open or merged when the lease was taken.
- ChatGPT had previously released 652 and had no current official task.
- A 64-bit truth-table SAT encoding (virtual true/false sources, AND/OR commutativity, Z3 4.15.4)
  reported UNSAT for sizes 0 (0.001s), 6 (0.35s) and 8 (33s). If the encoding is faithful, at least
  9 gates are required. This is computational evidence, not a Lean proof.
- Size 9 returned unknown after a 180s timeout. Size 14 returned unknown after a 900s timeout.
  The official shard was therefore not completed, and this is not an exhausted certificate.
- No size-<=14 witness was found, and no Lean proof of the posted statement was obtained.

## Not a contribution

Do not treat this note as a proof, a refutation, or a completed search shard.
The official lease was released as out_of_time.
