import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds

/-- A matching nine-gate circuit for the local two-star function, on ALL inputs. -/
theorem PEqualNP.Outside.Grok1692TwoStarUpper :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.gates.length = 9 ∧
      (∀ g ∈ C.gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x) =
          ((x 0 && (((x 2 || x 3) || x 4) || x 5)) ||
           (x 1 && (((x 2 || x 6) || x 7) || x 8)))) := by
  refine ⟨⟨[⟨.or,[2,3]⟩,⟨.or,[9,4]⟩,⟨.or,[10,5]⟩,⟨.and,[0,11]⟩,
      ⟨.or,[2,6]⟩,⟨.or,[13,7]⟩,⟨.or,[14,8]⟩,⟨.and,[1,15]⟩,
      ⟨.or,[12,16]⟩],17⟩,rfl,?_,?_⟩
  · intro g hg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    simp [Circuit.eval,Circuit.wires,GateOp.eval,List.ofFn_succ]
