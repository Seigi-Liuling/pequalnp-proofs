import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Grok612UnsafeInternal_aux

open PEqualNP.CircuitLowerBounds

def graph : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
    (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

def circ : Circuit where
  gates := [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [6, 7]⟩]
  output := 8

end PEqualNP.Outside.Grok612UnsafeInternal_aux

theorem PEqualNP.Outside.Grok612UnsafeInternal :
    ∃ (G : SimpleGraph (Fin 4)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ u v w z : Fin 4, u ≠ v → u ≠ w → u ≠ z →
      v ≠ w → v ≠ z → w ≠ z →
      G.Adj u v → G.Adj v w → G.Adj w z → ¬ G.Adj z u) ∧
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 5 ∧
    (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 4, G.Adj u v ∧ x u = true ∧ x v = true) ∧
    C.gates[2]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩ ∧
    ∃ x : Fin 4 → Bool, (C.wires (List.ofFn x)).getD 6 false = true ∧
      ¬ ∃ u v : Fin 4, G.Adj u v ∧ x u = true ∧ x v = true := by
  let _ : DecidableRel PEqualNP.Outside.Grok612UnsafeInternal_aux.graph.Adj := fun u v =>
    inferInstanceAs (Decidable ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
      (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
      (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)))
  refine ⟨PEqualNP.Outside.Grok612UnsafeInternal_aux.graph,
    PEqualNP.Outside.Grok612UnsafeInternal_aux.circ, ?_, ?_, rfl, ?_, rfl, ?_⟩
  · decide
  · intro g hg
    simp only [PEqualNP.Outside.Grok612UnsafeInternal_aux.circ,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · exact ⟨(fun i => decide (i = 1 ∨ i = 3)), by decide, by decide⟩
