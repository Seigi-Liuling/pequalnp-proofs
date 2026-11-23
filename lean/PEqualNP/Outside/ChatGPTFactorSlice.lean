import PEqualNP.Defs

namespace PEqualNP.Outside.ChatGPTFactorSlice_aux

-- For fixed point inputs, neighbors are exactly the line variables whose
-- presence should make the output true. The two factors may accept extras.
theorem fixed_points {n : ℕ} (neighbors : Finset (Fin n))
    (a b : Finset (Fin n) → Prop) (ha : Monotone a) (hb : Monotone b)
    (h : ∀ y, (a y ∧ b y) ↔ ∃ j ∈ y, j ∈ neighbors) :
    (∀ y, a y ↔ ∃ j ∈ y, j ∈ neighbors) ∨
    (∀ y, b y ↔ ∃ j ∈ y, j ∈ neighbors) := by
  classical
  let z := Finset.univ \ neighbors
  have hz : ¬ (a z ∧ b z) := by
    intro hab
    obtain ⟨j, hj, hn⟩ := (h z).mp hab
    exact (Finset.mem_sdiff.mp hj).2 hn
  have sub {y : Finset (Fin n)} (hy : ¬ ∃ j ∈ y, j ∈ neighbors) : y ⊆ z := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hn => hy ⟨j,hj,hn⟩⟩
  by_cases az : a z
  · right
    intro y
    exact ⟨fun by' => by
      by_contra hn
      exact hz ⟨az, hb (sub hn) by'⟩, fun hit => ((h y).mpr hit).2⟩
  · left
    intro y
    exact ⟨fun ay => by
      by_contra hn
      exact az (ha (sub hn) ay), fun hit => ((h y).mpr hit).1⟩

open PEqualNP.CircuitLowerBounds

-- Wires 0 and 1 are points; 2 and 3 are lines.
-- Wires 8 and 12 feed the output AND. With both points false, the
-- second factor needs both lines, so its quadratic term is essential.
def matchingCircuit (out : ℕ) : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [0, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 2]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [6, 11]⟩,
    ⟨.and, [8, 12]⟩], out⟩

theorem matching_monotone : PEqualNP.MetaComplexity.Monotone2 (matchingCircuit 13) := by
  intro g hg
  simp only [matchingCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem matching_counterexample :
    (matchingCircuit 8).lineDeg 4 {2, 3} = 1 ∧
    (matchingCircuit 12).lineDeg 4 {2, 3} = 2 ∧
    (matchingCircuit 13).lineDeg 4 {2, 3} = 3 ∧
    (∀ p q r s : Bool, (matchingCircuit 13).eval [p,q,r,s] = ((p && r) || (q && s))) ∧
    (matchingCircuit 8).eval [true,false,false,true] = true ∧
    (matchingCircuit 13).eval [true,false,false,true] = false ∧
    (matchingCircuit 12).eval [false,true,true,false] = true ∧
    (matchingCircuit 13).eval [false,true,true,false] = false ∧
    (∀ r s : Bool, (matchingCircuit 12).eval [false,false,r,s] = (r && s)) := by
  decide

end PEqualNP.Outside.ChatGPTFactorSlice_aux

theorem PEqualNP.Outside.ChatGPTFactorSlice : ∀ {n : ℕ} (neighbors : Finset (Fin n)) (a b : Finset (Fin n) → Prop),
    Monotone a → Monotone b →
    (∀ y, (a y ∧ b y) ↔ ∃ j ∈ y, j ∈ neighbors) →
    (∀ y, a y ↔ ∃ j ∈ y, j ∈ neighbors) ∨
    (∀ y, b y ↔ ∃ j ∈ y, j ∈ neighbors) := by
  intro n N a b ha hb h
  exact PEqualNP.Outside.ChatGPTFactorSlice_aux.fixed_points N a b ha hb h
