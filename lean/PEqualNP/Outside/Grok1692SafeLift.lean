import PEqualNP.MetaComplexity.Helpers.EdgeFnModel

/-! Research only: semantic core of sample-safe lifting, not the 64-gate bound.
If an erased gate agrees with its redirect whenever h=false, deleting it and
appending OR(output,h) computes OLD_OUTPUT OR h, with exactly the old gate count.
Unlike a full-function lift this needs no assumption h <= OLD_OUTPUT. -/
namespace PEqualNP.Outside
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.EdgeFn

private theorem safeLiftCore (N : ℕ) (gs : List Gate) (o p a h : ℕ)
    (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N+p) (hh : h < N+p)
    (ho : o < N+gs.length)
    (hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N+p) = vl gs x a) :
    let gs2 := rdel N p a gs ++ [⟨GateOp.or, [rd N p a o,h]⟩]
    CleanL N gs2 ∧ gs2.length = gs.length ∧
      ∀ x : Fin N → Bool, vl gs2 x (N+(gs.length-1)) = (vl gs x o || vl gs x h) := by
  have hlen := rdel_length N p a gs hp
  have hro : rd N p a o < N+(gs.length-1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p a gs ++ [⟨GateOp.or,[rd N p a o,h]⟩] with hgs2
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p a gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1,e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p a gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl,rd N p a o,h,by omega,by omega,rfl⟩
  have hlast : gs2[gs.length-1]? = some ⟨GateOp.or,[rd N p a o,h]⟩ := by
    rw [hgs2,List.getElem?_append_right (by omega)]
    rw [show gs.length-1-(rdel N p a gs).length = 0 by omega]; rfl
  refine ⟨hcl2,by simp [hgs2]; omega,?_⟩
  intro x
  rw [vl_gate _ hcl2 x _ _ hlast]
  have e1 : vl gs2 x (rd N p a o) = vl (rdel N p a gs) x (rd N p a o) :=
    vl_append_lt _ _ x _ (by omega)
  have e2 : vl gs2 x h = vl gs x h := by
    rw [vl_append_lt _ _ x _ (by omega),rdel_prefix N p a gs hcl hp ha x h hh]
  simp only [List.map,GateOp.eval,e1,e2]
  cases hx : vl gs x h
  · rw [rdel_all N p a gs hcl hp ha x (hS x hx) o]; simp
  · simp

private theorem pureOrTailStep (N : ℕ) (gs : List Gate) (o p a h : ℕ)
    (hp : p < gs.length) :
    let gs2 := rdel N p a gs ++ [⟨GateOp.or,[rd N p a o,h]⟩]
    ∀ b, p < b → (∀ j g, b ≤ j → gs[j]? = some g → g.op = GateOp.or) →
      ∀ j g, b-1 ≤ j → gs2[j]? = some g → g.op = GateOp.or := by
  dsimp only
  intro b hpb ht j g hjb hj
  by_cases hj' : j < (rdel N p a gs).length
  · rw [List.getElem?_append_left hj',rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0,hg0,rfl⟩ := Option.map_eq_some_iff.1 hj
    exact ht (j+1) g0 (by omega) hg0
  · rw [List.getElem?_append_right (by omega)] at hj
    obtain ⟨e1,e2⟩ := List.getElem?_eq_some_iff.1 hj
    simp at e1
    have ej : j = (rdel N p a gs).length := by omega
    subst ej
    simp at e2
    subst e2
    rfl

theorem Grok1692SafeLift :
let clean := fun (N : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) =>
  ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gs[j]? = some g →
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ i, i < N+j ∧ g.inputs = [i]) ∨
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ∃ i k, i < N+j ∧ k < N+j ∧ g.inputs = [i,k])
let wire := fun (N : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
  (x : Fin N → Bool) (w : ℕ) =>
    (PEqualNP.CircuitLowerBounds.Circuit.mk gs w).eval (List.ofFn x)
let rename := fun (N p a w : ℕ) => if w < N+p then w else if w = N+p then a else w-1
let del := fun (N p a : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) =>
  gs.take p ++ (gs.drop (p+1)).map (fun g =>
    (⟨g.op,g.inputs.map (rename N p a)⟩ : PEqualNP.CircuitLowerBounds.Gate))
∀ (N : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (o p a h : ℕ),
  clean N gs → p < gs.length → a < N+p → h < N+p → o < N+gs.length →
  (∀ x : Fin N → Bool, wire N gs x h = false → wire N gs x (N+p) = wire N gs x a) →
  let gs2 := del N p a gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or,[rename N p a o,h]⟩]
  clean N gs2 ∧ gs2.length = gs.length ∧
    (∀ x : Fin N → Bool, wire N gs2 x (N+(gs.length-1)) =
      (wire N gs x o || wire N gs x h)) ∧
    ∀ b, p < b → (∀ j g, b ≤ j → gs[j]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ j g, b-1 ≤ j → gs2[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  dsimp only
  intro N gs o p a h hcl hp ha hh ho hS
  have hc := safeLiftCore N gs o p a h hcl hp ha hh ho hS
  exact ⟨hc.1,hc.2.1,hc.2.2,pureOrTailStep N gs o p a h hp⟩

end PEqualNP.Outside
