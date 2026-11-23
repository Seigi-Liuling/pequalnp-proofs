import Mathlib
import PEqualNP.Defs

-- A local structural ingredient for L-meta-612, not a proof of that task.
-- If an AND of two monotone functions never produces a false positive for a
-- C4-free graph edge function, one input has at most one singleton witness.
namespace PEqualNP.Outside.Grok612LowAnd_aux

theorem pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (h : ∃ i j : Fin n, G.Adj i j ∧
      decide (i = u ∨ i = v) = true ∧ decide (j = u ∨ j = v) = true) :
    G.Adj u v := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have hi' : i = u ∨ i = v := of_decide_eq_true hi
  have hj' : j = u ∨ j = v := of_decide_eq_true hj
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact False.elim (G.irrefl hij)
  · exact hij
  · exact hij.symm
  · exact False.elim (G.irrefl hij)

end PEqualNP.Outside.Grok612LowAnd_aux

theorem PEqualNP.Outside.Grok612LowAnd :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (a b : (Fin n → Bool) → Bool),
    (∀ u v w z : Fin n, u ≠ v → u ≠ w → u ≠ z →
      v ≠ w → v ≠ z → w ≠ z →
      G.Adj u v → G.Adj v w → G.Adj w z → ¬ G.Adj z u) →
    (∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      a x = true → a y = true) →
    (∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      b x = true → b y = true) →
    (∀ x : Fin n → Bool, a x = true → b x = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    (Finset.univ.filter (fun u : Fin n => a (fun i => decide (i = u)) = true)).card ≤ 1 ∨
    (Finset.univ.filter (fun u : Fin n => b (fun i => decide (i = u)) = true)).card ≤ 1 := by
  classical
  intro n G a b hC4 ha hb hsafe
  let A := Finset.univ.filter (fun u : Fin n => a (fun i => decide (i = u)) = true)
  let B := Finset.univ.filter (fun u : Fin n => b (fun i => decide (i = u)) = true)
  change A.card ≤ 1 ∨ B.card ≤ 1
  have cross : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v := by
    intro u hu v hv
    have hau : a (fun i => decide (i = u)) = true := (Finset.mem_filter.mp hu).2
    have hbv : b (fun i => decide (i = v)) = true := (Finset.mem_filter.mp hv).2
    apply PEqualNP.Outside.Grok612LowAnd_aux.pair_adj G u v
    apply hsafe (fun i => decide (i = u ∨ i = v))
    · apply ha (fun i => decide (i = u)) _ _ hau
      intro i hi
      have hi' : i = u := of_decide_eq_true hi
      simp [hi']
    · apply hb (fun i => decide (i = v)) _ _ hbv
      intro i hi
      have hi' : i = v := of_decide_eq_true hi
      simp [hi']
  by_contra h
  push Not at h
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨v, hv, z, hz, hvz⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have huv := cross u hu v hv
  have huz := cross u hu z hz
  have hwv := cross w hw v hv
  have hwz := cross w hw z hz
  exact hC4 u v w z (G.ne_of_adj huv) huw (G.ne_of_adj huz)
    (G.ne_of_adj hwv).symm hvz (G.ne_of_adj hwz)
    huv hwv.symm hwz huz.symm
