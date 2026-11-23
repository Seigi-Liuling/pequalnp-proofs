import Mathlib
import PEqualNP.Defs.LineDegree

namespace PEqualNP.Outside.GrokLineDegreeZero

open PEqualNP.CircuitLowerBounds

lemma foldMax_zero (l : List ℕ) (h : l.foldr max 0 = 0) :
    ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a = 0 := by
      have hx := Nat.le_max_left a (l.foldr max 0)
      change max a (l.foldr max 0) = 0 at h
      rw [h] at hx
      omega
    have hl : l.foldr max 0 = 0 := by
      simpa only [List.foldr_cons, ha, Nat.zero_max] using h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih hl b hb

lemma gate_zero_inputs (g : Gate) (d : List ℕ) (h : g.lineDegree d = 0) :
    ∀ i ∈ g.inputs, d.getD i 0 = 0 := by
  unfold Gate.lineDegree at h
  split_ifs at h
  · intro i hi
    exact (List.sum_eq_zero_iff_forall_eq_nat.mp h) _ (List.mem_map_of_mem hi)
  · intro i hi
    exact foldMax_zero _ h _ (List.mem_map_of_mem hi)

lemma gate_agree (g : Gate) (d : List ℕ) (u v : List Bool)
    (h : ∀ i, d.getD i 0 = 0 → u.getD i false = v.getD i false)
    (hz : g.lineDegree d = 0) :
    g.op.eval (g.inputs.map fun i => u.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (gate_zero_inputs g d hz i hi)

lemma agree_append (d : List ℕ) (u v : List Bool) (a : ℕ) (b c : Bool)
    (hdu : d.length = u.length) (huv : u.length = v.length)
    (h : ∀ i, d.getD i 0 = 0 → u.getD i false = v.getD i false)
    (hbc : a = 0 → b = c) :
    ∀ i, (d ++ [a]).getD i 0 = 0 →
      (u ++ [b]).getD i false = (v ++ [c]).getD i false := by
  intro i hi
  by_cases hlt : i < d.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = d.length
    · subst i
      have hd : (d ++ [a]).getD d.length 0 = a := by
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp
      rw [hd] at hi
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hdu, huv] using hbc hi
    · rw [List.getD_eq_default (u ++ [b]) false (by simp; omega),
          List.getD_eq_default (v ++ [c]) false (by simp; omega)]

lemma run_agree (gs : List Gate) :
    ∀ (d : List ℕ) (u v : List Bool), d.length = u.length → u.length = v.length →
      (∀ i, d.getD i 0 = 0 → u.getD i false = v.getD i false) →
      ∀ i,
        (gs.foldl (fun ds g => ds ++ [g.lineDegree ds]) d).getD i 0 = 0 →
        (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun j => vs.getD j false)]) u).getD i false =
        (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun j => vs.getD j false)]) v).getD i false := by
  induction gs with
  | nil => intro d u v _ _ h; exact h
  | cons g gs ih =>
    intro d u v hdu huv h
    apply ih
    · simpa using hdu
    · simpa using huv
    · exact agree_append d u v _ _ _ hdu huv h (gate_agree g d u v h)

end PEqualNP.Outside.GrokLineDegreeZero

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.GrokLineDegreeZero :
    ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (x y : Fin n → Bool),
      (∀ i : Fin n, i.val ∉ marked → x i = y i) →
      C.lineDeg n marked = 0 → C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  intro n marked C x y hxy hz
  apply PEqualNP.Outside.GrokLineDegreeZero.run_agree C.gates
      ((List.range n).map fun i => if i ∈ marked then 1 else 0)
      (List.ofFn x) (List.ofFn y)
  · simp
  · simp
  · intro i hi
    by_cases hlt : i < n
    · have hn : i ∉ marked := by
        by_contra hm
        simp [List.getD_eq_getElem?_getD, hlt, hm] at hi
      simpa [List.getD_eq_getElem?_getD, hlt] using hxy ⟨i, hlt⟩ hn
    · simp [List.getD_eq_getElem?_getD, hlt]
  · exact hz
