import PEqualNP.Defs

namespace PEqualNP.Outside.ChatGPTTests523_aux

def edge (s : Finset (Fin 8)) : Bool :=
  decide ((0 ∈ s ∧ 1 ∈ s) ∨ (1 ∈ s ∧ 2 ∈ s) ∨ (2 ∈ s ∧ 3 ∈ s) ∨
    (3 ∈ s ∧ 4 ∈ s) ∨ (4 ∈ s ∧ 5 ∈ s) ∨ (0 ∈ s ∧ 5 ∈ s) ∨
    (0 ∈ s ∧ 6 ∈ s) ∨ (1 ∈ s ∧ 7 ∈ s))

def positive : List (Finset (Fin 8)) :=
  [{0,1}, {1,2}, {2,3}, {3,4}, {4,5}, {0,5}, {0,6}, {1,7}]

def negative : List (Finset (Fin 8)) :=
  [{1,4,6}, {1,3,5,6}, {0,3,7}, {0,2,4,7}, {2,4,6,7}, {2,5,6,7}, {3,5,6,7}]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem positive_cover : ∀ s : Finset (Fin 8),
    edge s = true → ∃ p ∈ positive, p ⊆ s := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem negative_cover : ∀ s : Finset (Fin 8),
    edge s = false → ∃ p ∈ negative, s ⊆ p := by decide

end PEqualNP.Outside.ChatGPTTests523_aux

open PEqualNP.Outside.ChatGPTTests523_aux

theorem PEqualNP.Outside.ChatGPTTests523 :
    let edge : Finset (Fin 8) → Bool := fun s =>
      decide ((0 ∈ s ∧ 1 ∈ s) ∨ (1 ∈ s ∧ 2 ∈ s) ∨ (2 ∈ s ∧ 3 ∈ s) ∨
        (3 ∈ s ∧ 4 ∈ s) ∨ (4 ∈ s ∧ 5 ∈ s) ∨ (0 ∈ s ∧ 5 ∈ s) ∨
        (0 ∈ s ∧ 6 ∈ s) ∨ (1 ∈ s ∧ 7 ∈ s))
    let positive : List (Finset (Fin 8)) :=
      [{0,1}, {1,2}, {2,3}, {3,4}, {4,5}, {0,5}, {0,6}, {1,7}]
    let negative : List (Finset (Fin 8)) :=
      [{1,4,6}, {1,3,5,6}, {0,3,7}, {0,2,4,7}, {2,4,6,7}, {2,5,6,7}, {3,5,6,7}]
    ∀ f : Finset (Fin 8) → Bool, Monotone f →
      (∀ p ∈ positive, f p = true) → (∀ p ∈ negative, f p = false) →
      ∀ s, f s = edge s := by
  change ∀ f : Finset (Fin 8) → Bool, Monotone f →
    (∀ p ∈ positive, f p = true) → (∀ p ∈ negative, f p = false) →
    ∀ s, f s = edge s
  intro f hf hp hn s
  cases he : edge s with
  | false =>
    obtain ⟨p, hm, hs⟩ := negative_cover s he
    have h := hf hs
    rw [hn p hm] at h
    cases w : f s
    · rfl
    · exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa only [w] using h))
  | true =>
    obtain ⟨p, hm, hs⟩ := positive_cover s he
    have h := hf hs
    rw [hp p hm] at h
    cases w : f s
    · exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa only [w] using h))
    · rfl
