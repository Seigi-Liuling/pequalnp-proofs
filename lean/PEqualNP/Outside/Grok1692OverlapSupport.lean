import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.Grok1692OverlapSupport

variable {n : ℕ}
def joint (L : List (Finset (Fin n))) (W : Finset ℕ) : Finset (Fin n) :=
  W.biUnion (fun j => L.getD j ∅)
def Overlap (L : List (Finset (Fin n))) (W : Finset ℕ) : Prop :=
  ∃ u ∈ W, ∃ v ∈ W, u ≠ v ∧ ∃ p, p ∈ L.getD u ∅ ∧ p ∈ L.getD v ∅
def Count (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W, (joint L W).card ≤ t + W.card
def Strict (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W, Overlap L W → (joint L W).card < t + W.card

lemma get_snoc_ne (L : List (Finset (Fin n))) (S : Finset (Fin n)) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j ∅ = L.getD j ∅ := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma joint_snoc_ne (L : List (Finset (Fin n))) (S : Finset (Fin n)) (W : Finset ℕ)
    (h : L.length ∉ W) : joint (L ++ [S]) W = joint L W := by
  apply Finset.biUnion_congr rfl
  intro j hj
  exact get_snoc_ne L S j (fun he => h (he ▸ hj))

lemma joint_expand (L : List (Finset (Fin n))) (q W : Finset ℕ) (hd : L.length ∈ W) :
    joint (L ++ [joint L q]) W = joint L (W.erase L.length ∪ q) := by
  calc
    _ = joint (L ++ [joint L q]) (insert L.length (W.erase L.length)) :=
      congrArg (joint (L ++ [joint L q])) (Finset.insert_erase hd).symm
    _ = joint L q ∪ joint (L ++ [joint L q]) (W.erase L.length) := by
      unfold joint
      rw [Finset.biUnion_insert]
      simp
    _ = joint L q ∪ joint L (W.erase L.length) := by
      rw [joint_snoc_ne L (joint L q) (W.erase L.length) (by simp)]
    _ = _ := by simp [joint, Finset.union_biUnion, union_comm]

lemma expansion_card (L : List (Finset (Fin n))) (q W : Finset ℕ)
    (hq : q.card ≤ 2) (hd : L.length ∈ W) :
    (W.erase L.length ∪ q).card ≤ W.card + 1 := by
  have hc := Finset.card_union_le (W.erase L.length) q
  have he := Finset.card_erase_of_mem hd
  have hp : 0 < W.card := Finset.card_pos.mpr ⟨L.length,hd⟩
  omega

lemma overlap_expand (L : List (Finset (Fin n))) (q W : Finset ℕ)
    (hfresh : Disjoint (W.erase L.length) q)
    (hov : Overlap (L ++ [joint L q]) W) : Overlap L (W.erase L.length ∪ q) := by
  obtain ⟨u,hu,v,hv,huv,p,hpu,hpv⟩ := hov
  by_cases hud : u = L.length
  · subst u
    have hvd : v ≠ L.length := Ne.symm huv
    have hvW : v ∈ W.erase L.length := mem_erase.mpr ⟨hvd,hv⟩
    have hpq : p ∈ joint L q := by simpa using hpu
    obtain ⟨a,ha,hpa⟩ := mem_biUnion.mp hpq
    rw [get_snoc_ne L (joint L q) v hvd] at hpv
    refine ⟨a,mem_union_right _ ha,v,mem_union_left _ hvW,?_,p,hpa,hpv⟩
    intro h
    subst a
    exact Finset.disjoint_left.mp hfresh hvW ha
  · by_cases hvd : v = L.length
    · subst v
      have huW : u ∈ W.erase L.length := mem_erase.mpr ⟨hud,hu⟩
      have hpq : p ∈ joint L q := by simpa using hpv
      obtain ⟨a,ha,hpa⟩ := mem_biUnion.mp hpq
      rw [get_snoc_ne L (joint L q) u hud] at hpu
      refine ⟨u,mem_union_left _ huW,a,mem_union_right _ ha,?_,p,hpu,hpa⟩
      intro h
      subst a
      exact Finset.disjoint_left.mp hfresh huW ha
    · rw [get_snoc_ne L (joint L q) u hud] at hpu
      rw [get_snoc_ne L (joint L q) v hvd] at hpv
      exact ⟨u,mem_union_left _ (mem_erase.mpr ⟨hud,hu⟩),
        v,mem_union_left _ (mem_erase.mpr ⟨hvd,hv⟩),huv,p,hpu,hpv⟩

lemma count_step (t : ℕ) (L : List (Finset (Fin n))) (q : Finset ℕ)
    (hq : q.card ≤ 2) (hc : Count t L) : Count (t+1) (L ++ [joint L q]) := by
  intro W
  by_cases hd : L.length ∈ W
  · rw [joint_expand L q W hd]
    have hh := hc (W.erase L.length ∪ q)
    have hb := expansion_card L q W hq hd
    omega
  · rw [joint_snoc_ne L (joint L q) W hd]
    have hh := hc W
    omega

lemma strict_step (t : ℕ) (L : List (Finset (Fin n))) (q : Finset ℕ)
    (hq : q.card ≤ 2) (hc : Count t L) (hs : Strict t L) :
    Strict (t+1) (L ++ [joint L q]) := by
  intro W hov
  by_cases hd : L.length ∈ W
  · rw [joint_expand L q W hd]
    by_cases hsmall : (W.erase L.length ∪ q).card ≤ W.card
    · have hh := hc (W.erase L.length ∪ q)
      omega
    · have hb := expansion_card L q W hq hd
      have he := Finset.card_erase_of_mem hd
      have hu := Finset.card_union_add_card_inter (W.erase L.length) q
      have hp : 0 < W.card := Finset.card_pos.mpr ⟨L.length,hd⟩
      have hfresh : Disjoint (W.erase L.length) q := by
        apply Finset.disjoint_iff_inter_eq_empty.mpr
        apply Finset.card_eq_zero.mp
        omega
      have hh := hs (W.erase L.length ∪ q) (overlap_expand L q W hfresh hov)
      omega
  · rw [joint_snoc_ne L (joint L q) W hd]
    have hh := hc W
    omega

def inputs (n : ℕ) : List (Finset (Fin n)) := List.ofFn (fun i : Fin n => {i})
lemma count_inputs : Count 0 (inputs n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < n
  · simp [inputs,hj]
  · rw [List.getD_eq_default _ _ (by simp [inputs]; omega)]
    simp

lemma mem_inputs (p : Fin n) (j : ℕ) (hp : p ∈ (inputs n).getD j ∅) : j = p.val := by
  by_cases hj : j < n
  · have hl : j < (inputs n).length := by simpa [inputs] using hj
    rw [List.getD_eq_getElem _ _ hl] at hp
    have he : p = (⟨j,hj⟩ : Fin n) := by simpa only [inputs,List.getElem_ofFn,mem_singleton] using hp
    exact (congrArg Fin.val he).symm
  · rw [List.getD_eq_default _ _ (by simp [inputs]; omega)] at hp
    simp at hp

lemma strict_inputs : Strict 0 (inputs n) := by
  intro W hov
  obtain ⟨u,hu,v,hv,hne,p,hpu,hpv⟩ := hov
  exact (hne ((mem_inputs p u hpu).trans (mem_inputs p v hpv).symm)).elim

def supps (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [joint L g.inputs.toFinset]) L

lemma run_bounds (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ t (L : List (Finset (Fin n))), Count t L → Strict t L →
      Count (t+gs.length) (supps gs L) ∧ Strict (t+gs.length) (supps gs L) := by
  induction gs with
  | nil => intro t L hc hs; simpa [supps] using And.intro hc hs
  | cons g gs ih =>
    intro t L hc hs
    have hq : g.inputs.toFinset.card ≤ 2 := le_trans (List.toFinset_card_le _) (hg g (by simp))
    have hrec := ih (fun k hk => hg k (List.mem_cons_of_mem g hk)) (t+1)
      (L ++ [joint L g.inputs.toFinset]) (count_step t L _ hq hc) (strict_step t L _ hq hc hs)
    simpa [supps,List.foldl_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hrec


lemma overlap_bound :
  ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    let L : List (Finset (Fin n)) := gs.foldl
      (fun L g => L ++ [g.inputs.toFinset.biUnion (fun j => L.getD j ∅)])
      (List.ofFn (fun i : Fin n => {i}))
    ∀ a b : ℕ, a ≠ b →
      (∃ p : Fin n, p ∈ L.getD a ∅ ∧ p ∈ L.getD b ∅) →
      (L.getD a ∅ ∪ L.getD b ∅).card ≤ gs.length + 1 := by
  intro n gs hg
  dsimp only
  intro a b hab hp
  have hstrict := (run_bounds gs hg 0 (inputs n) count_inputs strict_inputs).2
  have hover : Overlap (supps gs (inputs n)) {a,b} :=
    ⟨a,by simp,b,by simp,hab,hp⟩
  have hbound := hstrict {a,b} hover
  simp only [zero_add,Finset.card_pair hab,joint,Finset.biUnion_insert,
    Finset.singleton_biUnion] at hbound
  change ((supps gs (inputs n)).getD a ∅ ∪ (supps gs (inputs n)).getD b ∅).card ≤ gs.length+1
  omega

/-- A tight final gate cannot reuse an input support across its two operands. -/
lemma tight_root (gs : List Gate) (g : Gate)
    (hg : ∀ k ∈ gs, k.inputs.length ≤ 2) (hgin : g.inputs.length ≤ 2)
    (htight : gs.length + 2 = n)
    (hfull : joint (supps gs (inputs n)) g.inputs.toFinset = Finset.univ) :
    ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧
      Disjoint ((supps gs (inputs n)).getD a ∅) ((supps gs (inputs n)).getD b ∅) ∧
      (supps gs (inputs n)).getD a ∅ ∪ (supps gs (inputs n)).getD b ∅ = Finset.univ := by
  let L := supps gs (inputs n)
  have hbounds := run_bounds gs hg 0 (inputs n) count_inputs strict_inputs
  have hsmall (a : ℕ) : (L.getD a ∅).card ≤ gs.length + 1 := by
    simpa [joint, L] using hbounds.1 {a}
  have hnotfull (a : ℕ) : L.getD a ∅ ≠ Finset.univ := by
    intro he
    have hh := hsmall a
    rw [he, Finset.card_univ, Fintype.card_fin] at hh
    omega
  cases hi : g.inputs with
  | nil =>
      have he : (∅ : Finset (Fin n)) = Finset.univ := by simpa [joint,hi] using hfull
      have hh := congrArg Finset.card he
      simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hh
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have he : L.getD a ∅ = Finset.univ := by simpa [joint,hi,L] using hfull
          exact (hnotfull a he).elim
      | cons b tail =>
          have ht : tail = [] := by
            have hh := hgin
            simp only [hi, List.length_cons] at hh
            exact List.length_eq_zero_iff.mp (by omega)
          subst tail
          have he : L.getD a ∅ ∪ L.getD b ∅ = Finset.univ := by
            simpa [joint,hi,L] using hfull
          have hab : a ≠ b := by
            intro hh
            subst b
            exact hnotfull a (by simpa using he)
          refine ⟨a,b,rfl,hab,?_,he⟩
          apply Finset.disjoint_left.mpr
          intro p hpa hpb
          have hov : Overlap L {a,b} := ⟨a,by simp,b,by simp,hab,p,hpa,hpb⟩
          have hh := hbounds.2 {a,b} hov
          simp only [zero_add,Finset.card_pair hab,joint,Finset.biUnion_insert,
            Finset.singleton_biUnion] at hh
          change (L.getD a ∅ ∪ L.getD b ∅).card < gs.length + 2 at hh
          rw [he,Finset.card_univ,Fintype.card_fin] at hh
          omega

lemma supps_length (gs : List Gate) (L : List (Finset (Fin n))) :
    (supps gs L).length = L.length + gs.length := by
  induction gs generalizing L with
  | nil => simp [supps]
  | cons g gs ih =>
      simpa [supps,List.foldl_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (L ++ [joint L g.inputs.toFinset])

lemma supps_snoc (gs : List Gate) (g : Gate) (L : List (Finset (Fin n))) :
    supps (gs ++ [g]) L = supps gs L ++ [joint (supps gs L) g.inputs.toFinset] := by
  simp [supps,List.foldl_append]

lemma tight_output (hn : 2 ≤ n) (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (hlen : gs.length + 1 = n)
    (hfull : (supps gs (inputs n)).getD out ∅ = Finset.univ) :
    ∃ pre g a b, gs = pre ++ [g] ∧ out = n + pre.length ∧
      g.inputs = [a,b] ∧ a ≠ b ∧
      Disjoint ((supps pre (inputs n)).getD a ∅) ((supps pre (inputs n)).getD b ∅) ∧
      (supps pre (inputs n)).getD a ∅ ∪ (supps pre (inputs n)).getD b ∅ = Finset.univ := by
  induction gs using List.reverseRecOn with
  | nil => simp at hlen; omega
  | append_singleton pre g ih =>
      have hpre : ∀ k ∈ pre, k.inputs.length ≤ 2 := fun k hk => hg k (by simp [hk])
      have hgin : g.inputs.length ≤ 2 := hg g (by simp)
      have ht : pre.length + 2 = n := by simpa using hlen
      let L := supps pre (inputs n)
      have hLlen : L.length = n + pre.length := by simp [L,supps_length,inputs]
      have hout : out = L.length := by
        by_contra ho
        have he : L.getD out ∅ = Finset.univ := by
          rw [supps_snoc] at hfull
          change (L ++ [joint L g.inputs.toFinset]).getD out ∅ = Finset.univ at hfull
          rw [get_snoc_ne _ _ _ ho] at hfull
          exact hfull
        have hh := (run_bounds pre hpre 0 (inputs n) count_inputs strict_inputs).1 {out}
        simp only [zero_add,joint,Finset.singleton_biUnion,Finset.card_singleton] at hh
        change (L.getD out ∅).card ≤ pre.length + 1 at hh
        rw [he,Finset.card_univ,Fintype.card_fin] at hh
        omega
      have hgate : joint L g.inputs.toFinset = Finset.univ := by
        rw [supps_snoc] at hfull
        change (L ++ [joint L g.inputs.toFinset]).getD out ∅ = Finset.univ at hfull
        rw [hout] at hfull
        simpa using hfull
      obtain ⟨a,b,hab,hne,hdis,hcover⟩ := tight_root pre g hpre hgin ht hgate
      exact ⟨pre,g,a,b,rfl,hout.trans hLlen,hab,hne,hdis,hcover⟩

lemma get_snoc_eq {α : Type} (L : List α) (s d : α) : (L ++ [s]).getD L.length d = s := by simp

def values (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_values (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (supps gs L) (values gs w) (values gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1,h2,h3⟩ := h
    apply ih (L ++ [joint L g.inputs.toFinset])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst j
      simp only [get_snoc_eq] at hj
      rw [h1,get_snoc_eq,h2,get_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i (Finset.mem_biUnion.mpr ⟨a,List.mem_toFinset.mpr ha,hi⟩))
    · rw [get_snoc_ne _ _ _ hjl] at hj
      have hgen {α : Type} (R : List α) (s d : α) (k : ℕ) (hk : k ≠ R.length) :
          (R ++ [s]).getD k d = R.getD k d := by
        by_cases hkr : k < R.length
        · exact List.getD_append _ _ _ _ hkr
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
      rw [hgen _ _ _ _ (by omega),hgen _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputs n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputs],by simp,?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j,hjn⟩ = y ⟨j,hjn⟩ := hj _ (by simp [inputs,hjn])
    simp [hjn,hx]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

lemma essential_support_full (C : Circuit)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x i (!x i))) ≠ C.eval (List.ofFn x)) :
    (supps C.gates (inputs n)).getD C.output ∅ = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  obtain ⟨x,hx⟩ := hdep i
  apply hx
  have hag := (agree_values (Function.update x i (!x i)) x C.gates _ _ _
    (agree_inputs _ _)).2.2 C.output (by
      intro k hk
      have hki : k ≠ i := fun e => hi (e ▸ hk)
      simp [Function.update_of_ne hki])
  exact hag

lemma essential_tight_output (hn : 2 ≤ n) (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hlen : C.gates.length + 1 = n)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x i (!x i))) ≠ C.eval (List.ofFn x)) :
    ∃ pre g a b, C.gates = pre ++ [g] ∧ C.output = n + pre.length ∧
      g.inputs = [a,b] ∧ a ≠ b ∧
      Disjoint ((supps pre (inputs n)).getD a ∅) ((supps pre (inputs n)).getD b ∅) ∧
      (supps pre (inputs n)).getD a ∅ ∪ (supps pre (inputs n)).getD b ∅ = Finset.univ :=
  tight_output hn C.gates C.output hg hlen (essential_support_full C hdep)

end PEqualNP.Outside.Grok1692OverlapSupport

open PEqualNP.Outside.Grok1692OverlapSupport

/-- Strict shared-support budget and the tight all-essential final-gate partition.
This is a structural auxiliary result, not the official64-gate lower bound. -/
theorem PEqualNP.Outside.Grok1692OverlapSupport :
  ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (let L : List (Finset (Fin n)) := gs.foldl
      (fun L g => L ++ [g.inputs.toFinset.biUnion (fun j => L.getD j ∅)])
      (List.ofFn (fun i : Fin n => {i}))
     ∀ a b : ℕ, a ≠ b →
      (∃ p : Fin n, p ∈ L.getD a ∅ ∧ p ∈ L.getD b ∅) →
      (L.getD a ∅ ∪ L.getD b ∅).card ≤ gs.length + 1) ∧
    (∀ out : ℕ, 2 ≤ n → gs.length + 1 = n →
      (∀ i : Fin n, ∃ x : Fin n → Bool,
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,out⟩
          (List.ofFn (Function.update x i (!x i))) ≠
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,out⟩ (List.ofFn x)) →
      ∃ pre g a b, gs = pre ++ [g] ∧ out = n + pre.length ∧
        g.inputs = [a,b] ∧ a ≠ b ∧
        (let L : List (Finset (Fin n)) := pre.foldl
          (fun L g => L ++ [g.inputs.toFinset.biUnion (fun j => L.getD j ∅)])
          (List.ofFn (fun i : Fin n => {i}))
         Disjoint (L.getD a ∅) (L.getD b ∅) ∧
           L.getD a ∅ ∪ L.getD b ∅ = Finset.univ)) := by
  intro n gs hg
  constructor
  · exact overlap_bound n gs hg
  · intro out hn hlen hdep
    exact essential_tight_output hn ⟨gs,out⟩ hg hlen hdep
