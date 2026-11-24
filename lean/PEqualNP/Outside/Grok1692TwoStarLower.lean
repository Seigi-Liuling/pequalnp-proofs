import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.Grok1692OverlapSupport
open Finset PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.Grok1692TwoStarLower

def edge (u v : Fin 9) : Prop :=
  (u = 0 ∧ v ∈ ({2,3,4,5} : Finset (Fin 9))) ∨
  (v = 0 ∧ u ∈ ({2,3,4,5} : Finset (Fin 9))) ∨
  (u = 1 ∧ v ∈ ({2,6,7,8} : Finset (Fin 9))) ∨
  (v = 1 ∧ u ∈ ({2,6,7,8} : Finset (Fin 9)))
instance (u v : Fin 9) : Decidable (edge u v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
lemma no_loop : ∀ u : Fin 9, ¬edge u u := by decide
lemma min_degree : ∀ u : Fin 9, ∃ v : Fin 9, edge u v := by decide
lemma edge_symm : ∀ u v, edge u v → edge v u := by
  intro u v
  simp only [edge]
  tauto
lemma partitions (A : Finset (Fin 9)) (hA : A.Nonempty) (hB : Aᶜ.Nonempty) :
  (∃ u ∈ A, ∃ v ∉ A, edge u v) ∧
  ((∀ u v, edge u v → (u ∈ A ↔ v ∉ A)) → ∃ u ∈ A, ∃ v ∉ A, ¬edge u v) := by
  constructor
  · by_contra hn
    have hs : ∀ u v, edge u v → (u ∈ A ↔ v ∈ A) := by
      intro u v he
      constructor
      · intro hu
        by_contra hv
        exact hn ⟨u,hu,v,hv,he⟩
      · intro hv
        by_contra hu
        exact hn ⟨v,hv,u,hu,edge_symm u v he⟩
    have h02 := hs 0 2 (by decide)
    have h12 := hs 1 2 (by decide)
    have h03 := hs 0 3 (by decide)
    have h04 := hs 0 4 (by decide)
    have h05 := hs 0 5 (by decide)
    have h16 := hs 1 6 (by decide)
    have h17 := hs 1 7 (by decide)
    have h18 := hs 1 8 (by decide)
    have hall : ∀ u : Fin 9, u ∈ A ↔ (0 : Fin 9) ∈ A := by
      intro u
      fin_cases u
      · exact Iff.rfl
      · exact h12.trans h02.symm
      · exact h02.symm
      · exact h03.symm
      · exact h04.symm
      · exact h05.symm
      · exact h16.symm.trans (h12.trans h02.symm)
      · exact h17.symm.trans (h12.trans h02.symm)
      · exact h18.symm.trans (h12.trans h02.symm)
    obtain ⟨a,ha⟩ := hA
    obtain ⟨b,hb⟩ := hB
    have hb' : b ∉ A := by simpa using hb
    exact hb' ((hall b).mpr ((hall a).mp ha))
  · intro hc
    have h02 := hc 0 2 (by decide)
    have h12 := hc 1 2 (by decide)
    have h16 := hc 1 6 (by decide)
    have h06 : (0 : Fin 9) ∈ A ↔ (6 : Fin 9) ∉ A := h02.trans (h12.symm.trans h16)
    by_cases h0 : (0 : Fin 9) ∈ A
    · exact ⟨0,h0,6,h06.mp h0,by decide⟩
    · have h6 : (6 : Fin 9) ∈ A := by
        by_contra hh
        exact h0 (h06.mpr hh)
      exact ⟨6,h6,0,h0,by decide⟩

lemma mask_left (A : Finset (Fin 9)) (u v : Fin 9) :
    ({u,v} : Finset (Fin 9)) ∩ A =
      (if u ∈ A then {u} else ∅) ∪ (if v ∈ A then {v} else ∅) := by
  ext k
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_union,Finset.notMem_empty,hu,hv,ite_true,ite_false] <;> aesop
lemma mask_right (A : Finset (Fin 9)) (u v : Fin 9) :
    ({u,v} : Finset (Fin 9)) \ A =
      (if u ∈ A then ∅ else {u}) ∪ (if v ∈ A then ∅ else {v}) := by
  ext k
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_union,Finset.notMem_empty,hu,hv,ite_true,ite_false] <;> aesop

lemma mask_left_single (A : Finset (Fin 9)) (u : Fin 9) :
    ({u} : Finset (Fin 9)) ∩ A = if u ∈ A then {u} else ∅ := by
  simpa using mask_left A u u
lemma mask_right_single (A : Finset (Fin 9)) (u : Fin 9) :
    ({u} : Finset (Fin 9)) \ A = if u ∈ A then ∅ else {u} := by
  simpa using mask_right A u u

lemma no_disjoint_root (A : Finset (Fin 9)) (hA : A.Nonempty) (hB : Aᶜ.Nonempty)
    (f g : Finset (Fin 9) → Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hzero : op.eval [f ∅,g ∅] = false)
    (hpairs : ∀ u v : Fin 9,
      op.eval [f ({u,v} ∩ A),g ({u,v} \ A)] = decide (edge u v)) : False := by
  obtain ⟨hcros,hnotbic⟩ := partitions A hA hB
  rcases hop with hop | hop
  · subst op
    have hf0 : f ∅ = false := by
      cases he0 : f ∅ with
      | false => rfl
      | true =>
        obtain ⟨u,hu⟩ := hA
        obtain ⟨v,he⟩ := min_degree u
        have hsing := hpairs v v
        have hpair := hpairs u v
        by_cases hv : v ∈ A <;>
          simp [mask_left,mask_right,mask_left_single,mask_right_single,hu,hv,GateOp.eval,he0,no_loop,he] at hzero hsing hpair
        all_goals simp_all
    have hg0 : g ∅ = false := by
      cases he0 : g ∅ with
      | false => rfl
      | true =>
        obtain ⟨u,hu⟩ := hB
        have hu : u ∉ A := by simpa using hu
        obtain ⟨v,he⟩ := min_degree u
        have hsing := hpairs v v
        have hpair := hpairs u v
        by_cases hv : v ∈ A <;>
          simp [mask_left,mask_right,mask_left_single,mask_right_single,hu,hv,GateOp.eval,he0,hf0,no_loop,he] at hsing hpair
        all_goals simp_all
    have hcut : ∀ u v, edge u v → (u ∈ A ↔ v ∉ A) := by
      intro u v he
      have hh := hpairs u v
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
        simp_all [mask_left,mask_right,mask_left_single,mask_right_single,GateOp.eval]
    have hft (u : Fin 9) (hu : u ∈ A) : f {u} = true := by
      obtain ⟨v,he⟩ := min_degree u
      have hv : v ∉ A := (hcut u v he).mp hu
      have hh := hpairs u v
      have hboth : f {u} = true ∧ g {v} = true := by
        simpa [mask_left,mask_right,hu,hv,GateOp.eval,he] using hh
      exact hboth.1
    have hgt (u : Fin 9) (hu : u ∉ A) : g {u} = true := by
      obtain ⟨v,he⟩ := min_degree u
      have hv : v ∈ A := by
        by_contra hn
        exact hu ((hcut u v he).mpr hn)
      have hh := hpairs u v
      have hboth : f {v} = true ∧ g {u} = true := by
        simpa [mask_left,mask_right,hu,hv,GateOp.eval,he] using hh
      exact hboth.2
    obtain ⟨u,hu,v,hv,he⟩ := hnotbic hcut
    have hh := hpairs u v
    simp [mask_left,mask_right,mask_left_single,mask_right_single,hu,hv,GateOp.eval,he,hft u hu,hgt v hv] at hh
  · subst op
    obtain ⟨u,hu,v,hv,he⟩ := hcros
    have hi := hpairs u u
    have hj := hpairs v v
    have hij := hpairs u v
    simp [mask_left,mask_right,mask_left_single,mask_right_single,hu,hv,GateOp.eval,no_loop,he] at hi hj hij
    simp_all



def bits (T : Finset (Fin 9)) : Fin 9 → Bool := fun i => decide (i ∈ T)
def val (C : Circuit) (T : Finset (Fin 9)) : Bool := C.eval (List.ofFn (bits T))

lemma lower (C : Circuit)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : val C ∅ = false)
    (hpairs : ∀ u v : Fin 9, val C {u,v} = decide (edge u v)) : 9 ≤ C.gates.length := by
  have hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hdep : ∀ i : Fin 9, ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn (Function.update x i (!x i))) ≠ C.eval (List.ofFn x) := by
    intro i
    obtain ⟨v,he⟩ := min_degree i
    have hne : i ≠ v := by
      intro hh
      subst v
      exact no_loop i he
    let x : Fin 9 → Bool := fun k => decide (k = v)
    have hupdate : Function.update x i (!x i) = bits {i,v} := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [x,bits,hne]
      · simp [Function.update_of_ne hk,x,bits,hk]
    have hsingle : x = bits {v,v} := by funext k; simp [x,bits]
    refine ⟨x,?_⟩
    have ht : C.eval (List.ofFn (Function.update x i (!x i))) = true := by
      rw [hupdate]
      simpa [val,he] using hpairs i v
    have hf : C.eval (List.ofFn x) = false := by
      rw [hsingle]
      simpa [val,no_loop] using hpairs v v
    rw [ht,hf]
    decide
  have hfull := PEqualNP.Outside.Grok1692OverlapSupport.essential_support_full C hdep
  have hc := (PEqualNP.Outside.Grok1692OverlapSupport.run_bounds C.gates hfanin 0 (PEqualNP.Outside.Grok1692OverlapSupport.inputs 9) PEqualNP.Outside.Grok1692OverlapSupport.count_inputs PEqualNP.Outside.Grok1692OverlapSupport.strict_inputs).1 {C.output}
  simp only [zero_add,PEqualNP.Outside.Grok1692OverlapSupport.joint,Finset.singleton_biUnion,Finset.card_singleton] at hc
  rw [hfull,Finset.card_univ,Fintype.card_fin] at hc
  by_contra hn
  have hlen : C.gates.length + 1 = 9 := by omega
  obtain ⟨pre,g,a,b,hgs,hout,hab,hne,hdis,hcover⟩ :=
    PEqualNP.Outside.Grok1692OverlapSupport.essential_tight_output (by decide) C hfanin hlen hdep
  let A := (PEqualNP.Outside.Grok1692OverlapSupport.supps pre (PEqualNP.Outside.Grok1692OverlapSupport.inputs 9)).getD a ∅
  let B := (PEqualNP.Outside.Grok1692OverlapSupport.supps pre (PEqualNP.Outside.Grok1692OverlapSupport.inputs 9)).getD b ∅
  change Disjoint A B at hdis
  change A ∪ B = Finset.univ at hcover
  have hpre : ∀ k ∈ pre, k.inputs.length ≤ 2 := by
    intro k hk
    apply hfanin k
    rw [hgs]
    simp [hk]
  have hprelen : pre.length = 7 := by rw [hgs] at hlen; simp at hlen; omega
  have hsmall (w : ℕ) : ((PEqualNP.Outside.Grok1692OverlapSupport.supps pre (PEqualNP.Outside.Grok1692OverlapSupport.inputs 9)).getD w ∅).card ≤ 8 := by
    have hh := (PEqualNP.Outside.Grok1692OverlapSupport.run_bounds pre hpre 0 (PEqualNP.Outside.Grok1692OverlapSupport.inputs 9) PEqualNP.Outside.Grok1692OverlapSupport.count_inputs PEqualNP.Outside.Grok1692OverlapSupport.strict_inputs).1 {w}
    simpa [PEqualNP.Outside.Grok1692OverlapSupport.joint,hprelen] using hh
  have hA : A.Nonempty := by
    by_contra ha
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hh := hsmall b
    have hb : B = Finset.univ := by simpa [he] using hcover
    change B.card ≤ 8 at hh
    rw [hb,Finset.card_univ,Fintype.card_fin] at hh
    omega
  have hB : Aᶜ.Nonempty := by
    by_contra hb
    have he : A = Finset.univ := by
      have hc : Aᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      exact (Finset.compl_eq_empty_iff A).mp hc
    have hh := hsmall a
    change A.card ≤ 8 at hh
    rw [he,Finset.card_univ,Fintype.card_fin] at hh
    omega
  let fa : Finset (Fin 9) → Bool := fun T =>
    (PEqualNP.Outside.Grok1692OverlapSupport.values pre (List.ofFn (bits T))).getD a false
  let fb : Finset (Fin 9) → Bool := fun T =>
    (PEqualNP.Outside.Grok1692OverlapSupport.values pre (List.ofFn (bits T))).getD b false
  have hfa (T : Finset (Fin 9)) : fa T = fa (T ∩ A) := by
    apply (PEqualNP.Outside.Grok1692OverlapSupport.agree_values (bits T) (bits (T ∩ A)) pre _ _ _ (PEqualNP.Outside.Grok1692OverlapSupport.agree_inputs _ _)).2.2 a
    intro i hi
    change i ∈ A at hi
    simp [bits,hi]
  have hfb (T : Finset (Fin 9)) : fb T = fb (T \ A) := by
    apply (PEqualNP.Outside.Grok1692OverlapSupport.agree_values (bits T) (bits (T \ A)) pre _ _ _ (PEqualNP.Outside.Grok1692OverlapSupport.agree_inputs _ _)).2.2 b
    intro i hi
    have hnA : i ∉ A := by
      intro hiA
      exact Finset.disjoint_left.mp hdis hiA hi
    simp [bits,hnA]
  have hroot (T : Finset (Fin 9)) : g.op.eval [fa (T ∩ A),fb (T \ A)] = val C T := by
    rw [←hfa T,←hfb T]
    symm
    change (PEqualNP.Outside.Grok1692OverlapSupport.values C.gates (List.ofFn (bits T))).getD C.output false = _
    rw [hgs,hout]
    have hwlen : (PEqualNP.Outside.Grok1692OverlapSupport.values pre (List.ofFn (bits T))).length = 9 + pre.length := by
      have hh := (PEqualNP.Outside.Grok1692OverlapSupport.agree_values (bits T) (bits T) pre _ _ _ (PEqualNP.Outside.Grok1692OverlapSupport.agree_inputs _ _)).1
      simpa [PEqualNP.Outside.Grok1692OverlapSupport.supps_length,PEqualNP.Outside.Grok1692OverlapSupport.inputs] using hh.symm
    have hrun : PEqualNP.Outside.Grok1692OverlapSupport.values (pre ++ [g]) (List.ofFn (bits T)) =
        PEqualNP.Outside.Grok1692OverlapSupport.values pre (List.ofFn (bits T)) ++
          [g.op.eval (g.inputs.map fun w => (PEqualNP.Outside.Grok1692OverlapSupport.values pre (List.ofFn (bits T))).getD w false)] := by
      simp [PEqualNP.Outside.Grok1692OverlapSupport.values,List.foldl_append]
    rw [hrun,←hwlen,PEqualNP.Outside.Grok1692OverlapSupport.get_snoc_eq]
    simp [hab,fa,fb]
  have hopg : g.op = GateOp.and ∨ g.op = GateOp.or := (hops g (by rw [hgs]; simp)).1
  apply no_disjoint_root A hA hB fa fb g.op hopg
  · simpa using (hroot ∅).trans hzero
  · intro u v
    exact (hroot {u,v}).trans (hpairs u v)

end PEqualNP.Outside.Grok1692TwoStarLower

/-- Exact local lower bound for two four-edge stars sharing one leaf.
Inputs0,1 are centers;2 is their common leaf;3,4,5 and6,7,8 are private leaves.
This is a local nine-input result, NOT the official64-gate conclusion. -/
theorem PEqualNP.Outside.Grok1692TwoStarLower :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    (∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    C.eval (List.ofFn (fun _ : Fin 9 => false)) = false →
    (∀ u v : Fin 9,
      C.eval (List.ofFn (fun k : Fin 9 => decide (k ∈ ({u,v} : Finset (Fin 9))))) =
      decide ((u = 0 ∧ v ∈ ({2,3,4,5} : Finset (Fin 9))) ∨
        (v = 0 ∧ u ∈ ({2,3,4,5} : Finset (Fin 9))) ∨
        (u = 1 ∧ v ∈ ({2,6,7,8} : Finset (Fin 9))) ∨
        (v = 1 ∧ u ∈ ({2,6,7,8} : Finset (Fin 9))))) →
    9 ≤ C.gates.length := by
  intro C hops hzero hpairs
  exact PEqualNP.Outside.Grok1692TwoStarLower.lower C hops (by simpa [PEqualNP.Outside.Grok1692TwoStarLower.val,PEqualNP.Outside.Grok1692TwoStarLower.bits] using hzero) hpairs
