import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.Grok1692FirstMixedGate

lemma local_gate (g : Gate) (u v z : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2)
    (hprior : ∀ w ∈ g.inputs, z w = true → u w = true ∨ v w = true)
    (hz : g.op.eval (g.inputs.map z) = true)
    (hu : g.op.eval (g.inputs.map u) = false)
    (hv : g.op.eval (g.inputs.map v) = false) :
    g.op = GateOp.and ∧ ∃ a b, g.inputs = [a,b] ∧
      ((u a = true ∧ v a = false ∧ u b = false ∧ v b = true) ∨
       (v a = true ∧ u a = false ∧ v b = false ∧ u b = true)) := by
  rcases hop with ha | ho
  · refine ⟨ha, ?_⟩
    cases he : g.inputs with
    | nil => simp [he, ha, GateOp.eval] at hu
    | cons a rest =>
      cases hr : rest with
      | nil =>
        have hp := hprior a (by simp [he, hr])
        simp [he, hr, ha, GateOp.eval] at hz hu hv
        rcases hp hz with hp | hp <;> simp_all
      | cons b tail =>
        have ht : tail = [] := by
          have hl := hlen
          simp only [he, hr, List.length_cons] at hl
          exact List.eq_nil_of_length_eq_zero (by omega)
        have hab : g.inputs = [a,b] := by simp [he, hr, ht]
        refine ⟨a,b,by simp [ht],?_⟩
        have hpa := hprior a (by simp [hab])
        have hpb := hprior b (by simp [hab])
        simp only [he, hr, ht, ha, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true] at hz hu hv
        have hz' : z a = true ∧ z b = true := by simpa only [Bool.and_eq_true] using hz
        have hza := hz'.1
        have hzb := hz'.2
        have hca := hpa hza
        have hcb := hpb hzb
        cases hua : u a <;> cases hva : v a <;> cases hub : u b <;> cases hvb : v b <;>
          simp_all
  · have hp : ∃ w ∈ g.inputs, z w = true := by
      simpa [ho, GateOp.eval, List.any_map] using hz
    obtain ⟨w, hw, hwz⟩ := hp
    rcases hprior w hw hwz with hwu | hwv
    · have ht : g.op.eval (g.inputs.map u) = true := by
        simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨u w, ⟨w,hw,rfl⟩,hwu⟩
      rw [hu] at ht
      contradiction
    · have ht : g.op.eval (g.inputs.map v) = true := by
        simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨v w, ⟨w,hw,rfl⟩,hwv⟩
      rw [hv] at ht
      contradiction


def gateValue (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => x.getD w false)
def step (x : List Bool) (g : Gate) : List Bool := x ++ [gateValue g x]
def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x
def Covered (x y z : List Bool) : Prop :=
  ∀ i, z.getD i false = true → x.getD i false = true ∨ y.getD i false = true

def Cross (g : Gate) (x y : List Bool) : Prop :=
  g.op = GateOp.and ∧ ∃ a b, g.inputs = [a,b] ∧
    ((x.getD a false = true ∧ y.getD a false = false ∧ x.getD b false = false ∧ y.getD b false = true) ∨
     (y.getD a false = true ∧ x.getD a false = false ∧ y.getD b false = false ∧ x.getD b false = true))

lemma covered_append (x y z : List Bool) (hx : x.length = z.length) (hy : y.length = z.length)
    (hc : Covered x y z) (ex ey ez : Bool) (he : ez = true → ex = true ∨ ey = true) :
    Covered (x ++ [ex]) (y ++ [ey]) (z ++ [ez]) := by
  intro i hi
  by_cases hlt : i < z.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact hc i hi
  · by_cases heq : i = z.length
    · subst i
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self, List.getD_cons_zero] at hi
      have hnew := he hi
      rcases hnew with hnew | hnew
      · left
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simpa [hx] using hnew
      · right
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simpa [hy] using hnew
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction

lemma first_mixed (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ x y z : List Bool, x.length = z.length → y.length = z.length → Covered x y z →
    (∃ i, (run gs z).getD i false = true ∧ (run gs x).getD i false = false ∧
      (run gs y).getD i false = false) →
    ∃ pre g post, gs = pre ++ g :: post ∧ Covered (run pre x) (run pre y) (run pre z) ∧
      gateValue g (run pre z) = true ∧ gateValue g (run pre x) = false ∧
      gateValue g (run pre y) = false ∧ Cross g (run pre x) (run pre y) := by
  induction gs with
  | nil =>
    intro x y z _ _ hc hbad
    obtain ⟨i, hi, hix, hiy⟩ := hbad
    rcases hc i hi with hh | hh <;> simp_all [run]
  | cons g gs ih =>
    intro x y z hx hy hc hbad
    by_cases hm : gateValue g z = true ∧ gateValue g x = false ∧ gateValue g y = false
    · refine ⟨[],g,gs,by simp,hc,hm.1,hm.2.1,hm.2.2,?_⟩
      exact local_gate g (fun i => x.getD i false) (fun i => y.getD i false)
        (fun i => z.getD i false) (hg g (by simp)).1 (hg g (by simp)).2
        (fun w _ hw => hc w hw) hm.1 hm.2.1 hm.2.2
    · have he : gateValue g z = true → gateValue g x = true ∨ gateValue g y = true := by
        cases hz : gateValue g z <;> cases hxx : gateValue g x <;> cases hyy : gateValue g y <;> simp_all
      have hcov := covered_append x y z hx hy hc _ _ _ he
      obtain ⟨pre,k,post,hgs,hpre,hkz,hkx,hky,hcross⟩ := ih
        (fun k hk => hg k (List.mem_cons_of_mem g hk)) (step x g) (step y g) (step z g)
        (by simp [step,hx]) (by simp [step,hy]) hcov (by simpa only [run, List.foldl_cons] using hbad)
      refine ⟨g :: pre,k,post,?_,?_,?_,?_,?_,?_⟩
      · simp [hgs]
      · simpa only [run,List.foldl_cons] using hpre
      · simpa only [run,List.foldl_cons] using hkz
      · simpa only [run,List.foldl_cons] using hkx
      · simpa only [run,List.foldl_cons] using hky
      · simpa only [run,List.foldl_cons] using hcross

end PEqualNP.Outside.Grok1692FirstMixedGate

open PEqualNP.Outside.Grok1692FirstMixedGate

theorem PEqualNP.Outside.Grok1692FirstMixedGate :
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y z : List Bool, x.length = z.length → y.length = z.length →
    (∀ i, z.getD i false = true → x.getD i false = true ∨ y.getD i false = true) →
    C.eval z = true → C.eval x = false → C.eval y = false →
    ∃ pre g post, C.gates = pre ++ g :: post ∧
      (∀ i, ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires z).getD i false = true →
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires x).getD i false = true ∨
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires y).getD i false = true) ∧
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ a b, g.inputs = [a,b] ∧
      (((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires z).getD a false = true ∧
       ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires z).getD b false = true) ∧
      ((((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires x).getD a false = true ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires y).getD a false = false ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires x).getD b false = false ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires y).getD b false = true) ∨
       (((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires y).getD a false = true ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires x).getD a false = false ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires y).getD b false = false ∧
        ((PEqualNP.CircuitLowerBounds.Circuit.mk pre 0).wires x).getD b false = true)) := by
  intro C hg x y z hx hy hc hz hxx hyy
  have hbad : ∃ i, (run C.gates z).getD i false = true ∧
      (run C.gates x).getD i false = false ∧ (run C.gates y).getD i false = false :=
    ⟨C.output,hz,hxx,hyy⟩
  obtain ⟨pre,g,post,hgs,hcov,hgz,hgx,hgy,hop,a,b,hab,hpattern⟩ :=
    first_mixed C.gates hg x y z hx hy hc hbad
  refine ⟨pre,g,post,hgs,hcov,hop,a,b,hab,?_,hpattern⟩
  change (run pre z).getD a false = true ∧ (run pre z).getD b false = true
  simpa [gateValue,hop,hab,GateOp.eval] using hgz
