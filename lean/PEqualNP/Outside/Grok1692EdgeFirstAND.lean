import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.Grok1692EdgeFirstAND.Bridge

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi


def diff : Finset (Fin 13) := {0,1,3,9}
abbrev IsQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ diff)).card ≤ 2
def negative (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p : Fin 13 => decide (p ∈ Q))
    (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ diff))
abbrev Incident (a b : Fin 26) : Prop :=
  (a.val < 13 ∧ 13 ≤ b.val ∧ ((Fin.ofNat 13 a.val) - (Fin.ofNat 13 (b.val-13))) ∈ diff) ∨
  (b.val < 13 ∧ 13 ≤ a.val ∧ ((Fin.ofNat 13 b.val) - (Fin.ofNat 13 (a.val-13))) ∈ diff)
def quadMasks : List ℕ := [29,39,58,71,77,78,83,85,101,105,116,135,141,142,154,156,166,170,195,201,202,210,232,270,275,281,284,297,308,329,332,337,340,387,402,404,420,449,464,533,540,549,550,562,568,593,609,664,674,680,774,801,840,897,1037,1049,1059,1066,1098,1124,1136,1155,1157,1283,1328,1348,1541,1548,1553,1602,2055,2067,2069,2073,2074,2083,2118,2132,2181,2185,2196,2272,2307,2314,2565,3082,4110,4115,4131,4137,4148,4163,4233,4362,4625,5123,6153]
def quadAt (i : Fin 97) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => (quadMasks.getD i.val 0).testBit p.val = true)
def indices : List (List (Fin 97)) := [[1,1,1,0,6,1,3,11,24,39,56,70,87,0,9,6,1,0,0,24,1,1,3,0,0,0],[1,1,1,5,6,1,3,11,24,42,56,70,87,0,0,6,1,5,0,24,1,1,3,13,0,2],[1,1,1,0,0,1,3,11,23,39,54,70,86,10,0,0,1,5,0,0,1,1,3,13,0,0],[0,5,0,0,0,9,4,12,25,40,54,73,89,0,9,0,0,5,0,25,0,4,0,13,0,2],[6,6,0,0,6,2,6,14,24,39,55,71,87,10,0,6,0,0,0,24,6,0,6,2,0,2],[1,1,1,9,2,1,8,16,27,41,56,75,88,10,9,0,1,0,0,56,1,1,0,16,8,2],[3,3,3,4,6,8,3,18,29,45,58,76,91,10,9,6,0,5,0,0,3,3,3,0,4,20],[11,11,11,12,14,16,18,11,33,53,61,78,92,35,19,18,11,0,12,0,0,11,11,13,0,14],[24,24,23,25,24,27,29,33,24,51,63,82,93,28,27,24,33,23,0,24,0,0,24,23,25,0],[39,42,39,40,39,41,45,53,51,39,66,84,94,0,46,45,41,50,39,0,39,0,0,42,39,43],[56,56,54,54,55,56,58,61,63,66,56,85,95,59,0,61,56,58,54,56,0,56,0,0,54,57],[70,70,70,73,71,75,76,78,82,84,85,70,96,77,79,0,70,76,72,71,70,0,70,0,0,74],[87,87,86,89,87,88,91,92,93,94,95,96,87,90,89,87,0,86,92,87,87,88,0,86,0,0],[0,0,10,0,10,10,10,35,28,0,59,77,90,10,81,38,36,65,80,64,10,59,32,28,10,60],[9,0,0,9,0,9,9,19,27,46,0,79,89,81,9,37,51,52,79,27,46,9,19,49,9,22],[6,6,0,0,6,0,6,18,24,45,61,0,87,38,37,6,33,69,68,24,6,18,6,34,31,21],[1,1,1,0,0,1,0,11,33,41,56,70,0,36,51,33,1,50,62,56,1,1,11,16,41,48],[0,5,5,5,0,0,5,0,23,50,58,76,86,65,52,69,50,5,67,83,76,5,5,23,30,58],[0,0,0,0,0,0,0,12,0,39,54,72,92,80,79,68,62,67,0,55,39,12,0,15,0,47],[24,24,0,25,24,56,0,0,24,0,56,71,87,64,27,24,56,83,55,24,71,56,24,2,25,2],[1,1,1,0,6,1,3,0,0,39,0,70,87,10,46,6,1,76,39,71,1,1,3,42,7,43],[1,1,1,4,0,1,3,11,0,0,56,0,88,59,9,18,1,5,12,56,1,1,3,13,4,17],[3,3,3,0,6,0,3,11,24,0,0,70,0,32,19,6,11,5,0,24,3,3,3,13,0,14],[0,13,13,13,2,16,0,13,23,42,0,0,86,28,49,34,16,23,15,2,42,13,13,13,26,2],[0,0,0,0,0,8,4,0,25,39,54,0,0,10,9,31,41,30,0,25,7,4,0,26,0,44],[0,2,0,2,2,2,20,14,0,43,57,74,0,60,22,21,48,58,47,2,43,17,14,2,44,2]]
def witness (a b : Fin 26) : Finset (Fin 13) :=
  quadAt ((indices.getD a.val []).getD b.val 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
lemma valid_quads : ∀ i : Fin 97, IsQuad (quadAt i) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
lemma coverage : ∀ a b : Fin 26, ¬ Incident a b →
    negative (witness a b) a = true ∧ negative (witness a b) b = true := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

lemma geometry (a b : Fin 26) (h : ¬ Incident a b) :
    IsQuad (witness a b) ∧ negative (witness a b) a = true ∧ negative (witness a b) b = true := by
  exact ⟨valid_quads _, coverage a b h⟩

lemma vectors_mono (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 26 → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply fold_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output
  intro i hi
  by_cases h : i < 26
  · have hx : i < (List.ofFn x).length := by simpa using h
    have hy : i < (List.ofFn y).length := by simpa using h
    rw [List.getD_eq_getElem _ _ hx] at hi
    rw [List.getD_eq_getElem _ _ hy]
    simpa only [List.getElem_ofFn] using hxy ⟨i,h⟩ (by simpa only [List.getElem_ofFn] using hi)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)] at hi
    contradiction

end PEqualNP.Outside.Grok1692EdgeFirstAND.Bridge

open PEqualNP.Outside.Grok1692EdgeFirstAND.Bridge

namespace PEqualNP.Outside.Grok1692EdgeFirstAND

lemma BridgeResult :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (∀ Q : Finset (Fin 13), (Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13)))).card ≤ 2) → C.eval
      (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
       List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13))))) = false) →
    ∀ a b : Fin 26, ¬ ((a.val < 13 ∧ 13 ≤ b.val ∧ ((Fin.ofNat 13 a.val) - (Fin.ofNat 13 (b.val-13))) ∈ ({0,1,3,9} : Finset (Fin 13))) ∨ (b.val < 13 ∧ 13 ≤ a.val ∧ ((Fin.ofNat 13 b.val) - (Fin.ofNat 13 (a.val-13))) ∈ ({0,1,3,9} : Finset (Fin 13)))) →
      C.eval (List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = b))) = false := by
  intro C hC hnegative a b hab
  obtain ⟨hQ, ha, hb⟩ := geometry a b hab
  have hn := hnegative (witness a b) hQ
  rw [← List.ofFn_fin_append] at hn
  change C.eval (List.ofFn (negative (witness a b))) = false at hn
  cases he : C.eval (List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = b))) with
  | false => rfl
  | true =>
    have ht := vectors_mono C hC (fun i : Fin 26 => decide (i = a ∨ i = b))
      (negative (witness a b)) (by
        intro i hi
        simp only [decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb) he
    rw [hn] at ht
    contradiction
end PEqualNP.Outside.Grok1692EdgeFirstAND


open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.Grok1692EdgeFirstAND.Mixed

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

end PEqualNP.Outside.Grok1692EdgeFirstAND.Mixed

open PEqualNP.Outside.Grok1692EdgeFirstAND.Mixed

namespace PEqualNP.Outside.Grok1692EdgeFirstAND

lemma MixedResult :
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
end PEqualNP.Outside.Grok1692EdgeFirstAND

namespace PEqualNP.Outside.Grok1692EdgeFirstAND

lemma AnyPairResult :
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ Q : Finset (Fin 13), (Q.card = 4 ∧ ∀ l : Fin 13,
      (Q.filter (fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13)))).card ≤ 2) → C.eval
      (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
       List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13))))) = false) →
    ∀ a b : Fin 26,
    let x := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = a))
    let y := List.ofFn (fun i : Fin 26 => decide (i = b ∨ i = b))
    let z := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = b))
    C.eval z = true →
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
  intro C hAO hnegative a b
  dsimp only
  intro hpos
  let x := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = a))
  let y := List.ofFn (fun i : Fin 26 => decide (i = b ∨ i = b))
  let z := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = b))
  have hdiag (v : Fin 26) : ¬ PEqualNP.Outside.Grok1692EdgeFirstAND.Bridge.Incident v v := by
    intro hh
    rcases hh with hh | hh <;> omega
  have hmono (g) (hg : g ∈ C.gates) := (hAO g hg).1
  have hxx := PEqualNP.Outside.Grok1692EdgeFirstAND.BridgeResult C hmono hnegative a a (hdiag a)
  have hyy := PEqualNP.Outside.Grok1692EdgeFirstAND.BridgeResult C hmono hnegative b b (hdiag b)
  have hc : ∀ i, z.getD i false = true → x.getD i false = true ∨ y.getD i false = true := by
    intro i hi
    by_cases h : i < 26
    · have hx : i < x.length := by simpa [x] using h
      have hy : i < y.length := by simpa [y] using h
      have hz : i < z.length := by simpa [z] using h
      rw [List.getD_eq_getElem _ _ hz] at hi
      rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [x,y,z,List.getElem_ofFn,decide_eq_true_eq] at hi ⊢
      aesop
    · rw [List.getD_eq_default _ _ (by simp [z]; omega)] at hi
      contradiction
  exact PEqualNP.Outside.Grok1692EdgeFirstAND.MixedResult C hAO x y z
    (by simp [x,z]) (by simp [y,z]) hc hpos hxx hyy


lemma positive_encoding (p l : Fin 13) :
    List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) =
      List.ofFn (fun u : Fin 13 => decide (u=p)) ++
      List.ofFn (fun v : Fin 13 => decide (v=l)) := by
  rw [List.ofFn_add (n := 13) (m := 13)]
  congr 1
  · congr 1
    funext u
    change decide (Fin.castAdd 13 u = Fin.castAdd 13 p ∨ Fin.castAdd 13 u = Fin.natAdd 13 l) = decide (u=p)
    have hs : (Fin.castAdd 13 u = Fin.castAdd 13 p) ↔ u=p := by
      constructor
      · intro h
        apply Fin.ext
        exact congrArg (fun v : Fin 26 => v.val) h
      · intro h; subst u; rfl
    have hn : Fin.castAdd 13 u ≠ Fin.natAdd 13 l := by
      intro h
      have hv := congrArg Fin.val h
      change u.val = 13+l.val at hv
      have := u.isLt
      omega
    simp only [hs,hn,or_false]
  · congr 1
    funext u
    change decide (Fin.natAdd 13 u = Fin.castAdd 13 p ∨ Fin.natAdd 13 u = Fin.natAdd 13 l) = decide (u=l)
    have hs : (Fin.natAdd 13 u = Fin.natAdd 13 l) ↔ u=l := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        change 13+u.val = 13+l.val at hv
        omega
      · intro h; subst u; rfl
    have hn : Fin.natAdd 13 u ≠ Fin.castAdd 13 p := by
      intro h
      have hv := congrArg Fin.val h
      change 13+u.val = p.val at hv
      have := p.isLt
      omega
    simp only [hs,hn,false_or]

end PEqualNP.Outside.Grok1692EdgeFirstAND

theorem PEqualNP.Outside.Grok1692EdgeFirstAND :
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ Q : Finset (Fin 13), (Q.card = 4 ∧ ∀ l : Fin 13,
      (Q.filter (fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13)))).card ≤ 2) → C.eval
      (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
       List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13))))) = false) →
    (∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) → C.eval
      (List.ofFn (fun u : Fin 13 => decide (u=p)) ++
       List.ofFn (fun v : Fin 13 => decide (v=l))) = true) →
    ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) →
    let a := Fin.castAdd 13 p
    let b := Fin.natAdd 13 l
    let x := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = a))
    let y := List.ofFn (fun i : Fin 26 => decide (i = b ∨ i = b))
    let z := List.ofFn (fun i : Fin 26 => decide (i = a ∨ i = b))
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
  intro C hAO hnegative hpositive p l hinc
  dsimp only
  exact PEqualNP.Outside.Grok1692EdgeFirstAND.AnyPairResult C hAO hnegative
    (Fin.castAdd 13 p) (Fin.natAdd 13 l) (by
      rw [PEqualNP.Outside.Grok1692EdgeFirstAND.positive_encoding]
      exact hpositive p l hinc)
