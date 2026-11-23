import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Grok086SquareZeroObstruction_aux

def ii : GaussianInt := ⟨0, 1⟩
def u : Fin 6 → GaussianInt := ![1, -1, ii, -ii, 0, 0]
def v : Fin 6 → GaussianInt := ![1, 1, ii, ii, -2 * ii, -2]
def gT (i j : Fin 6) : GaussianInt := u i * v j - v i * u j

theorem rows : ∀ i : Fin 6, ∑ j, gT i j = 0 := by decide
theorem cols : ∀ j : Fin 6, ∑ i, gT i j = 0 := by decide
theorem skew : ∀ i j : Fin 6, gT i j = -gT j i := by decide
theorem square : ∀ i j : Fin 6, ∑ k, gT i k * gT k j = 0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem perm_value : Matrix.permanent (fun i j : Fin 6 => 1 + gT i j) = (4944 : GaussianInt) := by
  decide +kernel

def t (p : Fin 6 × Fin 6) : ℂ := GaussianInt.toComplex (gT p.1 p.2)

theorem eval_value :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 6) = 4944 := by
  calc
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 6) =
        Matrix.permanent (fun i j : Fin 6 => 1 + GaussianInt.toComplex (gT i j)) := by
      simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, t]
    _ = GaussianInt.toComplex (Matrix.permanent (fun i j : Fin 6 => 1 + gT i j)) := by
      simp [Matrix.permanent]
    _ = 4944 := by
      rw [perm_value]
      change ((4944 : GaussianInt) : ℂ) = 4944
      norm_num [GaussianInt.toComplex_def]

end PEqualNP.Outside.Grok086SquareZeroObstruction_aux

theorem PEqualNP.Outside.Grok086SquareZeroObstruction :
    ∃ t : Fin 6 × Fin 6 → ℂ,
    (∀ i : Fin 6, ∑ j, t (i, j) = 0) ∧
    (∀ j : Fin 6, ∑ i, t (i, j) = 0) ∧
    (∀ i j : Fin 6, t (i, j) = -t (j, i)) ∧
    (∀ i j : Fin 6, ∑ k, t (i, k) * t (k, j) = 0) ∧
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 6) = 4944 ∧
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 6) ≠ (Nat.factorial 6 : ℂ) := by
  refine ⟨PEqualNP.Outside.Grok086SquareZeroObstruction_aux.t, ?_, ?_, ?_, ?_,
    PEqualNP.Outside.Grok086SquareZeroObstruction_aux.eval_value, ?_⟩
  · intro i
    simpa only [PEqualNP.Outside.Grok086SquareZeroObstruction_aux.t, map_sum, map_zero] using
      congrArg GaussianInt.toComplex (PEqualNP.Outside.Grok086SquareZeroObstruction_aux.rows i)
  · intro j
    simpa only [PEqualNP.Outside.Grok086SquareZeroObstruction_aux.t, map_sum, map_zero] using
      congrArg GaussianInt.toComplex (PEqualNP.Outside.Grok086SquareZeroObstruction_aux.cols j)
  · intro i j
    simpa only [PEqualNP.Outside.Grok086SquareZeroObstruction_aux.t, map_neg] using
      congrArg GaussianInt.toComplex (PEqualNP.Outside.Grok086SquareZeroObstruction_aux.skew i j)
  · intro i j
    simpa only [PEqualNP.Outside.Grok086SquareZeroObstruction_aux.t, map_sum, map_mul, map_zero] using
      congrArg GaussianInt.toComplex (PEqualNP.Outside.Grok086SquareZeroObstruction_aux.square i j)
  · rw [PEqualNP.Outside.Grok086SquareZeroObstruction_aux.eval_value]
    norm_num [Nat.factorial]
