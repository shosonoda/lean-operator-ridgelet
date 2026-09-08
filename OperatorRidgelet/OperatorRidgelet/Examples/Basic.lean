import OperatorRidgelet.Examples.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Auxiliary lemmas for Section 7 and Appendix E

Elementary facts used by the proofs in `OperatorRidgelet.Paper.Examples`; not imported by
`Challenge`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory LeanRidgelet

/-- `|b|^j e^{-b²/2}` is integrable on `ℝ` for every `j`. -/
theorem integrable_abs_pow_mul_exp_neg_sq_half (j : ℕ) :
    Integrable fun b : ℝ => |b| ^ j * Real.exp (-b ^ 2 / 2) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) (s := (j : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) j])).abs
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [Real.rpow_natCast, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

theorem continuous_relu : Continuous relu := by
  unfold relu
  fun_prop

theorem continuous_gaussianActDeriv2 : Continuous gaussianActDeriv2 := by
  unfold gaussianActDeriv2
  fun_prop

/-- `|φ''(b)| ≤ (b² + 1) e^{-b²/2}`. -/
theorem abs_gaussianActDeriv2_le (b : ℝ) :
    |gaussianActDeriv2 b| ≤ (b ^ 2 + 1) * Real.exp (-b ^ 2 / 2) := by
  unfold gaussianActDeriv2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg b]

end OperatorRidgelet
