import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Integrals of products of hyperbolic and trigonometric sines -/

namespace Real

/-- A primitive for the product of a hyperbolic sine and a sine. -/
theorem hasDerivAt_sinh_sin_primitive (k t : ℝ) :
    HasDerivAt (fun t : ℝ => (cosh t * sin (k * t) - k * sinh t * cos (k * t)) / (1 + k ^ 2))
      (sinh t * sin (k * t)) t := by
  have hs := ((hasDerivAt_id t).const_mul k).sin
  have hc := ((hasDerivAt_id t).const_mul k).cos
  convert! (((hasDerivAt_cosh t).mul hs).sub
    (((hasDerivAt_sinh t).const_mul k).mul hc)).div_const (1 + k ^ 2) using 1
  all_goals first | rfl | (simp only [id_eq, Pi.sub_apply, Pi.neg_apply]; field_simp; ring)

/-- A primitive for `sinh(c-t) sin(kt)`. -/
theorem hasDerivAt_sinh_sub_sin_primitive (c k t : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (-cosh (c - t) * sin (k * t) - k * sinh (c - t) * cos (k * t)) / (1 + k ^ 2))
      (sinh (c - t) * sin (k * t)) t := by
  have hs := ((hasDerivAt_id t).const_mul k).sin
  have hc := ((hasDerivAt_id t).const_mul k).cos
  have hd := (hasDerivAt_const t c).sub (hasDerivAt_id t)
  convert! (((hd.cosh.neg).mul hs).sub ((hd.sinh.const_mul k).mul hc)).div_const (1 + k ^ 2) using 1
  all_goals first | rfl | (simp only [id_eq, Pi.sub_apply, Pi.neg_apply]; field_simp; ring)

/-- Exact definite integral of `sinh(t) sin(kt)`. -/
theorem integral_sinh_mul_sin (k a b : ℝ) :
    (∫ t in a..b, sinh t * sin (k * t)) =
      (cosh b * sin (k * b) - k * sinh b * cos (k * b)) / (1 + k ^ 2) -
      (cosh a * sin (k * a) - k * sinh a * cos (k * a)) / (1 + k ^ 2) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_sinh_sin_primitive k t)
    ((continuous_sinh.mul (continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable a b)

/-- Exact definite integral of `sinh(c-t) sin(kt)`. -/
theorem integral_sinh_sub_mul_sin (c k a b : ℝ) :
    (∫ t in a..b, sinh (c - t) * sin (k * t)) =
      (-cosh (c - b) * sin (k * b) - k * sinh (c - b) * cos (k * b)) / (1 + k ^ 2) -
      (-cosh (c - a) * sin (k * a) - k * sinh (c - a) * cos (k * a)) / (1 + k ^ 2) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_sinh_sub_sin_primitive c k t)
    (((continuous_sinh.comp (continuous_const.sub continuous_id)).mul
      (continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable a b)

end Real
