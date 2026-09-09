import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The lower Lebesgue integral of the Cauchy weight

The weight `c ↦ (1 + c²)⁻¹` is the standard integrable majorant used to absorb the tail of a
rapidly decreasing function against a polynomially growing one.  Mathlib's
`integrable_inv_one_add_sq` gives its Bochner integrability; the `ℝ≥0∞`-valued restatement below
is what dominated-convergence and Tonelli estimates need.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

open scoped ENNReal

/-- The lower Lebesgue integral of the Cauchy weight `(1 + c²)⁻¹` is finite. -/
theorem lintegral_ofReal_inv_one_add_sq_lt_top :
    (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) < ⊤ := by
  have h := integrable_inv_one_add_sq.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun c => ?_)) h
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end OperatorRidgelet
