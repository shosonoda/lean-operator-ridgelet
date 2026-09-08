import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Fourier transform of a dilated function on `ℝ`

`𝓕 (f (c ·)) w = |c|⁻¹ 𝓕 f (w / c)` for `c ≠ 0`, by the change of variables `x ↦ c x`.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Real

/-- The Fourier transform of a dilated function: `𝓕 (f (c ·)) w = |c|⁻¹ • 𝓕 f (c⁻¹ w)`. -/
theorem fourier_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) {c : ℝ} (hc : c ≠ 0) (w : ℝ) :
    𝓕 (fun x => f (c * x)) w = |c|⁻¹ • 𝓕 f (c⁻¹ * w) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have h := Measure.integral_comp_mul_left (fun u : ℝ => 𝐞 (-⟪u, c⁻¹ * w⟫) • f u) c
  rw [abs_inv] at h
  rw [← h]
  congr 1
  funext v
  congr 3
  simp only [RCLike.inner_apply, conj_trivial]
  field_simp

end Real
