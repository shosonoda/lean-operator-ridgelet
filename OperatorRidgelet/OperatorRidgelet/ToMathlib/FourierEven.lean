import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The inverse Fourier transform of a real even function is real

For an even real function `f`, the inverse Fourier transform `𝓕⁻ (fun x => (f x : ℂ))` is
invariant under complex conjugation, hence real-valued.
-/

open MeasureTheory Complex
open scoped FourierTransform

namespace Real

/-- The inverse Fourier transform of a real even function equals its own conjugate. -/
theorem conj_fourierInv_ofReal_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (t : ℝ) :
    (starRingEnd ℂ) (𝓕⁻ (fun x => (f x : ℂ)) t) = 𝓕⁻ (fun x => (f x : ℂ)) t := by
  rw [Real.fourierInv_eq', ← integral_conj]
  have h1 : (fun v : ℝ => (starRingEnd ℂ)
      (Complex.exp (((2 * π * inner ℝ v t : ℝ) : ℂ) * I) • ((f v : ℝ) : ℂ))) =
      fun v => (fun w : ℝ => Complex.exp (((2 * π * inner ℝ w t : ℝ) : ℂ) * I) • ((f w : ℝ) : ℂ))
        (-v) := by
    funext v
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
      inner_neg_left, hf]
    congr 2
    push_cast
    ring
  rw [h1]
  have h2 := Measure.integral_comp_mul_left
    (fun w : ℝ => Complex.exp (((2 * π * inner ℝ w t : ℝ) : ℂ) * I) • ((f w : ℝ) : ℂ)) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h2
  exact h2

end Real
