import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy–Schwarz for the Bochner integral of a product of nonnegative functions

`integral_mul_le_sqrt_mul_sqrt`: `∫ f g ≤ √(∫ f²) √(∫ g²)` for nonnegative square-integrable
real functions, which is Hölder's inequality at the conjugate pair `(2, 2)` written with square
roots.
-/

open MeasureTheory

/-- **Cauchy–Schwarz** for the Bochner integral: `∫ f g ≤ √(∫ f²) √(∫ g²)` for nonnegative
square-integrable real functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ a, f a * g a ∂μ ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  have hsq : ∀ u : α → ℝ, ∫ a, u a ^ (2 : ℝ) ∂μ = ∫ a, u a ^ 2 ∂μ := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hsq f, hsq g] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
