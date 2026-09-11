import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Orthogonality integrals for positive sine frequencies -/

noncomputable section
open MeasureTheory

namespace Real

/-- Integrating a cosine through an integral number of half-turns gives zero. -/
theorem integral_cos_mul_zero {a : ℝ} (ha : a ≠ 0) (hs : sin a = 0) :
    (∫ t in (0 : ℝ)..1, cos (a * t)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left _ ha, integral_cos]
  simp [hs]

/-- Positive sine frequencies are orthonormal after multiplication by `sqrt 2`. -/
theorem integral_normalized_sin_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∫ t in (0 : ℝ)..1,
      (sqrt 2 * sin (m * Real.pi * t)) * (sqrt 2 * sin (n * Real.pi * t))) =
      if m = n then 1 else 0 := by
  have hproduct (t : ℝ) :
      (sqrt 2 * sin (m * Real.pi * t)) * (sqrt 2 * sin (n * Real.pi * t)) =
        cos (((m : ℝ) - n) * Real.pi * t) - cos (((m : ℝ) + n) * Real.pi * t) := by
    rw [show ((m : ℝ) - n) * Real.pi * t = m * Real.pi * t - n * Real.pi * t by ring,
      show ((m : ℝ) + n) * Real.pi * t = m * Real.pi * t + n * Real.pi * t by ring,
      cos_sub, cos_add]
    have hs := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [congrArg (fun r : ℝ => r * sin (m * Real.pi * t) * sin (n * Real.pi * t)) hs]
  simp_rw [hproduct]
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun t : ℝ => cos (((m : ℝ) - n) * Real.pi * t)).intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun t : ℝ => cos (((m : ℝ) + n) * Real.pi * t)).intervalIntegrable 0 1)]
  have hsum : ((m : ℝ) + n) * Real.pi ≠ 0 := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hsum_sin : sin (((m : ℝ) + n) * Real.pi) = 0 := by
    rw [add_mul, sin_add]
    simp
  rw [integral_cos_mul_zero hsum hsum_sin, sub_zero]
  by_cases hmn : m = n
  · subst n
    simp
  · rw [if_neg hmn]
    apply integral_cos_mul_zero
    · exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hmn)) pi_ne_zero
    · rw [sub_mul, sin_sub]
      simp

end Real

