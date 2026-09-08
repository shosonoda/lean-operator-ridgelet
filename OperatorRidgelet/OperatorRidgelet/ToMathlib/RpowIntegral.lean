import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The power function has infinite integral over `(0, ∞)`

For every real exponent `β`, `∫_0^∞ s^β ds = ∞`: the integral diverges at `0` when `β ≤ -1`
and at `∞` when `β ≥ -1`.
-/

open MeasureTheory Set
open scoped ENNReal

/-- The power function `s ↦ s^β` has infinite Lebesgue integral over `(0, ∞)` for every real
`β`. -/
theorem lintegral_Ioi_rpow_eq_top (β : ℝ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ β) = ⊤ := by
  have hmeas : Measurable fun s : ℝ => s ^ β := by fun_prop
  have key : ∀ T : Set ℝ, MeasurableSet T → T ⊆ Ioi 0 →
      ¬ IntegrableOn (fun s : ℝ => s ^ β) T → ∫⁻ s in T, ENNReal.ofReal (s ^ β) = ⊤ := by
    intro T hT hT' hnot
    by_contra h
    apply hnot
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hT fun s hs =>
      Real.rpow_nonneg (le_of_lt (hT' hs)) β)]
    exact lt_top_iff_ne_top.mpr h
  by_cases hβ : β < -1
  · refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ β) := by
          refine (key _ measurableSet_Ioo Ioo_subset_Ioi_self fun h => ?_).symm
          exact absurd ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mp h)
            (not_lt.mpr hβ.le)
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ β) := lintegral_mono_set Ioo_subset_Ioi_self
  · refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (s ^ β) := by
          refine (key _ measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) fun h => ?_).symm
          exact hβ ((integrableOn_Ioi_rpow_iff one_pos).mp h)
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ β) :=
          lintegral_mono_set (Ioi_subset_Ioi zero_le_one)
