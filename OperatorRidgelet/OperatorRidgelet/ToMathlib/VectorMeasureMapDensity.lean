import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The variation of a pushed-forward vector measure with a density

For an integrable density `g : X → E` with respect to a positive measure `μ` and a map
`φ : X → Y`, the variation of the vector measure `(μ.withDensityᵥ g).map φ` is dominated by the
image of `‖g‖ μ`:

`∫⁻ F d|(μ.withDensityᵥ g).map φ| ≤ ∫⁻ ‖g x‖ₑ F(φ x) μ(dx)`

for every `F : Y → ℝ≥0∞` (`lintegral_variation_map_withDensityᵥ_le`), with no measurability
assumption on `F` or `φ` (for non-measurable `φ` the pushforward is `0`).  In particular the
total variation is at most `∫⁻ ‖g‖ₑ dμ` (`variation_map_withDensityᵥ_univ_le`).

For an arbitrary vector measure `v` and map `φ`, a function `F` with `F ∘ φ ≤ C` satisfies
`∫⁻ F d|v.map φ| ≤ C |v.map φ|(univ)` (`lintegral_variation_map_le_of_forall_le`); the proof
goes through measurable minorants of `F`, so no measurability of `F` or of the fibres of `φ`
is needed.
-/

open scoped ENNReal
open MeasureTheory Filter

namespace MeasureTheory.VectorMeasure

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- `∫⁻ F d|(μ.withDensityᵥ g).map φ| ≤ ∫⁻ ‖g x‖ₑ F(φ x) μ(dx)`. -/
theorem lintegral_variation_map_withDensityᵥ_le {μ : Measure X} {g : X → E} (hg : Integrable g μ)
    (φ : X → Y) (F : Y → ℝ≥0∞) :
    ∫⁻ y, F y ∂((μ.withDensityᵥ g).map φ).variation ≤ ∫⁻ x, ‖g x‖ₑ * F (φ x) ∂μ := by
  by_cases hφ : Measurable φ
  · have hae : AEMeasurable (fun x => ‖g x‖ₑ) μ := hg.aestronglyMeasurable.enorm
    calc ∫⁻ y, F y ∂((μ.withDensityᵥ g).map φ).variation
        ≤ ∫⁻ y, F y ∂((μ.withDensityᵥ g).variation.map φ) :=
          lintegral_mono' variation_map_le le_rfl
      _ ≤ ∫⁻ x, F (φ x) ∂(μ.withDensityᵥ g).variation := lintegral_map_le F φ
      _ = ∫⁻ x, F (φ x) ∂(μ.withDensity hae.mk) := by
          rw [Measure.variation_withDensityᵥ hg, withDensity_congr_ae hae.ae_eq_mk]
      _ ≤ ∫⁻ x, (hae.mk * fun x => F (φ x)) x ∂μ :=
          lintegral_withDensity_le_lintegral_mul μ hae.measurable_mk _
      _ = ∫⁻ x, ‖g x‖ₑ * F (φ x) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae.ae_eq_mk] with x hx
          rw [Pi.mul_apply, ← hx]
  · rw [VectorMeasure.map_not_measurable _ hφ, variation_zero, lintegral_zero_measure]
    exact bot_le

/-- The total variation of `(μ.withDensityᵥ g).map φ` is at most `∫⁻ ‖g‖ₑ dμ`. -/
theorem variation_map_withDensityᵥ_univ_le {μ : Measure X} {g : X → E} (hg : Integrable g μ)
    (φ : X → Y) :
    ((μ.withDensityᵥ g).map φ).variation Set.univ ≤ ∫⁻ x, ‖g x‖ₑ ∂μ := by
  have h := lintegral_variation_map_withDensityᵥ_le hg φ fun _ => (1 : ℝ≥0∞)
  simpa [lintegral_one] using h

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- If `F ∘ φ ≤ C`, then `∫⁻ F d|v.map φ| ≤ C |v.map φ|(univ)`. -/
theorem lintegral_variation_map_le_of_forall_le (v : VectorMeasure X E) (φ : X → Y)
    {F : Y → ℝ≥0∞} {C : ℝ≥0∞} (hF : ∀ x, F (φ x) ≤ C) :
    ∫⁻ y, F y ∂(v.map φ).variation ≤ C * (v.map φ).variation Set.univ := by
  by_cases hφ : Measurable φ
  · rw [lintegral_def]
    refine iSup₂_le fun s hs => ?_
    rw [← SimpleFunc.lintegral_eq_lintegral, ← lintegral_const]
    refine lintegral_mono_ae ?_
    rw [ae_iff]
    have hE : MeasurableSet {y | ¬ s y ≤ C} := by
      have : {y | ¬ s y ≤ C} = s ⁻¹' Set.Ioi C := by
        ext y
        simp [not_le]
      rw [this]
      exact s.measurableSet_preimage _
    refine le_antisymm ?_ bot_le
    calc (v.map φ).variation {y | ¬ s y ≤ C}
        ≤ (v.variation.map φ) {y | ¬ s y ≤ C} := Measure.le_iff'.1 variation_map_le _
      _ = v.variation (φ ⁻¹' {y | ¬ s y ≤ C}) := Measure.map_apply hφ hE
      _ = 0 := by
          have : φ ⁻¹' {y | ¬ s y ≤ C} = ∅ := by
            ext x
            simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
              not_not]
            exact (hs (φ x)).trans (hF x)
          rw [this, measure_empty]
  · rw [VectorMeasure.map_not_measurable _ hφ, variation_zero, lintegral_zero_measure]
    exact bot_le

end MeasureTheory.VectorMeasure
