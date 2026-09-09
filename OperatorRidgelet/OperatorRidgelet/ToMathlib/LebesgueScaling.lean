import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Scaling the real line and Lebesgue measure

Small general facts about the maps `x ↦ R x`, `R ≠ 0`, on `ℝ` with Lebesgue measure: they are
quasi-measure-preserving, they preserve `MemLp` and almost-everywhere strong measurability, and
the lower Lebesgue integral of `x ↦ F (R x)` is `|R|⁻¹ ∫⁻ F` (for almost-everywhere measurable
`F`).  Companions of `MeasureTheory.Integrable.comp_mul_left'` and
`MeasureTheory.Measure.integral_comp_mul_left`.
-/

open scoped ENNReal

namespace MeasureTheory

/-- Scaling the real line by a nonzero constant is quasi-measure-preserving for Lebesgue
measure. -/
theorem quasiMeasurePreserving_mul_left_volume {R : ℝ} (hR : R ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => R * x) volume volume :=
  ⟨measurable_const_mul R, by
    rw [Real.map_volume_mul_left hR]
    exact Measure.absolutelyContinuous_of_le_smul le_rfl⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- Almost-everywhere strong measurability is preserved under scaling of the real line. -/
theorem AEStronglyMeasurable.comp_mul_left {g : ℝ → E} (hg : AEStronglyMeasurable g volume)
    {R : ℝ} (hR : R ≠ 0) : AEStronglyMeasurable (fun x => g (R * x)) volume :=
  hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_mul_left_volume hR)

/-- Membership in `L^p` is preserved under scaling of the real line. -/
theorem MemLp.comp_mul_left {p : ℝ≥0∞} {g : ℝ → E} (hg : MemLp g p volume) {R : ℝ}
    (hR : R ≠ 0) : MemLp (fun x => g (R * x)) p volume := by
  have h := hg.smul_measure (c := ENNReal.ofReal |R⁻¹|) ENNReal.ofReal_ne_top
  rw [← Real.map_volume_mul_left hR] at h
  exact h.comp_of_map (measurable_const_mul R).aemeasurable

/-- Scaling the variable of a lower Lebesgue integral on `ℝ`, for an almost-everywhere
measurable integrand. -/
theorem lintegral_comp_mul_left_volume {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) {R : ℝ}
    (hR : R ≠ 0) : ∫⁻ x, F (R * x) = ENNReal.ofReal |R⁻¹| * ∫⁻ y, F y := by
  have hF' : AEMeasurable F (Measure.map (fun x : ℝ => R * x) volume) := by
    rw [Real.map_volume_mul_left hR]
    exact hF.smul_measure _
  rw [← lintegral_map' hF' (measurable_const_mul R).aemeasurable, Real.map_volume_mul_left hR,
    lintegral_smul_measure, smul_eq_mul]

end MeasureTheory
