import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory
open scoped ENNReal

/-- A measurable equivalence transports a density by composition with its inverse. -/
theorem MeasurableEquiv.map_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    (setLIntegral_map (μ := μ) hs (hf.comp e.symm.measurable) e.measurable).symm
