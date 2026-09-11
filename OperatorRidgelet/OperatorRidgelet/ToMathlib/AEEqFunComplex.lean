import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Analysis.Complex.Basic

/-! # Real-valued almost-everywhere classes in a complex target -/

noncomputable section
open Filter
namespace MeasureTheory

/-- The real-linear inclusion of real-valued a.e. classes into complex-valued a.e. classes. -/
def aeOfReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    (Ω →ₘ[μ] ℝ) →ₗ[ℝ] (Ω →ₘ[μ] ℂ) where
  toFun := AEEqFun.comp Complex.ofReal Complex.continuous_ofReal
  map_add' f g := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal (f+g),
      AEEqFun.coeFn_add f g,
      AEEqFun.coeFn_add (AEEqFun.comp Complex.ofReal Complex.continuous_ofReal f)
        (AEEqFun.comp Complex.ofReal Complex.continuous_ofReal g),
      AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal f,
      AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal g] with t h1 h2 h3 h4 h5
    simp only [Function.comp_apply, Pi.add_apply] at *
    rw [h1, h2, h3, h4, h5, Complex.ofReal_add]
  map_smul' c f := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal (c • f),
      AEEqFun.coeFn_smul c f,
      AEEqFun.coeFn_smul c (AEEqFun.comp Complex.ofReal Complex.continuous_ofReal f),
      AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal f] with t h1 h2 h3 h4
    simp only [Function.comp_apply, RingHom.id_apply, Pi.smul_apply] at *
    rw [h1, h2, h3, h4]
    simp


end MeasureTheory
