import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# The polar decomposition of a complex measure of finite variation

A complex measure `c` of finite variation `|c| = c.variation` is absolutely continuous with
respect to `|c|`, so the Radon–Nikodym theorem for signed measures, applied to the real and
imaginary parts, gives `c = |c|.withDensityᵥ h` with `h = c.rnDeriv |c|`; taking variations of
both sides shows `‖h‖ = 1` `|c|`-almost everywhere.  This is the polar decomposition
`c = h |c|`.

* `ComplexMeasure.withDensityᵥ_rnDeriv_variation`: `|c|.withDensityᵥ (c.rnDeriv |c|) = c`;
* `ComplexMeasure.ae_norm_rnDeriv_variation_eq_one`: `‖c.rnDeriv |c|‖ = 1` almost everywhere;
* `ComplexMeasure.exists_withDensityᵥ_variation_eq`: the existence statement.
-/

open scoped ENNReal
open MeasureTheory

namespace MeasureTheory.ComplexMeasure

variable {α : Type*} [MeasurableSpace α]

/-- A complex measure is absolutely continuous with respect to its variation measure. -/
theorem absolutelyContinuous_variation (c : ComplexMeasure α) :
    c ≪ᵥ c.variation.toENNRealVectorMeasure :=
  VectorMeasure.absolutelyContinuous c

/-- The real part of a complex measure is absolutely continuous with respect to the
variation of the complex measure. -/
theorem re_absolutelyContinuous_variation (c : ComplexMeasure α) :
    c.re ≪ᵥ c.variation.toENNRealVectorMeasure := fun s hs => by
  show (c s).re = 0
  rw [c.absolutelyContinuous_variation hs, Complex.zero_re]

/-- The imaginary part of a complex measure is absolutely continuous with respect to the
variation of the complex measure. -/
theorem im_absolutelyContinuous_variation (c : ComplexMeasure α) :
    c.im ≪ᵥ c.variation.toENNRealVectorMeasure := fun s hs => by
  show (c s).im = 0
  rw [c.absolutelyContinuous_variation hs, Complex.zero_im]

/-- The Radon–Nikodym theorem for a complex measure with respect to its variation:
`|c|.withDensityᵥ (c.rnDeriv |c|) = c`. -/
theorem withDensityᵥ_rnDeriv_variation (c : ComplexMeasure α) [IsFiniteMeasure c.variation] :
    c.variation.withDensityᵥ (c.rnDeriv c.variation) = c := by
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq c.re c.variation
    (re_absolutelyContinuous_variation c)
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq c.im c.variation
    (im_absolutelyContinuous_variation c)
  ext s hs
  rw [withDensityᵥ_apply (c.integrable_rnDeriv _) hs]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re (c.integrable_rnDeriv _).integrableOn,
      RCLike.re_eq_complex_re]
    have h1 : ∫ x in s, (c.rnDeriv c.variation x).re ∂c.variation =
        c.variation.withDensityᵥ (c.re.rnDeriv c.variation) s :=
      (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs).symm
    rw [h1, hre]
    rfl
  · rw [← RCLike.im_eq_complex_im, ← integral_im (c.integrable_rnDeriv _).integrableOn,
      RCLike.im_eq_complex_im]
    have h1 : ∫ x in s, (c.rnDeriv c.variation x).im ∂c.variation =
        c.variation.withDensityᵥ (c.im.rnDeriv c.variation) s :=
      (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs).symm
    rw [h1, him]
    rfl

/-- The Radon–Nikodym derivative of a complex measure with respect to its variation has norm
one almost everywhere. -/
theorem ae_norm_rnDeriv_variation_eq_one (c : ComplexMeasure α) [IsFiniteMeasure c.variation] :
    ∀ᵐ x ∂c.variation, ‖c.rnDeriv c.variation x‖ = 1 := by
  have hint := c.integrable_rnDeriv c.variation
  have hvar : (c.variation.withDensityᵥ (c.rnDeriv c.variation)).variation =
      c.variation.withDensity fun x => ‖c.rnDeriv c.variation x‖ₑ :=
    Measure.variation_withDensityᵥ hint
  rw [withDensityᵥ_rnDeriv_variation c] at hvar
  have h1 : (fun x => ‖c.rnDeriv c.variation x‖ₑ) =ᵐ[c.variation] fun _ => (1 : ℝ≥0∞) := by
    refine (withDensity_eq_iff_of_sigmaFinite hint.aestronglyMeasurable.enorm
      aemeasurable_const).mp ?_
    rw [← hvar]
    exact withDensity_one.symm
  filter_upwards [h1] with x hx
  rw [enorm_eq_nnnorm, ENNReal.coe_eq_one] at hx
  rw [← coe_nnnorm, hx, NNReal.coe_one]

/-- **Polar decomposition** of a complex measure of finite variation: there is a density `h`
with `‖h‖ = 1` `|c|`-almost everywhere and `c = |c|.withDensityᵥ h`. -/
theorem exists_withDensityᵥ_variation_eq (c : ComplexMeasure α) [IsFiniteMeasure c.variation] :
    ∃ g : α → ℂ, (∀ᵐ x ∂c.variation, ‖g x‖ = 1) ∧ c = c.variation.withDensityᵥ g :=
  ⟨c.rnDeriv c.variation, c.ae_norm_rnDeriv_variation_eq_one,
    (withDensityᵥ_rnDeriv_variation c).symm⟩

end MeasureTheory.ComplexMeasure
