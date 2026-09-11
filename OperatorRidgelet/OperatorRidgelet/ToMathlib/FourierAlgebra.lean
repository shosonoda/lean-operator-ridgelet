import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Fourier L¹ estimates for products, dilations, and series -/

noncomputable section
open MeasureTheory Complex Filter Topology Set
open scoped FourierTransform Convolution
namespace MeasureTheory

/-- A measurable series with summable integrals of norms defines an integrable function. -/
theorem integrable_tsum_of_summable_integral_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] {f : ℕ → X → ℂ} (hm : ∀ n, Measurable (f n))
    (hi : ∀ n, Integrable (f n) μ) (hs : Summable (fun n => ∫ x, ‖f n x‖ ∂μ)) :
    Integrable (fun x => ∑' n, f n x) μ := by
  have hm' : Measurable (Function.uncurry f) := measurable_from_prod_countable_right hm
  have hp : Integrable (Function.uncurry f) (Measure.count.prod μ) := by
    apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hi, integrable_count_iff.mpr ?_⟩
    simpa only [Function.uncurry, Real.norm_eq_abs] using hs.abs
  apply hp.integral_prod_right.congr
  filter_upwards [hp.prod_left_ae] with x hx
  simpa using integral_countable hx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The L¹ norm of a complex convolution is at most the product of the L¹ norms. -/
theorem integral_norm_convolution_mul_le {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
      (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hb := hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x, ((fun y => ‖f y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => ‖g y‖)) x := by
      apply integral_mono_ae (hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg).norm hb
      filter_upwards with x
      simp only [convolution_def, ContinuousLinearMap.mul_apply']
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun t => f t * g (x - t))
    _ = _ := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

end MeasureTheory

namespace Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A positive dilation of the argument acts by reciprocal dilation on the inverse Fourier
transform. -/
theorem fourierInv_comp_smul (f : E → ℂ) {t : ℝ} (ht : 0 < t) (x : E) :
    𝓕⁻ (fun y => f (t • y)) x = ((t ^ Module.finrank ℝ E)⁻¹ : ℝ) • 𝓕⁻ f (t⁻¹ • x) := by
  rw [fourierInv_eq, fourierInv_eq]
  have heq : (fun y : E => 𝐞 (inner ℝ y x) • f (t • y)) =
      (fun y : E => 𝐞 (inner ℝ y (t⁻¹ • x)) • f y) ∘ (fun y => t • y) := by
    funext y
    dsimp only [Function.comp_def]
    rw [real_inner_smul_left, real_inner_smul_right]
    simp [ht.ne']
  rw [heq]
  exact Measure.integral_comp_smul_of_nonneg (volume : Measure E)
    (fun y : E => 𝐞 (inner ℝ y (t⁻¹ • x)) • f y) t (hR := ht.le)

/-- The L¹ norm of the inverse Fourier transform is invariant under positive argument dilation. -/
theorem integral_norm_fourierInv_comp_smul (f : E → ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖𝓕⁻ (fun y => f (t • y)) x‖) = ∫ x, ‖𝓕⁻ f x‖ := by
  simp_rw [fourierInv_comp_smul f ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos ht _))]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E)
    (fun x : E => ‖𝓕⁻ f x‖) ht.le,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

/-- A positive dilation of the argument acts by reciprocal dilation on the Fourier transform. -/
theorem fourier_comp_smul (f : E → ℂ) {t : ℝ} (ht : 0 < t) (x : E) :
    𝓕 (fun y => f (t • y)) x = ((t ^ Module.finrank ℝ E)⁻¹ : ℝ) • 𝓕 f (t⁻¹ • x) := by
  have h := fourierInv_comp_smul f ht (-x)
  simpa only [fourierInv_eq_fourier_neg, neg_neg, smul_neg] using h

end Real

namespace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Composition of a Schwartz function with a nonzero real dilation. -/
def dilate (φ : SchwartzMap E ℂ) (t : ℝ) (ht : t ≠ 0) : SchwartzMap E ℂ :=
  compCLMOfContinuousLinearEquiv ℂ (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv φ

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise evaluation of the dilated Schwartz function. -/
theorem dilate_apply (φ : SchwartzMap E ℂ) (t : ℝ) (ht : t ≠ 0) (x : E) :
    dilate φ t ht x = φ (t • x) := rfl

/-- Positive dilation preserves the inverse Fourier L¹ norm of a Schwartz function. -/
theorem integral_norm_fourierInv_dilate (φ : SchwartzMap E ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖𝓕⁻ (dilate φ t ht.ne') x‖) = ∫ x, ‖𝓕⁻ φ x‖ := by
  simp_rw [fourierInv_coe]
  exact Real.integral_norm_fourierInv_comp_smul φ ht

/-- Multiplication of Schwartz functions is submultiplicative for the inverse Fourier L¹ norm. -/
theorem integral_norm_fourierInv_pairing_le (φ ψ : SchwartzMap E ℂ) :
    (∫ x, ‖𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) φ ψ) x‖) ≤
      (∫ x, ‖𝓕⁻ φ x‖) * (∫ x, ‖𝓕⁻ ψ x‖) := by
  have heq : 𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) φ ψ) =
      convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ φ) (𝓕⁻ ψ) := by
    simp [convolution]
  rw [heq]
  simp_rw [convolution_apply]
  exact integral_norm_convolution_mul_le (𝓕⁻ φ).integrable (𝓕⁻ ψ).integrable

end SchwartzMap
