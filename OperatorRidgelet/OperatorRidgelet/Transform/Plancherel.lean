import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.Transform.Mixture
import OperatorRidgelet.ToMathlib.Logic
import OperatorRidgelet.ToMathlib.CharFunDensity
import OperatorRidgelet.ToMathlib.L2Glue
import OperatorRidgelet.ToMathlib.LebesgueScaling
import LeanRidgelet.ToMathlib.FourierPlancherel
import LeanRidgelet.ToMathlib.L2Duality
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Plancherel in the bias variable, the coefficient operator, and Theorem B

Ridgelet-specific results behind Section 3.2–3.4 of the manuscript (Lemma
`lem:coefficient-isometry`, Lemma `lem:spectral-unitary`, Theorem `thm:B`, and its
abstract-weight version `thm:general-weights`), for an abstract pair `(μ, ν)`: `μ` a probability
measure on `H` and `ν` an s-finite measure homogeneous of degree `α`.

* **Bridges.** The manuscript's line Fourier transform `ĥ(ω) = ∫ h(t) e^{-itω} dt` and the partial
  Fourier transform in the bias are Mathlib's `𝓕` at the rescaled frequency `ω / 2π`.
* **Separation of variables.** Tonelli/Fubini and the homogeneity `(D_ω)_# ν = |ω|^{-α} ν`
  separate `∫ K(ω) F(-ωa) d(ν ⊗ dω) = (∫ K(ω) |ω|^{-α} dω) ∫ F dν`.
* **Plancherel identity.** Along each bias line `R_ρ f(a, ·) ∈ L¹ ∩ L²`, so the `L¹ ∩ L²`
  Plancherel and Parseval identities of `LeanRidgelet.ToMathlib.FourierPlancherel` apply, and
  the Fourier-slice identity gives `‖R_ρ f‖²_{L²(λ)} = C_ρ ‖𝒢_μ f‖²_{L²(ν)}` and the cross
  identity `⟨R_{ρ₁} f, R_{ρ₂} g⟩ = C_{ρ₁,ρ₂} ⟨f, g⟩_𝓔` (`memLp_ridgelet`,
  `integral_ridgelet_mul_conj`).
* **The coefficient operator.** For measurable `G ∈ L²(ν)` the ray function `ω ↦ ρ̂(ω) G(-ωa)`
  is in `L¹ ∩ L²` for `ν`-almost every `a` (a weighted Cauchy–Schwarz argument with the weight
  `|ω|^α (1 + ω²)⁻¹`), so the explicit coefficient `γ_G = coefficientFormula ρ G` is defined
  pointwise, is jointly measurable, square integrable, and has the partial Fourier transform
  `ρ̂(ω) G(-ωa)` in the sense of `HasBiasFourier`; uniqueness of the coefficient with a given
  bias transform follows from the density of test functions.  Hence
  `W_ρ G = spectralCoefficient ν ρ G` is the class of `γ_G` (`spectralCoefficient_eq_toLp`)
  with `‖W_ρ G‖² = C_ρ ‖G‖²`.
* **The bounded extension.** `R_ρ` extends from the dense image of the core to
  `ridgeletExtensionCLM : 𝒦 →L L²(λ)` (`LinearMap.extendOfNorm`), a scaled isometry with closed
  range, uniquely determined by its values on the core, and equal to `W_ρ` on `𝒦`.
* **Injectivity.** `R_ρ f = 0` forces `𝒢_μ f = 0` on a set of full `ν`-measure by the slice
  identity and homogeneity, hence everywhere for full-support `ν`, and Fourier uniqueness for
  densities (`OperatorRidgelet.ToMathlib.CharFunDensity`) gives `f = 0`.
* **The Gaussian mixture** `ν_α` is s-finite (`IsCenteredGaussianLayers.sfinite_gaussianMixture`),
  which is all that the Plancherel theory needs of it.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace FourierTransform

section Bridges

variable {H : Type*}

/-- The manuscript's line Fourier transform is Mathlib's `𝓕` at the rescaled frequency
`ω / 2π`. -/
theorem lineFourier_eq_fourier (h : ℝ → ℂ) (ω : ℝ) :
    lineFourier h ω = 𝓕 h ((2 * Real.pi)⁻¹ * ω) := by
  unfold lineFourier
  rw [LeanRidgelet.Fourier.angularFourierIntegralInner_eq_mathlib]
  rfl

/-- Mathlib's `𝓕` at `u` is the line Fourier transform at `2πu`. -/
theorem fourier_eq_lineFourier (h : ℝ → ℂ) (u : ℝ) :
    𝓕 h u = lineFourier h (2 * Real.pi * u) := by
  rw [lineFourier_eq_fourier, inv_mul_cancel_left₀ (by positivity)]

/-- The partial Fourier transform in the bias is the line Fourier transform of the bias
function. -/
theorem biasFourier_eq_lineFourier (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) :
    biasFourier γ a ω = lineFourier (fun c => γ (a, c)) ω := by
  unfold biasFourier lineFourier LeanRidgelet.Fourier.angularFourierIntegralInner
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The partial Fourier transform in the bias is Mathlib's `𝓕` of the bias function at the
rescaled frequency `ω / 2π`. -/
theorem biasFourier_eq_fourier (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) :
    biasFourier γ a ω = 𝓕 (fun c => γ (a, c)) ((2 * Real.pi)⁻¹ * ω) := by
  rw [biasFourier_eq_lineFourier, lineFourier_eq_fourier]

/-- Mathlib's `𝓕` of the bias function at `u` is the partial Fourier transform at `2πu`. -/
theorem fourier_bias_eq (γ : H × ℝ → ℂ) (a : H) (u : ℝ) :
    𝓕 (fun c => γ (a, c)) u = biasFourier γ a (2 * Real.pi * u) := by
  rw [biasFourier_eq_fourier, inv_mul_cancel_left₀ (by positivity)]

end Bridges

section Scaling

/-- Scaling the variable of a lower Lebesgue integral on `ℝ`. -/
theorem lintegral_comp_mul_left_real {F : ℝ → ℝ≥0∞} (hF : Measurable F) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ x, F (a * x) = ENNReal.ofReal |a⁻¹| * ∫⁻ y, F y := by
  rw [← lintegral_map hF (measurable_const_mul a), Real.map_volume_mul_left ha,
    lintegral_smul_measure, smul_eq_mul]

end Scaling

/-! ### Separation of variables by homogeneity -/

section Separation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- Tonelli and homogeneity separate a product-type integrand:
`∫⁻ K(ω) F(-ωa) d(ν ⊗ dω) = (∫⁻ K(ω) |ω|^{-α} dω) ∫⁻ F dν`. -/
theorem IsHomogeneous.lintegral_prod_neg_smul {α : ℝ} {ν : Measure H} [SFinite ν]
    (hν : IsHomogeneous α ν) {K : ℝ → ℝ≥0∞} (hK : Measurable K) {F : H → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p : H × ℝ, K p.2 * F (-(p.2 • p.1)) ∂ν.prod volume =
      (∫⁻ ω, K ω * ENNReal.ofReal (|ω| ^ (-α))) * ∫⁻ ξ, F ξ ∂ν := by
  have hmeas : Measurable fun p : H × ℝ => K p.2 * F (-(p.2 • p.1)) :=
    (hK.comp measurable_snd).mul
      (hF.comp (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable)
  rw [lintegral_prod_symm' _ hmeas]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have key : ∀ᵐ ω : ℝ ∂volume, ∫⁻ a, K ω * F (-(ω • a)) ∂ν =
      K ω * ENNReal.ofReal (|ω| ^ (-α)) * ∫⁻ ξ, F ξ ∂ν := by
    filter_upwards [h0] with ω hω
    rw [lintegral_const_mul (K ω) (f := fun a => F (-(ω • a))) (hF.comp (by fun_prop))]
    have : (fun a : H => F (-(ω • a))) = fun a => F ((-ω) • a) := by
      funext a
      rw [neg_smul]
    rw [this, hν.lintegral_smul (neg_ne_zero.mpr hω) hF, abs_neg, mul_assoc]
  rw [lintegral_congr_ae key,
    lintegral_mul_const (f := fun ω => K ω * ENNReal.ofReal (|ω| ^ (-α))) _ (hK.mul (by fun_prop))]

/-- Fubini and homogeneity separate a product-type integrand:
`∫ K(ω) F(-ωa) d(ν ⊗ dω) = (∫ K(ω) |ω|^{-α} dω) ∫ F dν`. -/
theorem IsHomogeneous.integral_prod_neg_smul {α : ℝ} {ν : Measure H} [SFinite ν]
    (hν : IsHomogeneous α ν) {K : ℝ → ℂ} {F : H → ℂ} (hF : Measurable F)
    (hint : Integrable (fun p : H × ℝ => K p.2 * F (-(p.2 • p.1))) (ν.prod volume)) :
    ∫ p : H × ℝ, K p.2 * F (-(p.2 • p.1)) ∂ν.prod volume =
      (∫ ω, K ω * ((|ω| ^ (-α) : ℝ) : ℂ)) * ∫ ξ, F ξ ∂ν := by
  rw [integral_prod_symm _ hint]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have key : ∀ᵐ ω : ℝ ∂volume, ∫ a, K ω * F (-(ω • a)) ∂ν =
      K ω * ((|ω| ^ (-α) : ℝ) : ℂ) * ∫ ξ, F ξ ∂ν := by
    filter_upwards [h0] with ω hω
    rw [integral_const_mul]
    have : (fun a : H => F (-(ω • a))) = fun a => F ((-ω) • a) := by
      funext a
      rw [neg_smul]
    rw [this, ← integral_map (measurable_const_smul (-ω)).aemeasurable
      hF.aestronglyMeasurable, hν (-ω) (neg_ne_zero.mpr hω), integral_smul_measure, abs_neg,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg ω) _), Complex.real_smul, mul_assoc]
  rw [integral_congr_ae key, integral_mul_const]

end Separation

/-! ### Continuity of the weighted Fourier transform -/

section GaussFourier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- `𝒢_μ f` is continuous for integrable `f` (dominated convergence). -/
theorem continuous_gaussFourier (μ : Measure H) {f : H → ℂ} (hf : Integrable f μ) :
    Continuous (gaussFourier μ f) := by
  unfold gaussFourier
  refine continuous_of_dominated (bound := fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · intro ξ
    exact hf.aestronglyMeasurable.mul (continuous_character ξ).aestronglyMeasurable
  · intro ξ
    filter_upwards with x
    rw [norm_mul, norm_character, mul_one]
  · filter_upwards with x
    unfold character
    fun_prop

omit [OpensMeasurableSpace H] in
/-- `𝒢_μ f` is bounded by `‖f‖_{L¹(μ)}`. -/
theorem norm_gaussFourier_le (μ : Measure H) (f : H → ℂ) (ξ : H) :
    ‖gaussFourier μ f ξ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  unfold gaussFourier
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, norm_character, mul_one]

end GaussFourier

/-! ### Almost-everywhere modification along rays -/

section Rays

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- Changing a function on a `ν`-null set changes `(a, ω) ↦ G(-ωa)` only on a `ν ⊗ dω`-null
set; no measurability of the functions is needed. -/
theorem IsHomogeneous.ae_ae_eq_neg_smul' {α : ℝ} {ν : Measure H} [SFinite ν]
    (hν : IsHomogeneous α ν) {ι : Type*} {G G' : H → ι} (hGG' : G =ᵐ[ν] G') :
    ∀ᵐ a ∂ν, (fun ω : ℝ => G (-(ω • a))) =ᵐ[volume] fun ω : ℝ => G' (-(ω • a)) := by
  obtain ⟨E, hEsub, hE, hE0⟩ := exists_measurable_superset_of_null (ae_iff.mp hGG')
  set S : Set (H × ℝ) := (fun p : H × ℝ => -(p.2 • p.1)) ⁻¹' E with hS_def
  have hS : MeasurableSet S :=
    (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable hE
  have hnull : (ν.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
      rw [ae_iff]
      simp
    rw [← lintegral_zero (μ := (volume : Measure ℝ))]
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with ω hω
    have : (fun a : H => (a, ω)) ⁻¹' S = (fun a : H => (-ω) • a) ⁻¹' E := by
      ext a
      simp [hS_def, neg_smul]
    rw [this, hν.measure_preimage_smul (neg_ne_zero.mpr hω) hE, hE0, mul_zero]
  have := (Measure.measure_prod_null hS).mp hnull
  filter_upwards [this] with a ha
  rw [Pi.zero_apply] at ha
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) ha
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def] at hω ⊢
  exact hEsub hω

end Rays


/-! ### The Fourier transform of a filter as a Schwartz function -/

section FilterFourier

/-- `ρ̂` is the Schwartz function `𝓕 ρ` at the rescaled frequency. -/
theorem filterFourier_eq_fourier_ofReal (ρ : SchwartzMap ℝ ℝ) :
    filterFourier ρ = fun ω => (𝓕 (SchwartzMap.ofReal ρ)) ((2 * Real.pi)⁻¹ * ω) := by
  funext ω
  rw [filterFourier_eq_fourier, SchwartzMap.fourier_coe]
  rfl

/-- `ρ̂` is continuous. -/
theorem continuous_filterFourier (ρ : SchwartzMap ℝ ℝ) : Continuous (filterFourier ρ) := by
  rw [filterFourier_eq_fourier_ofReal]
  exact (𝓕 (SchwartzMap.ofReal ρ)).continuous.comp (continuous_const.mul continuous_id)

/-- `ρ̂` is integrable. -/
theorem integrable_filterFourier (ρ : SchwartzMap ℝ ℝ) : Integrable (filterFourier ρ) := by
  rw [filterFourier_eq_fourier_ofReal]
  exact (𝓕 (SchwartzMap.ofReal ρ)).integrable.comp_mul_left' (by positivity)

/-- `ρ̂` is square integrable. -/
theorem memLp_filterFourier (ρ : SchwartzMap ℝ ℝ) : MemLp (filterFourier ρ) 2 volume := by
  rw [filterFourier_eq_fourier_ofReal]
  exact ((𝓕 (SchwartzMap.ofReal ρ)).memLp 2).comp_mul_left (by positivity)

/-- Quadratic decay of `ρ̂`: `ω² ‖ρ̂(ω)‖ ≤ C`. -/
theorem exists_sq_mul_norm_filterFourier_le (ρ : SchwartzMap ℝ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, ω ^ 2 * ‖filterFourier ρ ω‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (SchwartzMap.ofReal ρ)).decay 2 0
  refine ⟨(2 * Real.pi) ^ 2 * C, by positivity, fun ω => ?_⟩
  have h := hC ((2 * Real.pi)⁻¹ * ω)
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs, mul_pow] at h
  rw [filterFourier_eq_fourier_ofReal]
  have h2 : ω ^ 2 = (2 * Real.pi) ^ 2 * (((2 * Real.pi)⁻¹) ^ 2 * ω ^ 2) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow, one_mul]
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The admissibility integral as a lower Lebesgue integral: `∫⁻ ‖ρ̂‖ₑ² |ω|^{-α} = 2π C_ρ`. -/
theorem IsAdmissible.lintegral_enorm_sq_mul {α : ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) :
    ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ENNReal.ofReal (|ω| ^ (-α)) =
      ENNReal.ofReal (2 * Real.pi * admissibilityConst α ρ) := by
  rw [admissibilityConst, mul_inv_cancel_left₀ (by positivity),
    ofReal_integral_eq_lintegral_ofReal hρ.integrable (Eventually.of_forall fun ω => by positivity)]
  congr 1
  funext ω
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The weighted admissibility integral `∫ ‖ρ̂(ω)‖² |ω|^{-α} (1 + ω²) dω` is finite: near the
origin it is the admissibility integral, at infinity `ρ̂` decays quadratically. -/
theorem IsAdmissible.integrable_mul_one_add_sq {α : ℝ} (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsAdmissible α ρ) :
    Integrable fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * (|ω| ^ (-α) * (1 + ω ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_sq_mul_norm_filterFourier_le ρ
  have hbound : ∀ ω : ℝ, ‖filterFourier ρ ω‖ ^ 2 * (|ω| ^ (-α) * (1 + ω ^ 2)) ≤
      2 * (‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)) + C * ‖filterFourier ρ ω‖ := by
    intro ω
    set A := ‖filterFourier ρ ω‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    have hw0 : 0 ≤ |ω| ^ (-α) := Real.rpow_nonneg (abs_nonneg ω) _
    have hq0 : 0 ≤ ω ^ 2 := sq_nonneg ω
    rcases le_total (ω ^ 2) 1 with hq | hq
    · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg A) hw0) (sub_nonneg.mpr hq),
        mul_nonneg hC0 hA0, mul_nonneg (sq_nonneg A) hw0]
    · have hω : 1 ≤ |ω| := by
        rw [← sq_abs] at hq
        nlinarith [abs_nonneg ω]
      have hw1 : |ω| ^ (-α) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hω (by linarith)
      have hCA : ω ^ 2 * A ≤ C := hC ω
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg A) hq0) (sub_nonneg.mpr hw1),
        mul_nonneg hA0 (sub_nonneg.mpr hCA), mul_nonneg (sq_nonneg A) hw0]
  refine Integrable.mono' ((hρ.integrable.const_mul 2).add
    ((integrable_filterFourier ρ).norm.const_mul C)) ?_ (Eventually.of_forall fun ω => ?_)
  · exact (((continuous_filterFourier ρ).norm.pow 2).measurable.mul
      ((continuous_abs.measurable.pow_const (-α)).mul
        (by fun_prop : Measurable fun ω : ℝ => 1 + ω ^ 2)))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound ω

end FilterFourier

/-! ### Square integrability along rays -/

section Rays2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The weighted Tonelli identity for `(a, ω) ↦ ρ̂(ω) G(-ωa)`:
`∫⁻ ‖ρ̂(ω)‖ₑ² ‖G(-ωa)‖ₑ² d(ν ⊗ dω) = 2π C_ρ ∫⁻ ‖G‖ₑ² dν`. -/
theorem IsAdmissible.lintegral_prod_enorm_sq {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {G : H → ℂ}
    (hG : Measurable G) :
    ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 ∂ν.prod volume =
      ENNReal.ofReal (2 * Real.pi * admissibilityConst α ρ) * ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν := by
  rw [hν.lintegral_prod_neg_smul (K := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2)
    ((continuous_filterFourier ρ).measurable.enorm.pow_const 2) (hG.enorm.pow_const 2),
    hρ.lintegral_enorm_sq_mul]

/-- For `G ∈ L²(ν)`, `(a, ω) ↦ ρ̂(ω) G(-ωa)` is square integrable on `ν ⊗ dω`. -/
theorem IsAdmissible.lintegral_prod_enorm_sq_lt_top {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {G : H → ℂ}
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 ∂ν.prod volume < ⊤ := by
  rw [hρ.lintegral_prod_enorm_sq hν hG]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hG₂.lintegral_enorm_sq_lt_top)

end Rays2

/-! ### The ridgelet transform along a bias line -/

section Slices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

variable (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)

omit [IsProbabilityMeasure μ] in
/-- `R_ρ f` is jointly continuous. -/
theorem continuous_ridgelet {f : H → ℂ} (hf : Integrable f μ) : Continuous (ridgelet μ ρ f) := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  unfold ridgelet
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hf.norm.mul_const C) ?_
  · intro p
    exact hf.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun x : H => ⟪p.1, x⟫ + p.2))).aestronglyMeasurable
  · intro p
    filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hC.2 _) (norm_nonneg _)
  · filter_upwards with x
    fun_prop

/-- The bias function `R_ρ f(a, ·)` is integrable. -/
theorem integrable_ridgelet_slice {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Integrable (fun c : ℝ => ridgelet μ ρ f (a, c)) :=
  (integrable_ridgelet_kernel μ ρ hf a).integral_prod_right

/-- The bias function `R_ρ f(a, ·)` is square integrable for `f ∈ L²(μ)`. -/
theorem memLp_ridgelet_slice {f : H → ℂ} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (a : H) :
    MemLp (fun c : ℝ => ridgelet μ ρ f (a, c)) 2 volume := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  have hA : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hpt : ∀ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
    intro c
    have hρc : MemLp (fun x : H => (ρ (⟪a, x⟫ + c) : ℂ)) (ENNReal.ofReal 2) μ :=
      MemLp.of_bound (Complex.continuous_ofReal.comp (ρ.continuous.comp
        (by fun_prop : Continuous fun x : H => ⟪a, x⟫ + c))).aestronglyMeasurable C
        (Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hC.2 _)
    have h1 : ‖ridgelet μ ρ f (a, c)‖ ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp_rw [norm_mul, Complex.norm_real]
    have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (by simpa using hf₂) hρc
    simp_rw [Real.rpow_two, Complex.norm_real] at h2
    have hB : 0 ≤ ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    have h0 : 0 ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := integral_nonneg fun x => by positivity
    calc ‖ridgelet μ ρ f (a, c)‖ ^ 2
        ≤ (∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ) ^ 2 := by gcongr
      _ ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA,
            ← Real.rpow_mul hB]
          norm_num
  have hsq : Integrable (fun t : ℝ => ‖ρ t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm ρ.continuous.aestronglyMeasurable).mp (ρ.memLp 2)
  have hG : Integrable (fun q : H × ℝ => ‖ρ (⟪a, q.1⟫ + q.2)‖ ^ 2) (μ.prod volume) := by
    have hmeas : AEStronglyMeasurable (fun q : H × ℝ => ‖ρ (⟪a, q.1⟫ + q.2)‖ ^ 2)
        (μ.prod volume) :=
      ((ρ.continuous.comp (by fun_prop : Continuous fun q : H × ℝ => ⟪a, q.1⟫ + q.2)).norm.pow 2)
        |>.aestronglyMeasurable
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards with x
      exact hsq.comp_add_left ⟪a, x⟫
    · have : (fun x : H => ∫ c : ℝ, ‖‖ρ (⟪a, x⟫ + c)‖ ^ 2‖) = fun _ => ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
        funext x
        simp_rw [norm_pow, norm_norm]
        exact integral_add_left_eq_self (f := fun t => ‖ρ t‖ ^ 2) ⟪a, x⟫
      rw [this]
      exact integrable_const _
  have hGc : Integrable (fun c : ℝ => (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) :=
    hG.integral_prod_right.const_mul _
  have hmeasR : AEStronglyMeasurable (fun c : ℝ => ridgelet μ ρ f (a, c)) volume :=
    ((continuous_ridgelet μ ρ hf).comp (by fun_prop : Continuous fun c : ℝ => (a, c)))
      |>.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeasR]
  refine hGc.mono' (hmeasR.norm.pow 2) (Eventually.of_forall fun c => ?_)
  rw [norm_pow, norm_norm]
  exact hpt c

/-- The Fourier-slice identity `\widehat{R_ρ f}(a, ω) = ρ̂(ω) 𝒢_μ f(-ωa)`. -/
theorem biasFourier_ridgelet {f : H → ℂ} (hf : Integrable f μ) (a : H) (ω : ℝ) :
    biasFourier (ridgelet μ ρ f) a ω = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
  have hF := integrable_ridgelet_kernel μ ρ hf a
  have hF' : Integrable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ) *
      Complex.exp (-((ω * q.2 : ℝ) * Complex.I))) (μ.prod volume) := by
    refine hF.mul_unimodular ?_ (Eventually.of_forall fun q => ?_)
    · exact (by fun_prop : Continuous fun q : H × ℝ =>
        Complex.exp (-((ω * q.2 : ℝ) * Complex.I))).aestronglyMeasurable
    · rw [show -((ω * q.2 : ℝ) * Complex.I) = ((-(ω * q.2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hchar : ∀ x : H, character (-(ω • a)) x =
      Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) := by
    intro x
    simp only [character, inner_neg_right, inner_smul_right, real_inner_comm a x]
    push_cast
    ring_nf
  unfold biasFourier
  calc ∫ c : ℝ, ridgelet μ ρ f (a, c) * Complex.exp (-((ω * c : ℝ) * Complex.I))
      = ∫ c : ℝ, (∫ x, f x * (ρ (⟪a, x⟫ + c) : ℂ) *
          Complex.exp (-((ω * c : ℝ) * Complex.I)) ∂μ) := by
        congr 1
        funext c
        unfold ridgelet
        rw [← integral_mul_const]
    _ = ∫ x, (∫ c : ℝ, f x * (ρ (⟪a, x⟫ + c) : ℂ) *
          Complex.exp (-((ω * c : ℝ) * Complex.I))) ∂μ :=
        (integral_integral_swap hF').symm
    _ = ∫ x, (f x * character (-(ω • a)) x) * filterFourier ρ ω ∂μ := by
        congr 1
        funext x
        have hkey : (fun c : ℝ => f x * (ρ (⟪a, x⟫ + c) : ℂ) *
            Complex.exp (-((ω * c : ℝ) * Complex.I))) =
            fun c : ℝ => (f x * character (-(ω • a)) x) *
              ((fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))
                (⟪a, x⟫ + c)) := by
          funext c
          rw [hchar]
          have hexp : Complex.exp (-((ω * c : ℝ) * Complex.I)) =
              Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-Complex.I * ((inner ℝ (⟪a, x⟫ + c) ω : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            simp only [RCLike.inner_apply, conj_trivial]
            push_cast
            ring
          rw [hexp]
          ring
        rw [hkey, integral_const_mul, integral_add_left_eq_self
          (f := fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))]
        rfl
    _ = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
        rw [integral_mul_const, mul_comm]
        rfl

/-- Mathlib's Fourier transform of the bias function is the Fourier slice at frequency
`2πu`. -/
theorem fourier_ridgelet_slice {f : H → ℂ} (hf : Integrable f μ) (a : H) (u : ℝ) :
    𝓕 (fun c => ridgelet μ ρ f (a, c)) u =
      filterFourier ρ (2 * Real.pi * u) * gaussFourier μ f (-((2 * Real.pi * u) • a)) := by
  rw [fourier_bias_eq, biasFourier_ridgelet μ ρ hf]

/-- Plancherel along the bias line:
`∫⁻ ‖R_ρ f(a,c)‖ₑ² dc = (2π)⁻¹ ∫⁻ ‖ρ̂(ω)‖ₑ² ‖𝒢_μ f(-ωa)‖ₑ² dω`. -/
theorem lintegral_ridgelet_slice_sq {f : H → ℂ} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ)
    (a : H) :
    ∫⁻ c, ‖ridgelet μ ρ f (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖gaussFourier μ f (-(ω • a))‖ₑ ^ 2 := by
  rw [← (integrable_ridgelet_slice μ ρ hf a).lintegral_enorm_fourier_sq
    (memLp_ridgelet_slice μ ρ hf hf₂ a)]
  simp_rw [fourier_ridgelet_slice μ ρ hf a, enorm_mul, mul_pow]
  rw [lintegral_comp_mul_left_real
    (F := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2 * ‖gaussFourier μ f (-(ω • a))‖ₑ ^ 2)
    (((continuous_filterFourier ρ).measurable.enorm.pow_const 2).mul
      (((continuous_gaussFourier μ hf).comp
        (by fun_prop : Continuous fun ω : ℝ => -(ω • a))).measurable.enorm.pow_const 2))
    (by positivity), abs_of_pos (by positivity)]

/-- Parseval along the bias line for two transforms:
`∫ R_{ρ₁}f(a,c) conj(R_{ρ₂}g(a,c)) dc = (2π)⁻¹ ∫ ρ̂₁ conj ρ̂₂ (ω) 𝒢f conj 𝒢g (-ωa) dω`. -/
theorem integral_ridgelet_slice_mul_conj (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) {f g : H → ℂ}
    (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (hg : Integrable g μ) (hg₂ : MemLp g 2 μ) (a : H) :
    ∫ c, ridgelet μ ρ₁ f (a, c) * (starRingEnd ℂ) (ridgelet μ ρ₂ g (a, c)) =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ ω, (filterFourier ρ₁ ω * (starRingEnd ℂ) (filterFourier ρ₂ ω)) *
          (gaussFourier μ f (-(ω • a)) * (starRingEnd ℂ) (gaussFourier μ g (-(ω • a)))) := by
  rw [← (integrable_ridgelet_slice μ ρ₁ hf a).integral_fourier_mul_conj_fourier
    (memLp_ridgelet_slice μ ρ₁ hf hf₂ a) (integrable_ridgelet_slice μ ρ₂ hg a)
    (memLp_ridgelet_slice μ ρ₂ hg hg₂ a)]
  simp_rw [fourier_ridgelet_slice μ _ hf a, fourier_ridgelet_slice μ _ hg a]
  rw [Measure.integral_comp_mul_left (fun ω => filterFourier ρ₁ ω * gaussFourier μ f (-(ω • a)) *
    (starRingEnd ℂ) (filterFourier ρ₂ ω * gaussFourier μ g (-(ω • a)))) (2 * Real.pi),
    abs_of_pos (by positivity), Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [map_mul]
  ring

/-- Parseval along the bias line against a Schwartz test function: the ridgelet transform has
the Fourier slice as its partial Fourier transform in the bias, in the sense of
`HasBiasFourier`. -/
theorem hasBiasFourier_ridgelet (ν : Measure H) {f : H → ℂ} (hf : Integrable f μ)
    (hf₂ : MemLp f 2 μ) :
    HasBiasFourier ν (ridgelet μ ρ f)
      (fun a ω => filterFourier ρ ω * gaussFourier μ f (-(ω • a))) := by
  refine ⟨Eventually.of_forall fun a => ?_, Eventually.of_forall fun a φ => ?_⟩
  · refine MemLp.mul' (memLp_top_of_bound ?_ (∫ x, ‖f x‖ ∂μ)
      (Eventually.of_forall fun ω => norm_gaussFourier_le μ f _)) (memLp_filterFourier ρ)
    exact ((continuous_gaussFourier μ hf).comp
      (by fun_prop : Continuous fun ω : ℝ => -(ω • a))).aestronglyMeasurable
  rw [← (integrable_ridgelet_slice μ ρ hf a).integral_fourier_mul_conj_fourier
    (memLp_ridgelet_slice μ ρ hf hf₂ a) φ.integrable (φ.memLp 2)]
  simp_rw [fourier_ridgelet_slice μ ρ hf a, fourier_eq_lineFourier (φ : ℝ → ℂ)]
  rw [Measure.integral_comp_mul_left (fun ω => filterFourier ρ ω *
    gaussFourier μ f (-(ω • a)) * (starRingEnd ℂ) (lineFourier (⇑φ) ω)) (2 * Real.pi),
    abs_of_pos (by positivity), Complex.real_smul]

end Slices

/-! ### Square integrability and the Plancherel identity on `H × ℝ` -/

section Product

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable (μ : Measure H) [IsProbabilityMeasure μ] {ν : Measure H} [SFinite ν] {α : ℝ}

/-- The squared `L²(λ)` norm of `R_ρ f`, as a lower Lebesgue integral. -/
theorem lintegral_ridgelet_sq (ν : Measure H) [SFinite ν] (ρ : SchwartzMap ℝ ℝ) {f : H → ℂ}
    (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    ∫⁻ p, ‖ridgelet μ ρ f p‖ₑ ^ 2 ∂parameterMeasure ν =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ ^ 2
          ∂ν.prod volume := by
  have hmeas : Measurable fun p : H × ℝ => ‖ridgelet μ ρ f p‖ₑ ^ 2 :=
    (continuous_ridgelet μ ρ hf).measurable.enorm.pow_const 2
  have hmeas' : Measurable fun p : H × ℝ =>
      ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ ^ 2 :=
    (((continuous_filterFourier ρ).measurable.comp measurable_snd).enorm.pow_const 2).mul
      (((continuous_gaussFourier μ hf).measurable.comp
        (by fun_prop : Measurable fun p : H × ℝ => -(p.2 • p.1))).enorm.pow_const 2)
  unfold parameterMeasure
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_prod _ hmeas'.aemeasurable,
    ← lintegral_const_mul _ (Measurable.lintegral_prod_right' hmeas')]
  refine lintegral_congr fun a => ?_
  exact lintegral_ridgelet_slice_sq μ ρ hf hf₂ a

/-- `R_ρ f ∈ L²(λ)` for `f ∈ L²(μ)` with `𝒢_μ f ∈ L²(ν)` and `α`-admissible `ρ`. -/
theorem memLp_ridgelet (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
    {f : H → ℂ}
    (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (hG : MemLp (gaussFourier μ f) 2 ν) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure ν) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top
    (continuous_ridgelet μ ρ hf).aestronglyMeasurable ?_
  rw [lintegral_ridgelet_sq μ ν ρ hf hf₂]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (hρ.lintegral_prod_enorm_sq_lt_top hν (continuous_gaussFourier μ hf).measurable hG)

omit [IsProbabilityMeasure μ] in
/-- The product `(a, ω) ↦ ρ̂₁ conj ρ̂₂ (ω) 𝒢f conj 𝒢g (-ωa)` is integrable on `ν ⊗ dω`. -/
theorem integrable_cross_kernel (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁)
    (hρ₂ : IsAdmissible α ρ₂) {f g : H → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hGf : MemLp (gaussFourier μ f) 2 ν) (hGg : MemLp (gaussFourier μ g) 2 ν) :
    Integrable (fun p : H × ℝ => (filterFourier ρ₁ p.2 * (starRingEnd ℂ) (filterFourier ρ₂ p.2)) *
      (gaussFourier μ f (-(p.2 • p.1)) * (starRingEnd ℂ) (gaussFourier μ g (-(p.2 • p.1)))))
      (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  refine ⟨?_, ?_⟩
  · exact (((continuous_filterFourier ρ₁).comp continuous_snd).mul
      (Complex.continuous_conj.comp ((continuous_filterFourier ρ₂).comp continuous_snd))).mul
      (((continuous_gaussFourier μ hf).comp hc).mul
        (Complex.continuous_conj.comp ((continuous_gaussFourier μ hg).comp hc)))
      |>.aestronglyMeasurable
  · rw [HasFiniteIntegral]
    calc ∫⁻ p : H × ℝ, ‖(filterFourier ρ₁ p.2 * (starRingEnd ℂ) (filterFourier ρ₂ p.2)) *
          (gaussFourier μ f (-(p.2 • p.1)) *
            (starRingEnd ℂ) (gaussFourier μ g (-(p.2 • p.1))))‖ₑ ∂ν.prod volume
        ≤ ∫⁻ p : H × ℝ, ‖filterFourier ρ₁ p.2‖ₑ ^ 2 * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ ^ 2 +
            ‖filterFourier ρ₂ p.2‖ₑ ^ 2 * ‖gaussFourier μ g (-(p.2 • p.1))‖ₑ ^ 2
            ∂ν.prod volume := by
          refine lintegral_mono fun p => ?_
          simp only [enorm_mul, RCLike.enorm_conj]
          calc ‖filterFourier ρ₁ p.2‖ₑ * ‖filterFourier ρ₂ p.2‖ₑ *
                (‖gaussFourier μ f (-(p.2 • p.1))‖ₑ * ‖gaussFourier μ g (-(p.2 • p.1))‖ₑ)
              = (‖filterFourier ρ₁ p.2‖ₑ * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ) *
                (‖filterFourier ρ₂ p.2‖ₑ * ‖gaussFourier μ g (-(p.2 • p.1))‖ₑ) := by ring
            _ ≤ (‖filterFourier ρ₁ p.2‖ₑ * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ) ^ 2 +
                (‖filterFourier ρ₂ p.2‖ₑ * ‖gaussFourier μ g (-(p.2 • p.1))‖ₑ) ^ 2 :=
                ENNReal.mul_le_sq_add_sq _ _
            _ = _ := by ring
      _ < ⊤ := by
          have hm : Measurable fun p : H × ℝ =>
              ‖filterFourier ρ₁ p.2‖ₑ ^ 2 * ‖gaussFourier μ f (-(p.2 • p.1))‖ₑ ^ 2 :=
            (((continuous_filterFourier ρ₁).comp continuous_snd).measurable.enorm.pow_const 2).mul
              (((continuous_gaussFourier μ hf).comp hc).measurable.enorm.pow_const 2)
          rw [lintegral_add_left hm]
          exact ENNReal.add_lt_top.mpr
            ⟨hρ₁.lintegral_prod_enorm_sq_lt_top hν (continuous_gaussFourier μ hf).measurable hGf,
              hρ₂.lintegral_prod_enorm_sq_lt_top hν (continuous_gaussFourier μ hg).measurable hGg⟩

/-- **Plancherel identity** for the ridgelet transform:
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ)} = C^{(α)}_{ρ₁,ρ₂} ⟨f, g⟩_𝓔`. -/
theorem integral_ridgelet_mul_conj (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁)
    (hρ₂ : IsAdmissible α ρ₂) {f g : H → ℂ} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ)
    (hg : Integrable g μ) (hg₂ : MemLp g 2 μ) (hGf : MemLp (gaussFourier μ f) 2 ν)
    (hGg : MemLp (gaussFourier μ g) 2 ν) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ ν f g := by
  have hint :=
    integrable_cross_kernel μ hν hρ₁ hρ₂ hf hg hGf hGg
  unfold parameterMeasure
  rw [integral_prod _ ((memLp_ridgelet μ hν hρ₁ hf hf₂ hGf).integrable_mul_conj
    (memLp_ridgelet μ hν hρ₂ hg hg₂ hGg))]
  simp_rw [integral_ridgelet_slice_mul_conj μ ρ₁ ρ₂ hf hf₂ hg hg₂]
  rw [integral_const_mul, ← integral_prod _ hint,
    hν.integral_prod_neg_smul (K := fun ω => filterFourier ρ₁ ω * (starRingEnd ℂ)
      (filterFourier ρ₂ ω))
      (F := fun ξ => gaussFourier μ f ξ * (starRingEnd ℂ) (gaussFourier μ g ξ))
      ((continuous_gaussFourier μ hf).mul
        (Complex.continuous_conj.comp (continuous_gaussFourier μ hg))).measurable hint]
  unfold crossAdmissibilityConst spectralInner
  ring

end Product

/-! ### The coefficient operator: construction through the explicit formula -/

section Coefficient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {ν : Measure H} [SFinite ν] {α : ℝ} {ρ : SchwartzMap ℝ ℝ} {G : H → ℂ}

/-- The weight `w(ω) = |ω|^α (1 + ω²)⁻¹` used in the Cauchy–Schwarz argument. -/
theorem integrable_prod_ray_weight (hν : IsHomogeneous α ν) (hG : Measurable G)
    (hG₂ : MemLp G 2 ν) :
    Integrable (fun p : H × ℝ => ‖G (-(p.2 • p.1))‖ ^ 2 * (|p.2| ^ α * (1 + p.2 ^ 2)⁻¹))
      (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  have hw : Measurable fun ω : ℝ => |ω| ^ α * (1 + ω ^ 2)⁻¹ :=
    (continuous_abs.measurable.pow_const α).mul (by fun_prop)
  refine ⟨(((hG.comp hc.measurable).norm.pow_const 2).mul
    (hw.comp measurable_snd)).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  calc ∫⁻ p : H × ℝ, ‖‖G (-(p.2 • p.1))‖ ^ 2 * (|p.2| ^ α * (1 + p.2 ^ 2)⁻¹)‖ₑ ∂ν.prod volume
      = ∫⁻ p : H × ℝ, ENNReal.ofReal (|p.2| ^ α * (1 + p.2 ^ 2)⁻¹) * ‖G (-(p.2 • p.1))‖ₑ ^ 2
          ∂ν.prod volume := by
        refine lintegral_congr fun p => ?_
        rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, mul_comm]
    _ = (∫⁻ ω, ENNReal.ofReal (|ω| ^ α * (1 + ω ^ 2)⁻¹) * ENNReal.ofReal (|ω| ^ (-α))) *
          ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν :=
        hν.lintegral_prod_neg_smul (K := fun ω => ENNReal.ofReal (|ω| ^ α * (1 + ω ^ 2)⁻¹))
          hw.ennreal_ofReal (hG.enorm.pow_const 2)
    _ = (∫⁻ ω, ENNReal.ofReal ((1 + ω ^ 2)⁻¹)) * ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [h0] with ω hω
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_neg (abs_nonneg ω), mul_right_comm,
          mul_inv_cancel₀ (Real.rpow_pos_of_pos (abs_pos.mpr hω) α).ne', one_mul]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ (hG₂.lintegral_enorm_sq_lt_top)
        have h := integrable_inv_one_add_sq.hasFiniteIntegral
        rw [HasFiniteIntegral] at h
        refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) h
        rw [Real.enorm_eq_ofReal (by positivity)]

/-- For `G ∈ L²(ν)` and admissible `ρ`, the ray function `ω ↦ ρ̂(ω) G(-ωa)` is integrable for
`ν`-almost every direction `a`: a weighted Cauchy–Schwarz inequality against the weight
`|ω|^α (1 + ω²)⁻¹`. -/
theorem ae_integrable_ray (hα : 0 < α) (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∀ᵐ a ∂ν, Integrable fun ω : ℝ => filterFourier ρ ω * G (-(ω • a)) := by
  filter_upwards [(integrable_prod_ray_weight hν hG hG₂).prod_right_ae] with a ha
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  refine Integrable.mono' ((hρ.integrable_mul_one_add_sq hα).add ha) ?_ ?_
  · exact ((continuous_filterFourier ρ).measurable.mul
      (hG.comp (by fun_prop : Continuous fun ω : ℝ => -(ω • a)).measurable)).aestronglyMeasurable
  · filter_upwards [h0] with ω hω
    rw [norm_mul]
    have hw : 0 < |ω| ^ α * (1 + ω ^ 2)⁻¹ := by
      have := Real.rpow_pos_of_pos (abs_pos.mpr hω) α
      positivity
    have hinv : (|ω| ^ α * (1 + ω ^ 2)⁻¹)⁻¹ = |ω| ^ (-α) * (1 + ω ^ 2) := by
      rw [mul_inv, inv_inv, Real.rpow_neg (abs_nonneg ω)]
    have := Real.mul_le_sq_mul_inv_add_sq_mul (norm_nonneg (filterFourier ρ ω))
      (norm_nonneg (G (-(ω • a)))) hw
    rwa [hinv] at this

/-- For `G ∈ L²(ν)` and admissible `ρ`, the ray function `ω ↦ ρ̂(ω) G(-ωa)` is square
integrable for `ν`-almost every direction `a`. -/
theorem ae_memLp_ray (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ) (hG : Measurable G)
    (hG₂ : MemLp G 2 ν) :
    ∀ᵐ a ∂ν, MemLp (fun ω : ℝ => filterFourier ρ ω * G (-(ω • a))) 2 volume := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  have hmeas : Measurable fun p : H × ℝ =>
      ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 :=
    (((continuous_filterFourier ρ).comp continuous_snd).measurable.enorm.pow_const 2).mul
      ((hG.comp hc.measurable).enorm.pow_const 2)
  have hfin := hρ.lintegral_prod_enorm_sq_lt_top hν hG hG₂
  rw [lintegral_prod _ hmeas.aemeasurable] at hfin
  filter_upwards [ae_lt_top hmeas.lintegral_prod_right' hfin.ne] with a ha
  refine memLp_two_of_lintegral_enorm_sq_lt_top ((continuous_filterFourier ρ).measurable.mul
    (hG.comp (by fun_prop : Continuous fun ω : ℝ => -(ω • a)).measurable)).aestronglyMeasurable ?_
  simpa only [enorm_mul, mul_pow] using ha

/-- The explicit coefficient `γ_G` is strongly measurable on `H × ℝ`. -/
theorem stronglyMeasurable_coefficientFormula (ρ : SchwartzMap ℝ ℝ) (hG : Measurable G) :
    StronglyMeasurable (coefficientFormula ρ G) := by
  have hF : StronglyMeasurable fun q : (H × ℝ) × ℝ =>
      filterFourier ρ q.2 * G (-(q.2 • q.1.1)) * Complex.exp ((q.2 * q.1.2 : ℝ) * Complex.I) := by
    refine Measurable.stronglyMeasurable ?_
    refine (((continuous_filterFourier ρ).comp continuous_snd).measurable.mul
      (hG.comp (by fun_prop : Continuous fun q : (H × ℝ) × ℝ => -(q.2 • q.1.1)).measurable)).mul
      (by fun_prop : Continuous fun q : (H × ℝ) × ℝ =>
        Complex.exp ((q.2 * q.1.2 : ℝ) * Complex.I)).measurable
  exact stronglyMeasurable_const.mul hF.integral_prod_right'

omit [MeasurableSpace H] [BorelSpace H] in
/-- The explicit coefficient is a Fourier transform along each ray:
`γ_G(a, c) = 𝓕 (u ↦ ρ̂(2πu) G(-2πu a)) (-c)` (a formal change of variables). -/
theorem coefficientFormula_eq_fourier (ρ : SchwartzMap ℝ ℝ) (G : H → ℂ) (a : H) (c : ℝ) :
    coefficientFormula ρ G (a, c) =
      𝓕 (fun u : ℝ => filterFourier ρ (2 * Real.pi * u) * G (-((2 * Real.pi * u) • a))) (-c) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold coefficientFormula
  have h := Measure.integral_comp_mul_left (fun ω => filterFourier ρ ω * G (-(ω • a)) *
    Complex.exp ((ω * c : ℝ) * Complex.I)) (2 * Real.pi)
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  have : ((-2 * Real.pi * u * -c : ℝ) : ℂ) = ((2 * Real.pi * u * c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]
  ring

/-- Plancherel along a ray: `∫⁻ ‖γ_G(a,c)‖ₑ² dc = (2π)⁻¹ ∫⁻ ‖ρ̂(ω) G(-ωa)‖ₑ² dω`. -/
theorem lintegral_coefficientFormula_slice_sq (ρ : SchwartzMap ℝ ℝ) (hG : Measurable G) {a : H}
    (ha₁ : Integrable fun ω : ℝ => filterFourier ρ ω * G (-(ω • a)))
    (ha₂ : MemLp (fun ω : ℝ => filterFourier ρ ω * G (-(ω • a))) 2 volume) :
    ∫⁻ c, ‖coefficientFormula ρ G (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
  set Ψ : ℝ → ℂ := fun u => filterFourier ρ (2 * Real.pi * u) * G (-((2 * Real.pi * u) • a))
    with hΨ
  have hΦmeas : Measurable fun ω : ℝ => filterFourier ρ ω * G (-(ω • a)) :=
    (continuous_filterFourier ρ).measurable.mul
      (hG.comp (by fun_prop : Continuous fun ω : ℝ => -(ω • a)).measurable)
  have hΨ₁ : Integrable Ψ := ha₁.comp_mul_left' (by positivity)
  have hΨsq : ∫⁻ u, ‖Ψ u‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi)⁻¹ *
      ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
    have := lintegral_comp_mul_left_real
      (F := fun ω => ‖filterFourier ρ ω * G (-(ω • a))‖ₑ ^ 2) (hΦmeas.enorm.pow_const 2)
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [abs_of_pos (by positivity)] at this
    simp only [hΨ, enorm_mul, mul_pow] at this ⊢
    exact this
  have hΨ₂ : MemLp Ψ 2 volume := by
    refine memLp_two_of_lintegral_enorm_sq_lt_top hΨ₁.aestronglyMeasurable ?_
    rw [hΨsq]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have := ha₂.lintegral_enorm_sq_lt_top
    simpa only [enorm_mul, mul_pow] using this
  calc ∫⁻ c, ‖coefficientFormula ρ G (a, c)‖ₑ ^ 2
      = ∫⁻ c, ‖𝓕 Ψ (-c)‖ₑ ^ 2 := by
        refine lintegral_congr fun c => ?_
        rw [coefficientFormula_eq_fourier ρ G a c]
    _ = ∫⁻ c, ‖𝓕 Ψ c‖ₑ ^ 2 := lintegral_neg_eq_self (fun c => ‖𝓕 Ψ c‖ₑ ^ 2)
    _ = ∫⁻ u, ‖Ψ u‖ₑ ^ 2 := hΨ₁.lintegral_enorm_fourier_sq hΨ₂
    _ = _ := hΨsq

/-- The squared `L²(λ)` norm of the explicit coefficient:
`∫⁻ ‖γ_G‖ₑ² dλ = C_ρ ∫⁻ ‖G‖ₑ² dν`. -/
theorem lintegral_coefficientFormula_sq (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∫⁻ p, ‖coefficientFormula ρ G p‖ₑ ^ 2 ∂parameterMeasure ν =
      ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  have hmeas : Measurable fun p : H × ℝ => ‖coefficientFormula ρ G p‖ₑ ^ 2 :=
    (stronglyMeasurable_coefficientFormula ρ hG).measurable.enorm.pow_const 2
  have hmeas' : Measurable fun p : H × ℝ =>
      ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 :=
    (((continuous_filterFourier ρ).comp continuous_snd).measurable.enorm.pow_const 2).mul
      ((hG.comp hc.measurable).enorm.pow_const 2)
  unfold parameterMeasure
  rw [lintegral_prod _ hmeas.aemeasurable]
  have key : ∀ᵐ a ∂ν, ∫⁻ c, ‖coefficientFormula ρ G (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
    filter_upwards [ae_integrable_ray hα hν hρ hG hG₂, ae_memLp_ray hν hρ hG hG₂] with a ha₁ ha₂
    exact lintegral_coefficientFormula_slice_sq ρ hG ha₁ ha₂
  rw [lintegral_congr_ae key, lintegral_const_mul _ hmeas'.lintegral_prod_right',
    ← lintegral_prod _ hmeas'.aemeasurable, hρ.lintegral_prod_enorm_sq hν hG, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel_left₀ (by positivity)]

/-- The explicit coefficient `γ_G` is square integrable on `H × ℝ`. -/
theorem memLp_coefficientFormula (hα : 0 < α) (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    MemLp (coefficientFormula ρ G) 2 (parameterMeasure ν) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top
    (stronglyMeasurable_coefficientFormula ρ hG).aestronglyMeasurable ?_
  rw [lintegral_coefficientFormula_sq hα hν hρ hG hG₂]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hG₂.lintegral_enorm_sq_lt_top)

/-- The scaled isometry `‖γ_G‖²_{L²(λ)} = C_ρ ‖G‖²_{L²(ν)}`. -/
theorem integral_coefficientFormula_norm_sq (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖coefficientFormula ρ G p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν := by
  rw [integral_norm_sq_eq_toReal_lintegral
      (stronglyMeasurable_coefficientFormula ρ hG).aestronglyMeasurable,
    integral_norm_sq_eq_toReal_lintegral hG.aestronglyMeasurable,
    lintegral_coefficientFormula_sq hα hν hρ hG hG₂, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.pos.le]

/-- The conjugate of a Schwartz function is integrable. -/
theorem integrable_conj_schwartz (φ : SchwartzMap ℝ ℂ) :
    Integrable fun c : ℝ => (starRingEnd ℂ) (φ c) :=
  φ.integrable.norm.mono' (Complex.continuous_conj.comp φ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun c => by rw [Complex.norm_conj])

/-- The explicit coefficient `γ_G` has the partial Fourier transform `ρ̂(ω) G(-ωa)` in the
bias, in the sense of `HasBiasFourier` (Parseval against Schwartz test functions, by Fubini). -/
theorem hasBiasFourier_coefficientFormula (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    HasBiasFourier ν (coefficientFormula ρ G)
      (fun a ω => filterFourier ρ ω * G (-(ω • a))) := by
  refine ⟨ae_memLp_ray hν hρ hG hG₂, ?_⟩
  filter_upwards [ae_integrable_ray hα hν hρ hG hG₂] with a ha φ
  set Φ : ℝ → ℂ := fun ω => filterFourier ρ ω * G (-(ω • a)) with hΦ
  have hint : Integrable (fun z : ℝ × ℝ =>
      (starRingEnd ℂ) (φ z.1) * Φ z.2 * Complex.exp ((z.2 * z.1 : ℝ) * Complex.I))
      (volume.prod volume) := by
    refine ((integrable_conj_schwartz φ).mul_prod ha).mul_unimodular ?_
      (Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ =>
        Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)).aestronglyMeasurable
    · exact (Complex.norm_exp_ofReal_mul_I _).le
  have hL : ∀ c : ℝ, coefficientFormula ρ G (a, c) * (starRingEnd ℂ) (φ c) =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ ω, (starRingEnd ℂ) (φ c) * Φ ω * Complex.exp ((ω * c : ℝ) * Complex.I) := by
    intro c
    unfold coefficientFormula
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hΦ]
    ring
  simp_rw [hL]
  rw [integral_const_mul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hconj : ∀ c : ℝ, (starRingEnd ℂ) (φ c) * Φ ω * Complex.exp ((ω * c : ℝ) * Complex.I) =
      Φ ω * (starRingEnd ℂ) (Complex.exp (-Complex.I * ((inner ℝ c ω : ℝ) : ℂ)) * φ c) := by
    intro c
    rw [map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    simp only [RCLike.inner_apply, conj_trivial]
    have : (Complex.exp ((ω * c : ℝ) * Complex.I)) =
        Complex.exp (-(-Complex.I) * ((c * ω : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [this]
    ring_nf
  simp_rw [hconj]
  rw [integral_const_mul, integral_conj]
  rfl

end Coefficient

/-! ### Uniqueness of the partial Fourier transform in the bias -/

section Uniqueness

variable {H : Type*} [MeasurableSpace H]

/-- The bias sections of a square-integrable function on `H × ℝ` are square integrable for
almost every direction. -/
theorem ae_memLp_slice {ν : Measure H} [SFinite ν] {γ : H × ℝ → ℂ}
    (h : MemLp γ 2 (ν.prod volume)) :
    ∀ᵐ a ∂ν, MemLp (fun c : ℝ => γ (a, c)) 2 volume := by
  filter_upwards [h.integrable_norm_sq.prod_right_ae, h.aestronglyMeasurable.prodMk_left]
    with a ha hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ha

/-- `HasBiasFourier` only depends on the `λ`-class of `γ`. -/
theorem HasBiasFourier.congr_left {ν : Measure H} [SFinite ν] {γ γ' : H × ℝ → ℂ}
    {Φ : H → ℝ → ℂ} (h : HasBiasFourier ν γ Φ) (hγ : γ =ᵐ[ν.prod volume] γ') :
    HasBiasFourier ν γ' Φ := by
  refine ⟨h.memLp, ?_⟩
  filter_upwards [h.parseval, Measure.ae_ae_of_ae_prod hγ] with a ha hae φ
  rw [← ha φ]
  apply integral_congr_ae
  filter_upwards [hae] with c hc
  rw [hc]

/-- `HasBiasFourier` only depends on the almost-everywhere classes of the ray functions
`Φ a`. -/
theorem HasBiasFourier.congr_right {ν : Measure H} {γ : H × ℝ → ℂ} {Φ Φ' : H → ℝ → ℂ}
    (h : HasBiasFourier ν γ Φ) (hΦ : ∀ᵐ a ∂ν, Φ a =ᵐ[volume] Φ' a) :
    HasBiasFourier ν γ Φ' := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.memLp, hΦ] with a ha hae
    exact ha.ae_eq hae
  filter_upwards [h.parseval, hΦ] with a ha hae φ
  rw [ha φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hae] with ω hω
  rw [hω]

/-- **Uniqueness**: two square-integrable functions on `H × ℝ` with the same partial Fourier
transform in the bias agree `λ`-almost everywhere. -/
theorem HasBiasFourier.ae_eq {ν : Measure H} [SFinite ν] {γ₁ γ₂ : H × ℝ → ℂ}
    (h₁ : MemLp γ₁ 2 (ν.prod volume)) (h₂ : MemLp γ₂ 2 (ν.prod volume)) {Φ : H → ℝ → ℂ}
    (hΦ₁ : HasBiasFourier ν γ₁ Φ) (hΦ₂ : HasBiasFourier ν γ₂ Φ) :
    γ₁ =ᵐ[ν.prod volume] γ₂ := by
  have key : ∀ᵐ a ∂ν, ∀ᵐ c : ℝ ∂volume, γ₁ (a, c) = γ₂ (a, c) := by
    filter_upwards [hΦ₁.parseval, hΦ₂.parseval, ae_memLp_slice h₁, ae_memLp_slice h₂]
      with a ha₁ ha₂ hm₁ hm₂
    have hloc : LocallyIntegrable (fun c : ℝ => γ₁ (a, c) - γ₂ (a, c)) volume :=
      (hm₁.sub hm₂).locallyIntegrable one_le_two
    have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g g_diff g_supp => ?_
    · filter_upwards [h0] with c hc
      exact sub_eq_zero.mp hc
    · have hr₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_supp.comp_left rfl
      have hr₂ := Complex.ofRealCLM.contDiff.comp g_diff
      set φ : SchwartzMap ℝ ℂ := hr₁.toSchwartzMap hr₂ with hφ
      have hval : ∀ c : ℝ, g c • (γ₁ (a, c) - γ₂ (a, c)) =
          γ₁ (a, c) * (starRingEnd ℂ) (φ c) - γ₂ (a, c) * (starRingEnd ℂ) (φ c) := by
        intro c
        change g c • (γ₁ (a, c) - γ₂ (a, c)) =
          γ₁ (a, c) * (starRingEnd ℂ) ((g c : ℂ)) - γ₂ (a, c) * (starRingEnd ℂ) ((g c : ℂ))
        rw [Complex.conj_ofReal, Complex.real_smul]
        ring
      simp_rw [hval]
      rw [integral_sub (hm₁.integrable_mul_conj (φ.memLp 2)) (hm₂.integrable_mul_conj (φ.memLp 2)),
        ha₁ φ, ha₂ φ, sub_self]
  set γ₁' := h₁.1.mk γ₁ with hγ₁'
  set γ₂' := h₂.1.mk γ₂ with hγ₂'
  have e₁ : γ₁ =ᵐ[ν.prod volume] γ₁' := h₁.1.ae_eq_mk
  have e₂ : γ₂ =ᵐ[ν.prod volume] γ₂' := h₂.1.ae_eq_mk
  have key' : ∀ᵐ a ∂ν, ∀ᵐ c : ℝ ∂volume, γ₁' (a, c) = γ₂' (a, c) := by
    filter_upwards [key, Measure.ae_ae_of_ae_prod e₁, Measure.ae_ae_of_ae_prod e₂]
      with a ha ha₁ ha₂
    filter_upwards [ha, ha₁, ha₂] with c hc hc₁ hc₂
    rw [← hc₁, ← hc₂, hc]
  have hprod : ∀ᵐ z ∂ν.prod volume, γ₁' z = γ₂' z :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun h₁.1.stronglyMeasurable_mk.measurable
      h₂.1.stronglyMeasurable_mk.measurable)).mpr key'
  filter_upwards [hprod, e₁, e₂] with z hz hz₁ hz₂
  rw [hz₁, hz₂, hz]

end Uniqueness

/-! ### The real form of the Plancherel identity -/

section NormIdentity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- `C^{(α)}_{ρ,ρ} = C^{(α)}_ρ`. -/
theorem crossAdmissibilityConst_self (α : ℝ) (ρ : ℝ → ℝ) :
    crossAdmissibilityConst α ρ ρ = (admissibilityConst α ρ : ℂ) := by
  unfold crossAdmissibilityConst admissibilityConst
  push_cast
  congr 1
  have h := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ))
    (f := fun ω => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α))
  refine Eq.trans ?_ h
  congr 1
  funext ω
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `‖R_ρ f‖²_{L²(λ)} = C^{(α)}_ρ ∫ ‖𝒢_μ f‖² dν`. -/
theorem integral_ridgelet_norm_sq (μ : Measure H) [IsProbabilityMeasure μ] {ν : Measure H}
    [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
    {f : H → ℂ} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (hG : MemLp (gaussFourier μ f) 2 ν) :
    ∫ p, ‖ridgelet μ ρ f p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖gaussFourier μ f ξ‖ ^ 2 ∂ν := by
  have h := integral_ridgelet_mul_conj μ hν hρ hρ hf hf₂ hf hf₂ hG hG
  rw [integral_mul_conj_self, crossAdmissibilityConst_self, spectralInner, integral_mul_conj_self,
    ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

end NormIdentity

/-! ### The bounded extension of the ridgelet transform to `𝒦` -/

section Embedding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

variable (μ ν : Measure H) [IsFiniteMeasure μ]

/-- `𝒢_μ : 𝒟 → 𝒦` as a linear map. -/
def spectralEmbedₗ : spectralCore μ ν →ₗ[ℂ] spectralRange μ ν where
  toFun := spectralEmbed μ ν
  map_add' f g := Subtype.ext (gaussFourierLp_add μ ν f g)
  map_smul' c f := Subtype.ext (gaussFourierLp_smul μ ν c f)

/-- `spectralEmbedₗ` acts as `spectralEmbed`. -/
@[simp]
theorem spectralEmbedₗ_apply (f : spectralCore μ ν) :
    spectralEmbedₗ μ ν f = spectralEmbed μ ν f := rfl

/-- The image of the core `𝒟` under `𝒢_μ` is dense in `𝒦`. -/
theorem denseRange_spectralEmbedₗ : DenseRange (spectralEmbedₗ μ ν) := by
  have key : (spectralRange μ ν : Set (Lp ℂ 2 ν)) ⊆ closure (Set.range (gaussFourierLp μ ν)) := by
    rw [← coe_gaussFourierRange, spectralRange_eq_topologicalClosure,
      Submodule.topologicalClosure_coe]
  unfold DenseRange
  rw [Subtype.dense_iff]
  convert key using 2
  ext g
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨spectralEmbedₗ μ ν f, ⟨f, rfl⟩, rfl⟩

variable {μ}

omit [IsFiniteMeasure μ] in
/-- The integrand of the ridgelet transform is integrable at every parameter. -/
theorem integrable_ridgelet_integrand (ρ : SchwartzMap ℝ ℝ) {f : H → ℂ} (hf : Integrable f μ)
    (p : H × ℝ) : Integrable (fun x => f x * (ρ (⟪p.1, x⟫ + p.2) : ℂ)) μ := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  refine hf.mul_bdd (c := C) (Complex.continuous_ofReal.comp (ρ.continuous.comp
    (by fun_prop : Continuous fun x : H => ⟪p.1, x⟫ + p.2))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_real]
  exact hC.2 _

/-- `R_ρ` is additive on `L²(μ)` classes. -/
theorem ridgelet_coe_add (ρ : SchwartzMap ℝ ℝ) (f g : Lp ℂ 2 μ) :
    ridgelet μ ρ ((f + g : Lp ℂ 2 μ) : H → ℂ) = ridgelet μ ρ f + ridgelet μ ρ g := by
  funext p
  simp only [ridgelet, Pi.add_apply]
  rw [← integral_add (integrable_ridgelet_integrand ρ ((Lp.memLp f).integrable one_le_two) p)
    (integrable_ridgelet_integrand ρ ((Lp.memLp g).integrable one_le_two) p)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx, Pi.add_apply, add_mul]

omit [OpensMeasurableSpace H] [IsFiniteMeasure μ] in
/-- `R_ρ` is homogeneous on `L²(μ)` classes. -/
theorem ridgelet_coe_smul (ρ : SchwartzMap ℝ ℝ) (c : ℂ) (f : Lp ℂ 2 μ) :
    ridgelet μ ρ ((c • f : Lp ℂ 2 μ) : H → ℂ) = c • ridgelet μ ρ f := by
  funext p
  simp only [ridgelet, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]

end Embedding

section Extension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SFinite ν]

variable {α : ℝ} (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hν hρ

/-- `R_ρ : 𝒟 → L²(λ)` as a linear map, for an `α`-admissible filter `ρ`. -/
def ridgeletCoreₗ : spectralCore μ ν →ₗ[ℂ] Lp ℂ 2 (parameterMeasure ν) where
  toFun f := (memLp_ridgelet μ hν hρ ((Lp.memLp (f : Lp ℂ 2 μ)).integrable one_le_two)
    (Lp.memLp _) f.2).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
    show ridgelet μ ρ (((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ) : Lp ℂ 2 μ) : H → ℂ) p = _
    rw [ridgelet_coe_add]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
    show ridgelet μ ρ ((c • (f : Lp ℂ 2 μ) : Lp ℂ 2 μ) : H → ℂ) p = _
    rw [ridgelet_coe_smul]
    rfl

/-- `ridgeletCoreₗ f` is the `L²(λ)` class of `R_ρ f`. -/
theorem ridgeletCoreₗ_apply (f : spectralCore μ ν) :
    ridgeletCoreₗ hν hρ f = MemLp.toLp (ridgelet μ ρ f) (memLp_ridgelet μ hν hρ
      ((Lp.memLp (f : Lp ℂ 2 μ)).integrable one_le_two) (Lp.memLp _) f.2) := rfl

/-- `ridgeletCoreₗ f` agrees `λ`-almost everywhere with `R_ρ f`. -/
theorem coeFn_ridgeletCoreₗ (f : spectralCore μ ν) :
    (ridgeletCoreₗ hν hρ f : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f := by
  rw [ridgeletCoreₗ_apply]
  exact MemLp.coeFn_toLp _

/-- The scaled isometry on the core: `‖R_ρ f‖² = C^{(α)}_ρ ‖𝒢_μ f‖²`. -/
theorem norm_ridgeletCoreₗ_sq (f : spectralCore μ ν) :
    ‖ridgeletCoreₗ hν hρ f‖ ^ 2 = admissibilityConst α ρ * ‖spectralEmbedₗ μ ν f‖ ^ 2 := by
  rw [ridgeletCoreₗ_apply, MemLp.norm_toLp_two_sq]
  show _ = admissibilityConst α ρ * ‖gaussFourierLp μ ν f‖ ^ 2
  rw [gaussFourierLp, MemLp.norm_toLp_two_sq]
  exact integral_ridgelet_norm_sq μ hν hρ ((Lp.memLp (f : Lp ℂ 2 μ)).integrable one_le_two)
    (Lp.memLp _) f.2

/-- The norm bound `‖R_ρ f‖ ≤ √C_ρ ‖𝒢_μ f‖` on the core, in the form used for the extension. -/
theorem norm_ridgeletCoreₗ_le (f : spectralCore μ ν) :
    ‖ridgeletCoreₗ hν hρ f‖ ≤ Real.sqrt (admissibilityConst α ρ) * ‖spectralEmbedₗ μ ν f‖ := by
  refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_)
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_ridgeletCoreₗ_sq]

/-- The bounded extension `R_ρ : 𝒦 → L²(λ)` of the ridgelet transform from the dense image of
the core. -/
def ridgeletExtensionCLM : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν) :=
  (ridgeletCoreₗ hν hρ).extendOfNorm (spectralEmbedₗ μ ν)

/-- The extension restricts to `ridgeletCoreₗ` on the image of the core. -/
theorem ridgeletExtensionCLM_embed (f : spectralCore μ ν) :
    ridgeletExtensionCLM hν hρ (spectralEmbed μ ν f) = ridgeletCoreₗ hν hρ f :=
  LinearMap.extendOfNorm_eq (denseRange_spectralEmbedₗ μ ν) ⟨_, norm_ridgeletCoreₗ_le hν hρ⟩ f

/-- The extension agrees `λ`-almost everywhere with `R_ρ f` on the image of the core. -/
theorem coeFn_ridgeletExtensionCLM_embed (f : spectralCore μ ν) :
    (ridgeletExtensionCLM hν hρ (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν]
      ridgelet μ ρ f := by
  rw [ridgeletExtensionCLM_embed]
  exact coeFn_ridgeletCoreₗ hν hρ f

/-- Any bounded operator on `𝒦` restricting to `R_ρ` on the core is the extension. -/
theorem eq_ridgeletExtensionCLM (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    R = ridgeletExtensionCLM hν hρ := by
  symm
  refine LinearMap.extendOfNorm_unique (denseRange_spectralEmbedₗ μ ν) _
    (norm_ridgeletCoreₗ_le hν hρ) R ?_
  ext f
  exact (hR f).trans (coeFn_ridgeletCoreₗ hν hρ f).symm

/-- Existence and uniqueness of the bounded extension of `R_ρ` to `𝒦`. -/
theorem existsUnique_ridgeletExtensionCLM :
    ∃! R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f :=
  ⟨ridgeletExtensionCLM hν hρ, coeFn_ridgeletExtensionCLM_embed hν hρ,
    fun R hR => eq_ridgeletExtensionCLM hν hρ R hR⟩

/-- The extension is a scaled isometry: `‖R_ρ G‖² = C^{(α)}_ρ ‖G‖²` on `𝒦`. -/
theorem norm_ridgeletExtensionCLM_sq (G : spectralRange μ ν) :
    ‖ridgeletExtensionCLM hν hρ G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  refine (denseRange_spectralEmbedₗ μ ν).induction_on G ?_ fun f => ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rw [spectralEmbedₗ_apply, ridgeletExtensionCLM_embed, norm_ridgeletCoreₗ_sq,
      spectralEmbedₗ_apply]

/-- `‖R_ρ G‖ = √C_ρ ‖G‖` on `𝒦`. -/
theorem norm_ridgeletExtensionCLM (G : spectralRange μ ν) :
    ‖ridgeletExtensionCLM hν hρ G‖ = Real.sqrt (admissibilityConst α ρ) * ‖G‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_ridgeletExtensionCLM_sq]

/-- The extension has closed range (an isometry up to a nonzero scalar). -/
theorem isClosed_range_ridgeletExtensionCLM :
    IsClosed (Set.range (ridgeletExtensionCLM (μ := μ) hν hρ)) := by
  have hC : 0 < Real.sqrt (admissibilityConst α ρ) := Real.sqrt_pos.mpr hρ.pos
  haveI : CompleteSpace (spectralRange μ ν) := Submodule.topologicalClosure.completeSpace _
  refine AntilipschitzWith.isClosed_range
    (K := (Real.sqrt (admissibilityConst α ρ))⁻¹.toNNReal) ?_
    (ridgeletExtensionCLM hν hρ).uniformContinuous
  refine (ridgeletExtensionCLM hν hρ).antilipschitz_of_bound fun G => ?_
  rw [norm_ridgeletExtensionCLM hν hρ, Real.coe_toNNReal _ (by positivity), ← mul_assoc,
    inv_mul_cancel₀ hC.ne', one_mul]

end Extension

/-! ### The coefficient operator on `L²(ν)` classes and the factorization `R_ρ = W_ρ U` -/

section Factorization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {ν : Measure H} [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν)
include hν

/-- `W_ρ G` depends only on the `ν`-class of `G`. -/
theorem spectralCoefficient_congr_ae (ρ : ℝ → ℝ) {G G' : H → ℂ} (hGG' : G =ᵐ[ν] G') :
    spectralCoefficient ν ρ G = spectralCoefficient ν ρ G' := by
  have hae := hν.ae_ae_eq_neg_smul' hGG'
  have hΦ : ∀ᵐ a ∂ν, (fun ω => filterFourier ρ ω * G (-(ω • a))) =ᵐ[volume]
      fun ω => filterFourier ρ ω * G' (-(ω • a)) := by
    filter_upwards [hae] with a ha
    filter_upwards [ha] with ω hω
    simp only [hω]
  have hΦ' : ∀ᵐ a ∂ν, (fun ω => filterFourier ρ ω * G' (-(ω • a))) =ᵐ[volume]
      fun ω => filterFourier ρ ω * G (-(ω • a)) := by
    filter_upwards [hΦ] with a ha
    exact ha.symm
  have key : ∀ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) ↔
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) :=
    fun γ => ⟨fun h => h.congr_right hΦ, fun h => h.congr_right hΦ'⟩
  unfold spectralCoefficient
  by_cases h : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a)))
  · have h' : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) :=
      h.imp fun γ => (key γ).mp
    rw [dif_pos h, dif_pos h']
    exact Exists.choose_congr (funext fun γ => propext (key γ)) h h'
  · have h' : ¬ ∃ γ : Lp ℂ 2 (parameterMeasure ν),
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) :=
      fun h' => h (h'.imp fun γ => (key γ).mpr)
    rw [dif_neg h, dif_neg h']

variable (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hα hρ

/-- Existence and uniqueness of `W_ρ G` for measurable `G ∈ L²(ν)`. -/
theorem existsUnique_hasBiasFourier {G : H → ℂ} (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∃! γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) := by
  have hB := (hasBiasFourier_coefficientFormula hα hν hρ hG hG₂).congr_left
    (memLp_coefficientFormula hα hν hρ hG hG₂).coeFn_toLp.symm
  exact ⟨_, hB, fun γ hγ => Lp.ext (HasBiasFourier.ae_eq (Lp.memLp γ) (Lp.memLp _) hγ hB)⟩

/-- For measurable `G ∈ L²(ν)`, `W_ρ G` is the class of the explicit coefficient `γ_G`. -/
theorem spectralCoefficient_eq_toLp {G : H → ℂ} (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    spectralCoefficient ν ρ G = (memLp_coefficientFormula hα hν hρ hG hG₂).toLp _ := by
  have hB := (hasBiasFourier_coefficientFormula hα hν hρ hG hG₂).congr_left
    (memLp_coefficientFormula hα hν hρ hG hG₂).coeFn_toLp.symm
  have hex : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) := ⟨_, hB⟩
  unfold spectralCoefficient
  rw [dif_pos hex]
  exact Lp.ext (HasBiasFourier.ae_eq (Lp.memLp _) (Lp.memLp _) hex.choose_spec hB)

/-- The scaled isometry `‖W_ρ G‖² = C^{(α)}_ρ ‖G‖²` for measurable `G ∈ L²(ν)`. -/
theorem integral_spectralCoefficient_norm_sq {G : H → ℂ} (hG : Measurable G)
    (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖(spectralCoefficient ν ρ G : H × ℝ → ℂ) p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν := by
  rw [spectralCoefficient_eq_toLp hν hα hρ hG hG₂,
    ← integral_coefficientFormula_norm_sq hα hν hρ hG hG₂]
  apply integral_congr_ae
  filter_upwards [(memLp_coefficientFormula hα hν hρ hG hG₂).coeFn_toLp] with p hp
  rw [hp]

/-- The explicit coefficient is linear in `G`, `λ`-almost everywhere. -/
theorem coefficientFormula_sub_ae {G₁ G₂ : H → ℂ} (hG₁ : Measurable G₁) (hG₁₂ : MemLp G₁ 2 ν)
    (hG₂ : Measurable G₂) (hG₂₂ : MemLp G₂ 2 ν) :
    coefficientFormula ρ (G₁ - G₂) =ᵐ[parameterMeasure ν]
      coefficientFormula ρ G₁ - coefficientFormula ρ G₂ := by
  have hray := (ae_integrable_ray hα hν hρ hG₁ hG₁₂).and (ae_integrable_ray hα hν hρ hG₂ hG₂₂)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hray] with p hp
  obtain ⟨h₁, h₂⟩ := hp
  have hmul : ∀ (Φ : ℝ → ℂ), Integrable Φ → Integrable fun ω : ℝ =>
      Φ ω * Complex.exp ((ω * p.2 : ℝ) * Complex.I) := fun Φ hΦ =>
    hΦ.mul_unimodular (by fun_prop : Continuous fun ω : ℝ =>
      Complex.exp ((ω * p.2 : ℝ) * Complex.I)).aestronglyMeasurable
      (Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le)
  simp only [coefficientFormula, Pi.sub_apply]
  rw [← mul_sub, ← integral_sub (hmul _ h₁) (hmul _ h₂)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only []
  ring

/-- `W_ρ` on `L²(ν)` classes is additive. -/
theorem spectralCoefficient_coeFn_sub (u v : Lp ℂ 2 ν) :
    spectralCoefficient ν ρ ((u - v : Lp ℂ 2 ν) : H → ℂ) =
      spectralCoefficient ν ρ u - spectralCoefficient ν ρ v := by
  set u' := (Lp.aestronglyMeasurable u).mk u with hu'
  set v' := (Lp.aestronglyMeasurable v).mk v with hv'
  have hum : Measurable u' := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable
  have hvm : Measurable v' := (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
  have hue : (u : H → ℂ) =ᵐ[ν] u' := (Lp.aestronglyMeasurable u).ae_eq_mk
  have hve : (v : H → ℂ) =ᵐ[ν] v' := (Lp.aestronglyMeasurable v).ae_eq_mk
  have hu₂ : MemLp u' 2 ν := (Lp.memLp u).ae_eq hue
  have hv₂ : MemLp v' 2 ν := (Lp.memLp v).ae_eq hve
  have hsub : ((u - v : Lp ℂ 2 ν) : H → ℂ) =ᵐ[ν] u' - v' := by
    filter_upwards [Lp.coeFn_sub u v, hue, hve] with x hx hx₁ hx₂
    rw [hx, Pi.sub_apply, Pi.sub_apply, hx₁, hx₂]
  rw [spectralCoefficient_congr_ae hν ρ hsub, spectralCoefficient_congr_ae hν ρ hue,
    spectralCoefficient_congr_ae hν ρ hve, spectralCoefficient_eq_toLp hν hα hρ (hum.sub hvm)
    (hu₂.sub hv₂), spectralCoefficient_eq_toLp hν hα hρ hum hu₂,
    spectralCoefficient_eq_toLp hν hα hρ hvm hv₂, ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (coefficientFormula_sub_ae hν hα hρ hum hu₂ hvm hv₂)

/-- `‖W_ρ u‖² = C^{(α)}_ρ ‖u‖²` on `L²(ν)` classes. -/
theorem norm_spectralCoefficient_coeFn_sq (u : Lp ℂ 2 ν) :
    ‖spectralCoefficient ν ρ u‖ ^ 2 = admissibilityConst α ρ * ‖u‖ ^ 2 := by
  set u' := (Lp.aestronglyMeasurable u).mk u with hu'
  have hum : Measurable u' := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable
  have hue : (u : H → ℂ) =ᵐ[ν] u' := (Lp.aestronglyMeasurable u).ae_eq_mk
  have hu₂ : MemLp u' 2 ν := (Lp.memLp u).ae_eq hue
  rw [spectralCoefficient_congr_ae hν ρ hue, spectralCoefficient_eq_toLp hν hα hρ hum hu₂,
    MemLp.norm_toLp_two_sq, integral_coefficientFormula_norm_sq hα hν hρ hum hu₂,
    Lp.norm_sq_eq_integral_norm_sq]
  congr 1
  apply integral_congr_ae
  filter_upwards [hue] with x hx
  rw [hx]

/-- `W_ρ` is Lipschitz on `L²(ν)` classes. -/
theorem lipschitzWith_spectralCoefficient :
    LipschitzWith (Real.sqrt (admissibilityConst α ρ)).toNNReal
      fun u : Lp ℂ 2 ν => spectralCoefficient ν ρ u := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [dist_eq_norm, dist_eq_norm, ← spectralCoefficient_coeFn_sub hν hα hρ,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_)
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_spectralCoefficient_coeFn_sq hν hα hρ]

/-- The factorization `R_ρ = W_ρ ∘ U`: on `𝒦` the extension of the ridgelet transform is the
coefficient operator. -/
theorem ridgeletExtensionCLM_eq_spectralCoefficient (μ : Measure H) [IsProbabilityMeasure μ]
    (G : spectralRange μ ν) :
    ridgeletExtensionCLM hν hρ G = spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ) := by
  refine (denseRange_spectralEmbedₗ μ ν).induction_on G ?_ fun f => ?_
  · exact isClosed_eq (ridgeletExtensionCLM hν hρ).continuous
      ((lipschitzWith_spectralCoefficient hν hα hρ).continuous.comp continuous_subtype_val)
  · have hf : Integrable ((f : Lp ℂ 2 μ) : H → ℂ) μ := (Lp.memLp _).integrable one_le_two
    have hcoe : ((spectralEmbed μ ν f : Lp ℂ 2 ν) : H → ℂ) =ᵐ[ν] gaussFourier μ f :=
      MemLp.coeFn_toLp f.2
    rw [spectralEmbedₗ_apply, ridgeletExtensionCLM_embed, spectralCoefficient_congr_ae hν ρ hcoe,
      spectralCoefficient_eq_toLp hν hα hρ (continuous_gaussFourier μ hf).measurable f.2,
      ridgeletCoreₗ_apply]
    refine MemLp.toLp_congr _ _ ?_
    exact HasBiasFourier.ae_eq (memLp_ridgelet μ hν hρ hf (Lp.memLp _) f.2)
      (memLp_coefficientFormula hα hν hρ (continuous_gaussFourier μ hf).measurable f.2)
      (hasBiasFourier_ridgelet μ ρ ν hf (Lp.memLp _))
      (hasBiasFourier_coefficientFormula hα hν hρ (continuous_gaussFourier μ hf).measurable f.2)

end Factorization

/-! ### Injectivity -/

section Injectivity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Fourier uniqueness: `𝒢_μ f = 0` forces `f = 0` `μ`-almost everywhere. -/
theorem ae_eq_zero_of_gaussFourier_eq_zero (μ : Measure H) [IsFiniteMeasure μ] {f : H → ℂ}
    (hf : Integrable f μ) (h : ∀ ξ, gaussFourier μ f ξ = 0) : f =ᵐ[μ] 0 := by
  refine hf.ae_eq_zero_of_forall_integral_mul_exp_eq_zero fun t => ?_
  rw [← h (-t)]
  unfold gaussFourier character
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_neg_right]
  congr 2
  push_cast
  ring

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- An admissible filter has a nonzero frequency at which `ρ̂` does not vanish. -/
theorem IsAdmissible.exists_ne_zero_filterFourier_ne_zero {α : ℝ} (hα : 0 < α)
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) :
    ∃ ω : ℝ, ω ≠ 0 ∧ filterFourier ρ ω ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : (fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)) = 0 := by
    funext ω
    by_cases hω : ω = 0
    · subst hω
      simp [Real.zero_rpow (neg_ne_zero.mpr hα.ne')]
    · simp [hcon ω hω]
  have h := hρ.pos
  unfold admissibilityConst at h
  rw [hzero] at h
  simp at h

/-- **Injectivity**: if `R_ρ f = 0` `λ`-almost everywhere for `f ∈ L¹(μ)`, then `f = 0`
`μ`-almost everywhere. -/
theorem ae_eq_zero_of_ridgelet_ae_eq_zero (μ : Measure H) [IsProbabilityMeasure μ]
    {ν : Measure H} [SFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {f : H → ℂ}
    (hf : Integrable f μ) (h : ridgelet μ ρ f =ᵐ[parameterMeasure ν] 0) : f =ᵐ[μ] 0 := by
  obtain ⟨ω₀, hω₀, hρω₀⟩ := hρ.exists_ne_zero_filterFourier_ne_zero hα
  have hslice : ∀ᵐ a ∂ν, gaussFourier μ f ((-ω₀) • a) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with a ha
    have hb : biasFourier (ridgelet μ ρ f) a ω₀ = 0 := by
      unfold biasFourier
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ha] with c hc
      simp only [hc, Pi.zero_apply, zero_mul]
    rw [biasFourier_ridgelet μ ρ hf, mul_eq_zero] at hb
    rw [neg_smul]
    exact hb.resolve_left hρω₀
  have hs : MeasurableSet {ξ : H | gaussFourier μ f ξ = 0} :=
    (isClosed_singleton.preimage (continuous_gaussFourier μ hf)).measurableSet
  have hmap : ∀ᵐ ξ ∂(ν.map fun a => (-ω₀) • a), gaussFourier μ f ξ = 0 :=
    (ae_map_iff (measurable_const_smul (-ω₀)).aemeasurable hs).mpr hslice
  rw [hν (-ω₀) (neg_ne_zero.mpr hω₀)] at hmap
  have hc : ENNReal.ofReal (|(-ω₀)| ^ (-α)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr (neg_ne_zero.mpr hω₀)) _)).ne'
  have hmap' : ∀ᵐ ξ ∂ν, gaussFourier μ f ξ = 0 := by
    rw [ae_iff] at hmap ⊢
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hmap
    exact hmap.resolve_left hc
  have hzero : gaussFourier μ f = 0 :=
    ((continuous_gaussFourier μ hf).ae_eq_iff_eq ν continuous_const).mp hmap'
  exact ae_eq_zero_of_gaussFourier_eq_zero μ hf fun ξ => congrFun hzero ξ

/-- Positivity of the spectral form: `∫ ‖𝒢_μ f‖² dν = 0` forces `f = 0` `μ`-almost
everywhere. -/
theorem ae_eq_zero_of_integral_norm_gaussFourier_sq_eq_zero (μ : Measure H)
    [IsFiniteMeasure μ] {ν : Measure H} [ν.IsOpenPosMeasure] {f : H → ℂ} (hf : Integrable f μ)
    (hG : MemLp (gaussFourier μ f) 2 ν) (h : ∫ ξ, ‖gaussFourier μ f ξ‖ ^ 2 ∂ν = 0) :
    f =ᵐ[μ] 0 := by
  have hae : (fun ξ => ‖gaussFourier μ f ξ‖ ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ξ => by positivity) hG.integrable_norm_sq).mp h
  have hae' : gaussFourier μ f =ᵐ[ν] 0 := by
    filter_upwards [hae] with ξ hξ
    simp only [Pi.zero_apply] at hξ ⊢
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hξ)
  have hzero : gaussFourier μ f = 0 :=
    ((continuous_gaussFourier μ hf).ae_eq_iff_eq ν continuous_const).mp hae'
  exact ae_eq_zero_of_gaussFourier_eq_zero μ hf fun ξ => congrFun hzero ξ

end Injectivity

/-! ### The Gaussian mixture is s-finite -/

section GaussianMixture

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {P : H →L[ℝ] H} {N : ℝ → Measure H}

/-- The Gaussian mixture `ν_α` is s-finite: it is the bind of the s-finite weight
`s^{α/2-1} ds` against a measurable family of probability measures. -/
theorem IsCenteredGaussianLayers.sfinite_gaussianMixture (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) : SFinite (gaussianMixture N α) := by
  have hbind : gaussianMixture N α = (mixtureWeight α (Set.Ioi 0)).bind (scaledLayer N) :=
    hN.gaussianMixtureOn_eq_bind α measurableSet_Ioi subset_rfl
  rw [hbind, ← sum_sfiniteSeq (mixtureWeight α (Set.Ioi 0)),
    Measure.bind_sum _ _ hN.measurable_scaledLayer.aemeasurable]
  haveI : ∀ n, IsFiniteMeasure
      ((sfiniteSeq (mixtureWeight α (Set.Ioi 0)) n).bind (scaledLayer N)) := by
    intro n
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hN.measurable_scaledLayer.aemeasurable]
    have huniv : ∀ s, scaledLayer N s Set.univ = 1 := fun s =>
      (hN.isProbabilityMeasure_scaledLayer s).measure_univ
    simp only [huniv, lintegral_one]
    exact measure_lt_top _ _
  infer_instance

end GaussianMixture

end OperatorRidgelet
