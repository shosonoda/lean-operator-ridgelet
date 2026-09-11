import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.ToMathlib.VectorMeasureWithDensity
import OperatorRidgelet.Examples.HingeMeasure
import OperatorRidgelet.Sampling.Basic

/-! # The vector measure representation of an operator layer -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter
open LeanRidgelet
open scoped RealInnerProductSpace

variable {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
  [CompleteSpace Y] [MeasurableSpace Ω] {m : Measure Ω} [IsFiniteMeasure m]
  {a : Ω → H} {b : Ω → Y}

omit [IsFiniteMeasure m] in
/-- A mapped vector density synthesizes by composing its parameters with the map. -/
theorem integralNetwork_map_withDensity (γ : Ω → Y) (hγ : Integrable γ m)
    (φ : Ω → H × ℝ) (hφ : Measurable φ) {β : ℝ → ℝ} (hβ : Continuous β) (x : H)
    (hi : Integrable (fun y => (β (⟪(φ y).1, x⟫ + (φ y).2) : ℂ) • γ y) m) :
    integralNetwork (fun t => (β t : ℂ)) ((m.withDensityᵥ γ).map φ) x =
      ∫ y, (β (⟪(φ y).1, x⟫ + (φ y).2) : ℂ) • γ y ∂m := by
  let f : H × ℝ → ℂ := fun θ => (β (⟪θ.1, x⟫ + θ.2) : ℂ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfm := (hf.stronglyMeasurable.comp_measurable hφ).aestronglyMeasurable (μ := m)
  have hif : Integrable (fun y => f (φ y)) (m.withDensity fun y => ‖γ y‖ₑ) := by
    simp only [enorm_eq_nnnorm]
    rw [integrable_withDensity_iff_integrable_coe_smul₀ hγ.aestronglyMeasurable.nnnorm.aemeasurable]
    apply (integrable_norm_iff (hγ.aestronglyMeasurable.norm.smul hfm)).mp
    convert hi.norm using 1
    ext y
    simp [f, Function.comp_def, norm_smul]
    ring
  have hiv : (m.withDensityᵥ γ).Integrable (fun y => f (φ y)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hγ] using hif
  change (∫ᵛ θ, f θ ∂[ContinuousLinearMap.lsmul ℝ ℂ; (m.withDensityᵥ γ).map φ]) = _
  rw [VectorMeasure.integral_map hφ hf.aestronglyMeasurable hiv]
  rw [VectorMeasure.integral_withDensityᵥ hγ hif]
  rfl

/-- Pushing forward the vector density of a layer gives its integral-network representation. -/
theorem IsLayerData.operatorLayer_eq_integralNetwork (hL : IsLayerData m a b)
    {β : ℝ → ℝ} (hβ : Continuous β) :
    operatorLayer m a b β = integralNetwork (fun t => (β t : ℂ)) (layerMeasure m a b) := by
  funext x
  let f : H × ℝ → ℂ := fun θ => (β (⟪θ.1, x⟫ + θ.2) : ℂ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hφ : Measurable fun y => (a y, (0 : ℝ)) :=
    hL.stronglyMeasurable_a.measurable.prodMk measurable_const
  haveI : IsFiniteMeasure (m.withDensity fun y => ‖b y‖ₑ) :=
    isFiniteMeasure_withDensity hL.integrable_b.hasFiniteIntegral.ne
  have hi : Integrable (fun y => f (a y, 0)) (m.withDensity fun y => ‖b y‖ₑ) := by
    obtain ⟨C, hC⟩ := hL.exists_bound_comp_inner hβ x
    refine Integrable.of_bound (hf.stronglyMeasurable.comp_measurable hφ).aestronglyMeasurable C
      (Eventually.of_forall fun y => ?_)
    simpa [f, Complex.norm_real, Real.norm_eq_abs] using hC y
  have hiv : (m.withDensityᵥ b).Integrable (fun y => f (a y, 0)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hL.integrable_b] using hi
  change _ = ∫ᵛ θ, f θ ∂[ContinuousLinearMap.lsmul ℝ ℂ; (m.withDensityᵥ b).map (fun y => (a y, 0))]
  rw [VectorMeasure.integral_map hφ hf.aestronglyMeasurable hiv,
    VectorMeasure.integral_withDensityᵥ hL.integrable_b hi]
  simp [operatorLayer, f]

/-- The vector coefficient measure of a layer has finite variation. -/
theorem IsLayerData.isFiniteMeasure_layerMeasure_variation (hL : IsLayerData m a b) :
    IsFiniteMeasure (layerMeasure m a b).variation := by
  constructor
  exact lt_of_le_of_lt (VectorMeasure.variation_map_withDensityᵥ_univ_le hL.integrable_b _)
    hL.integrable_b.hasFiniteIntegral

/-- The mass of a layer coefficient is bounded by the integral of the output-vector norms. -/
theorem IsLayerData.polarWeight_layerMeasure_le (hL : IsLayerData m a b) :
    polarWeight (layerMeasure m a b) ≤ ∫ y, ‖b y‖ ∂m := by
  haveI := hL.isFiniteMeasure_layerMeasure_variation
  unfold polarWeight totalVariation
  have h := VectorMeasure.variation_map_withDensityᵥ_univ_le hL.integrable_b (fun y => (a y, (0 : ℝ)))
  have ht := ENNReal.toReal_mono hL.integrable_b.hasFiniteIntegral.ne h
  simpa only [layerMeasure, ← integral_norm_eq_lintegral_enorm hL.integrable_b.aestronglyMeasurable] using ht

/-- The polar law of a layer has a bounded second parameter moment. -/
theorem IsLayerData.polarLaw_moment (hL : IsLayerData m a b) :
    Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw (layerMeasure m a b)) ∧
      secondMoment (polarLaw (layerMeasure m a b)) ≤ layerSupNorm a ^ 2 := by
  haveI := hL.isFiniteMeasure_layerMeasure_variation
  by_cases h0 : totalVariation (layerMeasure m a b) = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0]
    simp only [integrable_zero_measure, secondMoment, integral_zero_measure, true_and]
    positivity
  haveI := isProbabilityMeasure_polarLaw (layerMeasure m a b) h0
  have hφ : Measurable fun y => (a y, (0 : ℝ)) :=
    hL.stronglyMeasurable_a.measurable.prodMk measurable_const
  have hset : MeasurableSet {θ : H × ℝ | ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ layerSupNorm a ^ 2} := by
    apply measurableSet_le <;> fun_prop
  have hmap : ∀ᵐ θ ∂(m.withDensityᵥ b).variation.map (fun y => (a y, (0 : ℝ))),
      ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ layerSupNorm a ^ 2 := by
    apply (ae_map_iff hφ.aemeasurable hset).2
    exact Eventually.of_forall fun y => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hL.norm_le_layerSupNorm y) 2
  have hvar : ∀ᵐ θ ∂(layerMeasure m a b).variation,
      ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ layerSupNorm a ^ 2 :=
    (MeasureTheory.ae_mono VectorMeasure.variation_map_le) hmap
  have hlaw : ∀ᵐ θ ∂polarLaw (layerMeasure m a b),
      ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ layerSupNorm a ^ 2 :=
    (polarLaw_absolutelyContinuous (layerMeasure m a b)).ae_le hvar
  refine ⟨Integrable.of_bound (by fun_prop) (layerSupNorm a ^ 2) ?_, ?_⟩
  · exact hlaw.mono fun θ hθ => by rwa [Real.norm_of_nonneg (by positivity)]
  · exact (integral_mono_of_nonneg (Eventually.of_forall fun θ => by positivity)
      (integrable_const (layerSupNorm a ^ 2)) hlaw).trans_eq (by simp)

section GaussianParameters

variable (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}

/-- The ReLU hinge expansion of a Gaussian network is jointly integrable under its first moment. -/
theorem integrable_gaussian_hinge_parameter (hγ : Integrable γ lam)
    (hmom : Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) * ‖γ θ‖) lam) (x : H) :
    Integrable (fun p : (H × ℝ) × ℝ =>
      (relu (⟪p.1.1, x⟫ + p.1.2 - p.2) : ℂ) • (gaussianActDeriv2 p.2 • γ p.1))
      (lam.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : (H × ℝ) × ℝ =>
      (relu (⟪p.1.1, x⟫ + p.1.2 - p.2) : ℂ) • (gaussianActDeriv2 p.2 • γ p.1))
      (lam.prod volume) := by
    have hs : Continuous fun p : (H × ℝ) × ℝ =>
        (relu (⟪p.1.1, x⟫ + p.1.2 - p.2) : ℂ) := by
      exact Complex.continuous_ofReal.comp (continuous_relu.comp (by fun_prop))
    exact hs.aestronglyMeasurable.smul
      ((continuous_gaussianActDeriv2.comp continuous_snd).aestronglyMeasurable.smul
        (hγ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst))
  have hd := (hmom.const_mul (‖x‖ + 1)).mul_prod
    (integrable_one_add_abs_pow_mul_abs_gaussianActDeriv2 1)
  refine hd.mono' hm (Eventually.of_forall fun p => ?_)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, pow_one]
  have hr : |relu (⟪p.1.1, x⟫ + p.1.2 - p.2)| ≤
      (‖x‖ + 1) * (1 + ‖p.1.1‖ + |p.1.2|) * (1 + |p.2|) := by
    rw [abs_of_nonneg (relu_nonneg _)]
    refine max_le ?_ (by positivity)
    have hi := (abs_real_inner_le_norm p.1.1 x)
    have hi' := le_abs_self ⟪p.1.1, x⟫
    have hc := le_abs_self p.1.2
    have ht := neg_le_abs p.2
    have h0 := norm_nonneg x
    have h1 := norm_nonneg p.1.1
    have h2 := abs_nonneg p.1.2
    have h3 := abs_nonneg p.2
    have hD : 1 ≤ (‖x‖ + 1) * (1 + ‖p.1.1‖ + |p.1.2|) := by
      nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2]
    nlinarith [mul_nonneg h0 h2, mul_nonneg (sub_nonneg.mpr hD) h3]
  calc |relu (⟪p.1.1, x⟫ + p.1.2 - p.2)| * (|gaussianActDeriv2 p.2| * ‖γ p.1‖)
      ≤ ((‖x‖ + 1) * (1 + ‖p.1.1‖ + |p.1.2|) * (1 + |p.2|)) *
        (|gaussianActDeriv2 p.2| * ‖γ p.1‖) := by gcongr
    _ = (‖x‖ + 1) * ((1 + ‖p.1.1‖ + |p.1.2|) * ‖γ p.1‖) *
        ((1 + |p.2|) * |gaussianActDeriv2 p.2|) := by ring

/-- Gaussian activation networks are ReLU networks with the pushed-forward hinge density. -/
theorem gaussianNetwork_eq_hingeNetwork (hγ : Integrable γ lam)
    (hmom : Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) * ‖γ θ‖) lam) :
    integralNetworkDensity (fun t => (gaussianFun t : ℂ)) lam γ =
      integralNetwork (fun t => (relu t : ℂ)) (hingeCoefficientMeasure lam γ) := by
  funext x
  have hφ : Measurable fun p : (H × ℝ) × ℝ => (p.1.1, p.1.2 - p.2) := by fun_prop
  have hi := integrable_gaussian_hinge_parameter lam hγ hmom x
  have hi' : Integrable (fun p : (H × ℝ) × ℝ =>
      (relu (⟪p.1.1, x⟫ + (p.1.2 - p.2)) : ℂ) •
        (gaussianActDeriv2 p.2 • γ p.1)) (lam.prod volume) := by
    simpa only [add_sub_assoc] using hi
  rw [hingeCoefficientMeasure, integralNetwork_map_withDensity _
    (integrable_gaussianActDeriv2_smul_of_integrable lam hγ) _ hφ continuous_relu x hi',
    integral_prod _ hi']
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    simp only [Complex.coe_smul, smul_smul, ← add_sub_assoc]
    rw [integral_smul_const, integral_relu_sub_mul_gaussianActDeriv2]

end GaussianParameters

end OperatorRidgelet
