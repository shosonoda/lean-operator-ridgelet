import OperatorRidgelet.Paper.Reconstruction
import OperatorRidgelet.Paper.Sampling
import OperatorRidgelet.Reconstruction.FiniteOrder
import OperatorRidgelet.Reconstruction.Decoder
import OperatorRidgelet.Reconstruction.VectorBiasFourierUnitary
import OperatorRidgelet.Reconstruction.VectorAdjoint

/-! # Strengthened spectral synthesis and finite-order coefficient statements -/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:B.2]** The spectral target has the uniform L¹ norm bound. -/
theorem lem_B_2_i (ν : Measure H) (G : H → Y) (_hG : Integrable G ν) :
    ∀ x : H, ‖spectralTarget ν G x‖ ≤ ∫ ξ, ‖G ξ‖ ∂ν := by
  intro x
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
  filter_upwards with ξ
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:B.2]** An integrable spectral density has a continuous target. -/
theorem lem_B_2_ii (ν : Measure H) (G : H → Y) (hG : Integrable G ν) :
    Continuous (spectralTarget ν G) :=
  continuous_spectralTarget ν hG

/-- **Lemma [lem:B.2]** A spectral density is determined by its target. -/
theorem lem_B_2_iii (ν : Measure H) (G : H → Y) (hG : Integrable G ν)
    (hzero : spectralTarget ν G = 0) : G =ᵐ[ν] 0 :=
  ae_eq_zero_of_spectralTarget_eq_zero_vec ν hG hzero

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:B.3]** A bounded density with a finite ray moment is L¹∩L². -/
theorem lem_B_3_i (ν : Measure H) {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (G : H → Y) (hG : StronglyMeasurable G)
    (hbound : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M) (r : ℕ)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    Integrable G ν ∧ MemLp G 2 ν := by
  obtain ⟨ω, hω⟩ := hI.nonempty hρ
  have hω0 : ω ≠ 0 := fun h => hI.zero_notMem (h ▸ hω)
  exact ⟨integrable_of_finiteRayMoment hν hω hω0 hG hM,
    memLp_two_of_finiteRayMoment hν hω hω0 hG hbound hM⟩

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:B.3]** The inverse integral represents the coefficient. -/
theorem lem_B_3_ii (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (G : H → Y) (hG : StronglyMeasurable G)
    (hbound : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M) (r : ℕ)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    StronglyMeasurable (coefficientFormulaVec ρ G) ∧
      (spectralCoefficientVec ν ρ G : H × ℝ → Y) =ᵐ[parameterMeasure ν]
        coefficientFormulaVec ρ G := by
  have hG₂ := (lem_B_3_i ν hν ρ hρ I hI G hG hbound r hM).2
  refine ⟨stronglyMeasurable_coefficientFormulaVec ρ hG, ?_⟩
  rw [spectralCoefficientVec_eq_toLp hν hα (hρ.isAdmissible α) hG hG₂]
  exact (memLp_coefficientFormulaVec hα hν (hρ.isAdmissible α) hG hG₂).coeFn_toLp

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  [CompleteSpace Y] [SecondCountableTopology Y] in
/-- **Lemma [lem:B.3]** Finitely many ray derivatives give pointwise decay. -/
theorem lem_B_3_iii (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (r : ℕ) :
    0 < finiteCoefficientDecayConstant ρ (r + 2) ∧
      finiteCoefficientDecayConstant ρ (r + 2) < ⊤ ∧ ∀ G : H → Y,
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U) →
      ∀ (a : H) (c : ℝ),
        ENNReal.ofReal ((1 + |c|) ^ (r + 2)) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
          finiteCoefficientDecayConstant ρ (r + 2) * rayDerivBound I G (r + 2) a :=
  finiteCoefficientDecayConstant_spec hρ hI (r + 2)

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:B.3]** The parameter moment is bounded by A_{r+2,r}. -/
theorem lem_B_3_iv (ν : Measure H) [SigmaFinite ν]
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (r : ℕ) :
    finiteCoefficientMomentConstant ρ r ≠ ⊤ ∧ ∀ G : H → Y, StronglyMeasurable G →
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U) →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ r) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        finiteCoefficientMomentConstant ρ r * finiteRayMoment ν I G (r + 2) r :=
  finiteCoefficientMomentConstant_spec hρ hI r

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:B.3]** Finite ray data imply a finite parameter moment. -/
theorem lem_B_3_v (ν : Measure H) [SigmaFinite ν]
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (G : H → Y) (hG : StronglyMeasurable G) (r : ℕ)
    (hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ r *
      ‖coefficientFormulaVec ρ G θ‖) (parameterMeasure ν) :=
  integrable_moment_norm_coefficientFormulaVec_of_contDiff hρ hI hG r hGs hM

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Theorem [thm:6.4]** All parameter moments are bounded, also for vector-valued densities. -/
theorem thm_6_4_moments (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (r : ℕ) :
    finiteCoefficientMomentConstant ρ r ≠ ⊤ ∧ ∀ G : H → Y, IsRegularAlongRays ν I G →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ r) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        finiteCoefficientMomentConstant ρ r * rayMoment ν I G (r + 2) := by
  obtain ⟨hC, hbound⟩ := finiteCoefficientMomentConstant_spec (ν := ν) (Y := Y) hρ hI r
  refine ⟨hC, fun G hG => ?_⟩
  have hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U := by
    intro a
    obtain ⟨U, hU, hIU, hdiff⟩ := hG.contDiffOn a
    exact ⟨U, hU, hIU, hdiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  exact (hbound G hG.stronglyMeasurable hGs).trans
    (mul_le_mul' le_rfl (finiteRayMoment_le_rayMoment ν I G (r + 2) r (by omega)))

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:4.2]** The network integrand is jointly absolutely integrable. -/
theorem thm_4_2_iii_e (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b)
    (G : H → ℂ) (hG : IsRegularAlongRays ν I G) (x : H) :
    Integrable (fun θ : H × ℝ => coefficientFormula ρ G θ *
      (b (⟪θ.1, x⟫ + θ.2) : ℂ)) (parameterMeasure ν) := by
  have h := integrable_prod_smul_coefficientFormulaVec hρ hI hG hβ.continuous
    hβ.polynomialGrowth x
  refine h.congr (Eventually.of_forall fun θ => ?_)
  dsimp only
  rw [Prod.mk.eta, coefficientFormulaVec_eq_coefficientFormula, smul_eq_mul, mul_comm]

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Theorem [thm:4.6]** The network integrand is Bochner integrable on the product. -/
theorem thm_4_6_representation_iii_e (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b)
    (G : H → Y) (hG : IsRegularAlongRays ν I G) (x : H) :
    Integrable (fun θ : H × ℝ => (b (⟪θ.1, x⟫ + θ.2) : ℂ) •
      coefficientFormulaVec ρ G θ) (parameterMeasure ν) :=
  integrable_prod_smul_coefficientFormulaVec hρ hI hG hβ.continuous hβ.polynomialGrowth x

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [BorelSpace H] in
/-- **Lemma [lem:A.1]** Bias Fourier transformation is a genuine unitary
with jointly measurable representatives and the angular normalization. -/
theorem lem_A_1 (ν : Measure H) [SigmaFinite ν] :
    ∃ U : Lp Y 2 (parameterMeasure ν) ≃ₗᵢ[ℂ]
      Lp Y 2 (ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • (volume : Measure ℝ))),
      ∀ γ : Lp Y 2 (parameterMeasure ν),
        ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
          HasBiasFourierVec ν γ Φ ∧
          Function.uncurry Φ =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)] ⇑(U γ) :=
  exists_unitary_hasBiasFourierVec ν

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Corollary [cor:4.4]** The decoder is C⁻¹ T⁻¹ S. -/
theorem cor_4_4_i (α : ℝ) (μ ν : Measure H) [IsProbabilityMeasure μ]
    (ρ : ℝ → ℝ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    coefficientDecoder α μ ν ρ γ =
      ((admissibilityConst α ρ : ℂ)⁻¹) • rieszInv μ ν (synthesis μ ν ρ γ) :=
  coefficientDecoder_apply α μ ν ρ γ

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Corollary [cor:4.4]** The bounded decoder is a left inverse. -/
theorem cor_4_4_ii (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : spectralRange μ ν) :
    coefficientDecoder α μ ν ρ (ridgeletExtension μ ν ρ f) = f :=
  coefficientDecoder_ridgeletExtension hν hρ f

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Corollary [cor:4.4]** The decoder norm is at most 1/√C. -/
theorem cor_4_4_iii (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ‖coefficientDecoder α μ ν ρ‖ ≤ (Real.sqrt (admissibilityConst α ρ))⁻¹ :=
  norm_coefficientDecoder_le hν hρ

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Corollary [cor:4.4]** Coefficient error δ gives spectral error δ/√C. -/
theorem cor_4_4_iv (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : spectralRange μ ν) (γ : Lp ℂ 2 (parameterMeasure ν))
    {δ : ℝ} (hδ : ‖γ - ridgeletExtension μ ν ρ f‖ ≤ δ) :
    ‖coefficientDecoder α μ ν ρ γ - f‖ ≤ δ / Real.sqrt (admissibilityConst α ρ) :=
  norm_coefficientDecoder_sub_le hν hρ f γ hδ

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:4.3]** Backprojection after analysis recovers the completed spectral density. -/
theorem thm_4_3_iv_completion (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : spectralRange μ ν) :
    backprojection α ν ρ (ridgeletExtension μ ν ρ f) =ᵐ[ν]
      fun ξ => admissibilityConst α ρ * (f : Lp ℂ 2 ν) ξ := by
  rw [OperatorRidgelet.ridgeletExtension_eq hν hρ,
    ridgeletExtensionCLM_eq_spectralCoefficient hν hα hρ μ f]
  exact hν.backprojection_spectralCoefficient hα hρ
    (Lp.stronglyMeasurable (f : Lp ℂ 2 ν)).measurable (Lp.memLp _)

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:4.6]** The completed vector spectral density is recovered in L². -/
theorem thm_4_6_frame_iv_completion (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : spectralRangeVec Y μ ν) :
    backprojectionVec α ν ρ (ridgeletExtensionVec Y μ ν ρ f) =ᵐ[ν]
      fun ξ => (admissibilityConst α ρ : ℂ) • (f : Lp Y 2 ν) ξ := by
  rw [ridgeletExtensionVec_eq hν hρ,
    ridgeletExtensionVecCLM_eq_spectralCoefficientVec hν hα hρ μ f]
  exact hν.backprojectionVec_spectralCoefficientVec hα hρ
    (Lp.stronglyMeasurable (f : Lp Y 2 ν)) (Lp.memLp _)

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:B.1]** The L² inverse formula is absolutely integrable
for almost every direction, for every bias value. -/
theorem lem_B_1_v {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (G : H → ℂ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∀ᵐ a ∂ν, ∀ c : ℝ, Integrable (fun ω : ℝ =>
      filterFourier ρ ω * G (-(ω • a)) * Complex.exp ((ω * c : ℝ) * Complex.I)) := by
  filter_upwards [ae_integrable_ray hα hν hρ hG hG₂] with a ha c
  exact ha.mul_unimodular (by fun_prop : Continuous fun ω : ℝ =>
    Complex.exp ((ω * c : ℝ) * Complex.I)).aestronglyMeasurable
      (Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [BorelSpace H] in
/-- **Lemma [lem:A.1]** The Fourier representatives agree on almost every section. -/
theorem lem_A_1_uniqueness (ν : Measure H) [SigmaFinite ν]
    (γ : H × ℝ → Y) (Φ Φ' : H → ℝ → Y) (hΦ : HasBiasFourierVec ν γ Φ)
    (hΦ' : HasBiasFourierVec ν γ Φ') :
    ∀ᵐ a ∂ν, Φ a =ᵐ[volume] Φ' a :=
  hΦ.ae_ae_eq hΦ'

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:3.6]** The coefficient operator has the bounded ray-average
adjoint and the scaled left-inverse identity. -/
theorem lem_3_6_i (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∃ W : Lp Y 2 ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      (∀ F, W F = spectralCoefficientVec ν ρ F) ∧
      (∀ γ, W.adjoint γ = backprojectionLpVec α ν ρ γ) ∧
      ‖W‖ ≤ Real.sqrt (admissibilityConst α ρ) ∧
      (∀ γ : Lp Y 2 (parameterMeasure ν), ‖backprojectionLpVec α ν ρ γ‖ ≤
        Real.sqrt (admissibilityConst α ρ) * ‖γ‖) ∧
      ∀ F, W.adjoint (W F) = (admissibilityConst α ρ : ℂ) • F :=
  exists_spectralCoefficientVecCLM_adjoint hν hα hρ

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:3.6]** The backprojection integral is absolutely convergent a.e. -/
theorem lem_3_6_ii (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (γ : Lp Y 2 (parameterMeasure ν)) (Φ : H → ℝ → Y)
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (hB : HasBiasFourierVec ν γ Φ) :
    ∀ᵐ ξ ∂ν, Integrable fun ω : ℝ =>
      ((starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) •
        Φ (-(ω⁻¹ • ξ)) ω :=
  hν.ae_integrable_backprojectionOfVec_integrand hρ (Lp.memLp γ) hΦ hB

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:3.6]** Every measurable Fourier representative gives Λ. -/
theorem lem_3_6_iii (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (γ : Lp Y 2 (parameterMeasure ν)) (Φ : H → ℝ → Y)
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (hB : HasBiasFourierVec ν γ Φ) :
    backprojectionVec α ν ρ γ =ᵐ[ν] backprojectionOfVec α ρ Φ :=
  hν.backprojectionVec_ae_eq_of_hasBiasFourierVec γ hΦ hB

end OperatorRidgelet.Paper
