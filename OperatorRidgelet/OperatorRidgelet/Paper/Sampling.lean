import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Sampling.Basic
import OperatorRidgelet.Sampling.Spectral
import OperatorRidgelet.Paper.Reconstruction

/-!
# Statements of Section 6 (finite-width approximation) and Appendix D

Each item is `theorem OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, identical to its twin in
`Challenge.Sampling`, proved from the library or left as `sorry`.

The probabilistic setup (the polar decomposition `Γ = h|Γ|`, `V = ‖Γ‖_TV`, `p = |Γ|/V`, the
product law of `N` independent samples, the Rademacher signs, the sampled network
`eq:polar-network`, the compact sup norm `‖·‖_{C(K)}`, `R_K`, and `M₂`) is documented in
`OperatorRidgelet.Sampling.Defs`.  Throughout, `Lip(β)` is any `L` with `LipschitzWith L β`,
and the width `N` is positive (for `N = 0` the manuscript's bounds `8V/√N` are void).

Theorems `thm:E` and `thm:D` are stated for the abstract direction measure `ν` of Appendix H
(σ-finite, full support, homogeneous of degree `α`), as Theorem `thm:A` is in
`OperatorRidgelet.Paper.Reconstruction`, with the frequency window `I` of the band-pass filter
`ρ` explicit; the tempered activation `β` that is a continuous function `b` of polynomial
growth is the pair `(β, b)` with `IsTemperedFunction β b`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Section 6: sampling bounds -/

/-- **Theorem [thm:general-rademacher]** General compact-open sampling bound.  Whenever the
atoms `x ↦ h(θ) β(⟪a, x⟫ + c)` are measurable and integrably bounded in `C(K)` (they are the
values of a Bochner-integrable map `Φ : Θ → C(K)`), the sampled network of the polar
decomposition of `Γ` satisfies `𝔼‖f_N − f‖_{C(K)} ≤ 2V 𝔑_N(K; p, β)`. -/
theorem thm_general_rademacher [MeasurableSpace H] [BorelSpace H] (β : ℝ → ℂ)
    (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation] {K : Set H} (hK : IsCompact K)
    (Φ : H × ℝ → (K →ᵇ ℂ))
    (hΦ : ∀ θ : H × ℝ, ∀ x : K, Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) * polarDensity Γ θ)
    (hint : Integrable Φ (polarLaw Γ)) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      2 * polarWeight Γ * rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ) := by
  have _hK := hK
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0, mul_zero, zero_mul]
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  have hΦ' : ∀ θ (x : K), Φ θ x = β (⟪(id θ).1, (x : H)⟫ + (id θ).2) * polarDensity Γ θ := hΦ
  have hpt : ∀ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x) =
        polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖ := by
    intro θ
    rw [← compactSupNorm_sampled_sub_eq (polarLaw Γ) β id (polarDensity Γ) hΦ' hint
      (polarWeight_nonneg Γ) hN θ]
    refine compactSupNorm_congr fun x hx => ?_
    rw [integralNetwork_eq_integral_polarLaw β Γ h0
      (integrable_ridge_of_integrable_atom (polarLaw Γ) β id hh hh1 hΦ' hint ⟨x, hx⟩)]
    rfl
  have hsym := integral_norm_sum_sub_le (polarLaw Γ) hint (signVector (N := N))
    (fun _ => (2 ^ N : ℝ)⁻¹) (fun _ => by positivity) (sum_signs_inv_pow_two N)
    fun σ j => signVector_eq_one_or_neg_one σ j
  rw [rademacherComplexity_eq_sum_signs N (polarLaw Γ) β (polarDensity Γ) hΦ hint]
  calc ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ)
      = ∫ θ, polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) := integral_congr_ae (Eventually.of_forall hpt)
    _ = polarWeight Γ / N * ∫ θ, ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) := integral_const_mul _ _
    _ ≤ polarWeight Γ / N * (2 * ∑ σ : Signs N, (2 ^ N : ℝ)⁻¹ *
          ∫ θ, ‖∑ j, signVector σ j • Φ (θ j)‖ ∂sampleLaw N (polarLaw Γ)) :=
        mul_le_mul_of_nonneg_left hsym (div_nonneg (polarWeight_nonneg Γ) (Nat.cast_nonneg N))
    _ = _ := by
        rw [← Finset.mul_sum]
        ring

/-- **Theorem [thm:lipschitz-barron]** Dimension-free compact-open Barron bound.  For real
globally Lipschitz `β` and `M₂² = ∫ (‖a‖² + |c|²) dp < ∞`, the sampled network of the polar
decomposition of `Γ` satisfies
`𝔼‖f_N − f‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂)`. -/
theorem thm_lipschitz_barron_i [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      8 * polarWeight Γ / Real.sqrt N *
        (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0]
    simp
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ ≤ 1 :=
    (ae_polarLaw_norm_polarDensity_eq_one Γ).mono fun θ hθ => hθ.le
  have hsqrt : Real.sqrt N / N = 1 / Real.sqrt N := Real.sqrt_div_self'
  calc ∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) ∂sampleLaw N (polarLaw Γ)
      = ∫ θ, polarWeight Γ / N *
          ‖∑ j, polarDensity Γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
            (N : ℝ) • ∫ θ', polarDensity Γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
              ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) :=
        integral_congr_ae (Eventually.of_forall
          (compactSupNorm_polarSampledNetwork_sub_eq hK hβ Γ h0 hM hN))
    _ = polarWeight Γ / N * ∫ θ,
          ‖∑ j, polarDensity Γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
            (N : ℝ) • ∫ θ', polarDensity Γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
              ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) := integral_const_mul _ _
    _ ≤ polarWeight Γ / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
          Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂polarLaw Γ))) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_sum_smul_ridgeAtom_sub_le hK hβ (polarLaw Γ) measurable_id hh hh1 hM N)
          (div_nonneg (polarWeight_nonneg Γ) (Nat.cast_nonneg N))
    _ = 8 * polarWeight Γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
        rw [secondMoment]
        calc polarWeight Γ / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂polarLaw Γ)))
            = 8 * polarWeight Γ * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂polarLaw Γ)) * (Real.sqrt N / N) := by
              ring
          _ = _ := by rw [hsqrt]; ring

/-- **Theorem [thm:lipschitz-barron]** Dimension-free compact-open Barron bound.  At least one
deterministic width-`N` realization satisfies the same bound
`‖f_N − f‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂)`. -/
theorem thm_lipschitz_barron_ii [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∃ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) ≤
        8 * polarWeight Γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
  by_cases h0 : totalVariation Γ = 0
  · refine ⟨fun _ => (0, 0), ?_⟩
    rw [polarWeight_eq_zero_of_totalVariation_eq_zero h0]
    refine le_of_le_of_eq (compactSupNorm_le le_rfl fun x _ => ?_) (by simp)
    rw [polarSampledNetwork_eq_zero _ h0, integralNetwork_eq_zero_of_totalVariation_eq_zero _ h0,
      sub_zero, norm_zero]
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hint : Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
      polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
        integralNetwork (fun t => (β t : ℂ)) Γ x)) (sampleLaw N (polarLaw Γ)) :=
    ((integrable_norm_sum_sub (polarLaw Γ) (integrable_polar_atom hK hβ Γ h0 hM) N).const_mul
      (polarWeight Γ / N)).congr (Eventually.of_forall fun θ =>
        (compactSupNorm_polarSampledNetwork_sub_eq hK hβ Γ h0 hM hN θ).symm)
  obtain ⟨θ, hθ⟩ := exists_realization_le_mean _ _ hint
  exact ⟨θ, hθ.trans (thm_lipschitz_barron_i hβ Γ hM hK hN)⟩

/-! ## Section 6: finite variation from the spectral density -/

section Spectral

variable [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- **Theorem [thm:E]** Finite variation and moments of the coefficient.  For a band-pass `ρ`
with frequency window `I` there is a finite constant `c_ρ`, depending only on `ρ` and `α`,
such that every `G` regular along rays satisfies
`∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α ≤ c_ρ M₄(G)`. -/
theorem thm_E_i (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ G : H → ℂ, IsRegularAlongRays ν I G →
      ∫⁻ θ, ENNReal.ofReal (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖ₑ
          ∂parameterMeasure ν ≤
        c * rayMoment ν I G 4 := by
  obtain ⟨c, hctop, hc⟩ :=
    exists_const_lintegral_moment_enorm_coefficientFormulaVec_le (ν := ν) (Y := ℂ) hρ hI 2
  refine ⟨c, hctop, fun G hG => le_trans (lintegral_mono fun θ => ?_) (hc G hG)⟩
  rw [← coefficientFormulaVec_eq_coefficientFormula ρ G θ]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  nlinarith [norm_nonneg θ.1, abs_nonneg θ.2]

/-- **Theorem [thm:E]** Finite variation and moments of the coefficient.  For `G` regular along
rays, `∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α < ∞`: the coefficient measure `γ_G λ_α` is finite with
finite second moment. -/
theorem thm_E_ii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖)
      (parameterMeasure ν) := by
  have hsm : StronglyMeasurable
      (fun θ : H × ℝ => (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖) :=
    (Continuous.stronglyMeasurable (by fun_prop)).mul
      (stronglyMeasurable_coefficientFormula ρ hG.stronglyMeasurable.measurable).norm
  refine (integrable_moment_norm_coefficientFormulaVec (Y := ℂ) hρ hI hG 2).mono
    hsm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
  have h1 : ‖(1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖‖ =
      (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖ :=
    Real.norm_of_nonneg (by positivity)
  have h2 : ‖(1 + ‖θ.1‖ + |θ.2|) ^ 2 * ‖coefficientFormulaVec ρ G θ‖‖ =
      (1 + ‖θ.1‖ + |θ.2|) ^ 2 * ‖coefficientFormulaVec ρ G θ‖ :=
    Real.norm_of_nonneg (by positivity)
  rw [h1, h2, coefficientFormulaVec_eq_coefficientFormula]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  nlinarith [norm_nonneg θ.1, abs_nonneg θ.2]

/-- **Theorem [thm:E]** Finite variation and moments of the coefficient.  Consequently, for every
real `β` that is globally Lipschitz and not a polynomial (a tempered activation that is the
function `b`), the target `C^{(α)}_{β,ρ} g_G` is the integral network `S_β[γ_G λ_α]`. -/
theorem thm_E_iii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) {L : ℝ≥0} (hb : LipschitzWith L b)
    (hpoly : ¬ IsPolynomialFun b) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    ∀ x : H, temperedAdmissibilityConst α β ρ * spectralTarget ν G x =
      integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν) (coefficientFormula ρ G)
        x := by
  intro x
  have hint : Integrable (fun θ : H × ℝ =>
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ) (ν.prod volume) := by
    refine (integrable_prod_smul_coefficientFormulaVec hρ hI hG hβ.continuous
      hβ.polynomialGrowth x).congr (Eventually.of_forall fun θ => ?_)
    show (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G (θ.1, θ.2) =
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ
    rw [Prod.mk.eta, coefficientFormulaVec_eq_coefficientFormula]
  rw [← thm_A_iii_c ν hα hν ρ hρ I hI β b hβ hpoly G hG x, integralNetworkDensity,
    parameterMeasure, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  show coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ) =
    (b (⟪a, x⟫ + c) : ℂ) * coefficientFormula ρ G (a, c)
  ring

/-- **Theorem [thm:E]** Finite variation and moments of the coefficient.  For real globally
Lipschitz non-polynomial `β`, the sampled network `eq:polar-network` of `γ_G λ_α`, with
`V = ‖γ_G‖_{L¹(λ_α)}` and `M₂` the second moment of `p = |γ_G| λ_α / V`, satisfies
`𝔼‖f_N − C^{(α)}_{β,ρ} g_G‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂)` for every compact
`K`. -/
theorem thm_E_iv (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) {L : ℝ≥0} (hb : LipschitzWith L b)
    (hpoly : ¬ IsPolynomialFun b) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) θ x -
            temperedAdmissibilityConst α β ρ * spectralTarget ν G x)
        ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) ≤
      8 * densityWeight (parameterMeasure ν) (coefficientFormula ρ G) / Real.sqrt N *
        (|b 0| + (L : ℝ) * compactRadius K *
          Real.sqrt (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)))) := by
  have hfun : coefficientFormulaVec (Y := ℂ) ρ G = coefficientFormula ρ G :=
    coefficientFormulaVec_eq_coefficientFormula' ρ G
  have hγ : Integrable (coefficientFormula ρ G) (parameterMeasure ν) :=
    hfun ▸ integrable_coefficientFormulaVec hρ hI hG
  have hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2)
      (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) :=
    hfun ▸ integrable_sq_densityLaw_coefficientFormulaVec hρ hI hG
  have hcongr : ∀ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) θ x -
            temperedAdmissibilityConst α β ρ * spectralTarget ν G x) =
        compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) θ x -
            integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) x) := fun θ =>
    compactSupNorm_congr fun x _ => by
      rw [thm_E_iii ν hα hν ρ hρ I hI β b hβ hb hpoly G hG x]
  rw [integral_congr_ae (Eventually.of_forall hcongr)]
  exact integral_compactSupNorm_densitySampledNetwork_sub_le hK hb hγ hM hN

/-! ## Section 6: constructive universal approximation -/

/-- **Theorem [thm:D]** Constructive universal approximation with rates.  For a continuous,
polynomially growing, non-polynomial real `β` (the function `b` of the tempered `β`), a
band-pass `ρ` with `C^{(α)}_{β,ρ} = 1`, a continuous `f : H → ℂ`, a compact `K`, and `ε > 0`,
there is a spectral density `G`, regular along rays, smooth, and vanishing outside a bounded
set, such that (i) `‖f − g_G‖_{C(K)} < ε`; (ii) `g_G = S_β[γ_G λ_α]` with a coefficient
measure `γ_G λ_α` that is finite with finite moments of all orders; (iii) if `β` is globally
Lipschitz, the sampled network of `γ_G λ_α` satisfies
`𝔼‖f − f_N‖_{C(K)} ≤ ε + (8V/√N)(|β(0)| + Lip(β) R_K M₂)` with `V = ‖γ_G‖_{L¹(λ_α)}` and
`M₂` the second moment of `|γ_G| λ_α / V`, and at least one deterministic width-`N` network
satisfies the same bound. -/
theorem thm_D (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hpoly : ¬ IsPolynomialFun b) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) {f : H → ℂ} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → ℂ, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      compactSupNorm K (fun x => f x - spectralTarget ν G x) < ε ∧
      spectralTarget ν G =
        integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
          (coefficientFormula ρ G) ∧
      (∀ m : ℕ, Integrable
        (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormula ρ G θ‖)
        (parameterMeasure ν)) ∧
      (∀ L : ℝ≥0, LipschitzWith L b → ∀ N : ℕ, 0 < N →
        (∫ θ, compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) ≤
          ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormula ρ G) / Real.sqrt N *
            (|b 0| + (L : ℝ) * compactRadius K *
              Real.sqrt
                (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))))) ∧
        ∃ θ : Fin N → H × ℝ,
          compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x) ≤
            ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormula ρ G) / Real.sqrt N *
              (|b 0| + (L : ℝ) * compactRadius K *
                Real.sqrt
                  (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))))) := by
  sorry

/-- **Theorem [thm:D]** Constructive universal approximation with rates.  In particular, the
finite-width networks with a continuous, polynomially growing, non-polynomial real activation
`β` are dense in `C(H)` for the compact-open topology. -/
theorem thm_D_dense (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b)
    (hpoly : ¬ IsPolynomialFun b) {f : H → ℂ} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → ℂ) (a : Fin N → H) (c : Fin N → ℝ),
      compactSupNorm K (fun x => f x - finiteNetwork (fun t => (b t : ℂ)) v a c x) < ε := by
  sorry

/-- **Theorem [thm:D]** Constructive universal approximation with rates.  The same statements
hold for continuous `f : H → Y` with values in a separable complex Hilbert space: there is a
`Y`-valued spectral density `G`, regular along rays, smooth, and vanishing outside a bounded
set, with (i) `‖f − g_G‖_{C(K;Y)} < ε`, (ii) `g_G = S_β[γ_G λ_α]` with a finite coefficient
measure with finite moments of all orders, and (iii), for globally Lipschitz `β`, the
vector-valued compact-open rate `𝔼‖f − f_N‖_{C(K;Y)} ≤ ε + 2V 𝔑^Y_N(K; p, β)` of Corollary
`cor:vector-rates`. -/
theorem thm_D_vec {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [SecondCountableTopology Y] (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hpoly : ¬ IsPolynomialFun b) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) {f : H → Y} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → Y, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      compactSupNorm K (fun x => f x - spectralTarget ν G x) < ε ∧
      spectralTarget ν G =
        integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
          (coefficientFormulaVec ρ G) ∧
      (∀ m : ℕ, Integrable
        (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖)
        (parameterMeasure ν)) ∧
      (∀ L : ℝ≥0, LipschitzWith L b → ∀ N : ℕ, 0 < N →
        ∫ θ, compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) ≤
          ε + 2 * densityWeight (parameterMeasure ν) (coefficientFormulaVec ρ G) *
            rademacherComplexity N K
              (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))
              (fun t => (b t : ℂ)) (densityPhase (coefficientFormulaVec ρ G))) := by
  sorry

end Spectral

/-! ## Section 6: vector-valued sampling -/

section VectorValued

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

/-- **Corollary [cor:vector-rates]** Vector-valued rates.  For globally Lipschitz `β`, a
`Y`-valued `Γ` whose law `p = |Γ|/V` has finite second moment, and every Borel probability
measure `ζ` on `H` with `∫ ‖x‖² dζ < ∞`,
`𝔼‖f_N − f‖²_{L²(ζ;Y)} ≤ (V²/N) ∫ ‖β(⟪a,·⟫ + c)‖²_{L²(ζ)} dp`. -/
theorem cor_vector_rates_i_a [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) {N : ℕ} (hN : 0 < N) :
    ∫ θ, (∫ x, ‖polarSampledNetwork β Γ θ x - integralNetwork β Γ x‖ ^ 2 ∂ζ)
        ∂sampleLaw N (polarLaw Γ) ≤
      polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ := by
  -- Requires the polar decomposition `Γ = h|Γ|` of a `Y`-valued measure, i.e. the
  -- Radon–Nikodym theorem for Hilbert-space-valued measures, which Mathlib only provides for
  -- signed and complex measures (`polarDensity Γ` is the junk value `0` otherwise).
  sorry

/-- **Corollary [cor:vector-rates]** Vector-valued rates.  The `L²(ζ;Y)` rate is explicit:
`(V²/N) ∫ ‖β(⟪a,·⟫ + c)‖²_{L²(ζ)} dp ≤ (2V²/N)(|β(0)|² + Lip(β)² (1 + ∫ ‖x‖² dζ) M₂²)`. -/
theorem cor_vector_rates_i_b [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) {N : ℕ} (hN : 0 < N) :
    polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ ≤
      2 * polarWeight Γ ^ 2 / N *
        (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * secondMoment (polarLaw Γ)) := by
  sorry

/-- **Corollary [cor:vector-rates]** Vector-valued rates.  For every compact `K`,
`𝔼‖f_N − f‖_{C(K;Y)} ≤ 2V 𝔑^Y_N(K; p, β)`, where `𝔑^Y_N` is the Rademacher complexity with the
absolute value replaced by the norm of `Y`. -/
theorem cor_vector_rates_ii_a [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      2 * polarWeight Γ * rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ) := by
  sorry

/-- **Corollary [cor:vector-rates]** Vector-valued rates.  For every compact `K`,
`𝔑^Y_N(K; p, β) → 0` as `N → ∞`. -/
theorem cor_vector_rates_ii_b [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) :
    Tendsto (fun N : ℕ => rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ)) atTop
      (𝓝 0) := by
  sorry

end VectorValued

/-! ## Appendix D: supplementary sampling results -/

/-- **Lemma [lem:qualitative-sampling]** Qualitative finite-atomic approximation.  For
continuous `β`, compact `K`, and `∫ ‖β(⟪a,·⟫ + c)‖_{C(K)} d|Γ| < ∞`, for every `ε > 0` there
is a finite atomic complex measure `Γ_ε = ∑_j w_j δ_{θ_j}` with
`‖S_β Γ_ε − S_β Γ‖_{C(K)} < ε`. -/
theorem lem_qualitative_sampling [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ}
    (hβ : Continuous β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation] {K : Set H}
    (hK : IsCompact K)
    (hint : Integrable (fun θ : H × ℝ => compactSupNorm K fun x => β (⟪θ.1, x⟫ + θ.2))
      Γ.variation)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℂ) (θ : Fin n → H × ℝ),
      compactSupNorm K
        (fun x => integralNetwork β (atomicMeasure w θ) x - integralNetwork β Γ x) < ε := by
  by_cases h0 : totalVariation Γ = 0
  · refine ⟨0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    refine lt_of_le_of_lt (compactSupNorm_le le_rfl fun x _ => ?_) hε
    rw [integralNetwork_atomicMeasure, integralNetwork_eq_zero_of_totalVariation_eq_zero β h0]
    simp
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hV : 0 < polarWeight Γ := polarWeight_pos Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  set h₀ := hh.mk (polarDensity Γ) with hh₀def
  have hh₀m : StronglyMeasurable h₀ := hh.stronglyMeasurable_mk
  have hh₀eq : polarDensity Γ =ᵐ[polarLaw Γ] h₀ := hh.ae_eq_mk
  -- the ridge atoms in `C(K)` and the atoms `h₀ β(⟪a, ·⟫ + c)`
  have hΨm : StronglyMeasurable (ridgeAtom hK hβ) := stronglyMeasurable_ridgeAtom hK hβ
  have hΨint : Integrable (ridgeAtom hK hβ) (polarLaw Γ) :=
    (hint.smul_measure (ENNReal.inv_ne_top.mpr h0)).mono' hΨm.aestronglyMeasurable
      (Eventually.of_forall fun θ => (norm_ridgeAtom hK hβ θ).le)
  set Φ₀ : H × ℝ → (K →ᵇ ℂ) := fun θ => h₀ θ • ridgeAtom hK hβ θ with hΦ₀def
  have hΦ₀m : StronglyMeasurable Φ₀ := hh₀m.smul hΨm
  have hΦ₀ : Integrable Φ₀ (polarLaw Γ) := by
    refine hΨint.norm.mono' hΦ₀m.aestronglyMeasurable ?_
    filter_upwards [hh1, hh₀eq] with θ h1 h2
    rw [norm_smul, ← h2, h1, one_mul]
  -- the target is `V ∫ Φ₀` on `K`
  have hf : ∀ x (hx : x ∈ K),
      integralNetwork β Γ x = polarWeight Γ • (∫ θ, Φ₀ θ ∂polarLaw Γ) ⟨x, hx⟩ := by
    intro x hx
    have hintx : Integrable (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) (polarLaw Γ) := by
      have hΨnorm : Integrable (fun θ => ‖ridgeAtom hK hβ θ‖) (polarLaw Γ) := hΨint.norm
      refine hΨnorm.mono'
        (hβ.comp (by fun_prop : Continuous fun θ : H × ℝ => ⟪θ.1, x⟫ + θ.2)).aestronglyMeasurable
        (Eventually.of_forall fun θ => ?_)
      exact BoundedContinuousFunction.norm_coe_le_norm (ridgeAtom hK hβ θ) ⟨x, hx⟩
    rw [integralNetwork_eq_integral_polarLaw β Γ h0 hintx]
    congr 1
    change _ = (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : K)) (∫ θ, Φ₀ θ ∂polarLaw Γ)
    rw [← ContinuousLinearMap.integral_comp_comm _ hΦ₀]
    refine integral_congr_ae ?_
    filter_upwards [hh₀eq] with θ hθ
    change β (⟪θ.1, x⟫ + θ.2) • polarDensity Γ θ = (h₀ θ • ridgeAtom hK hβ θ) ⟨x, hx⟩
    rw [hθ]
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, ridgeAtom_apply]
    ring
  -- simple-function approximation of `Φ₀` in the separable space `C(K)`
  borelize (K →ᵇ ℂ)
  haveI : SecondCountableTopology (K →ᵇ ℂ) := secondCountableTopology_boundedContinuousFunction hK
  haveI : TopologicalSpace.SeparableSpace (Set.range Φ₀) :=
    (TopologicalSpace.IsSeparable.of_separableSpace _).separableSpace
  have hΦ₀meas : Measurable Φ₀ := hΦ₀m.measurable
  obtain ⟨θ₁⟩ : Nonempty (H × ℝ) := inferInstance
  have hy₀ : Φ₀ θ₁ ∈ Set.range Φ₀ := ⟨θ₁, rfl⟩
  have htend := SimpleFunc.tendsto_approxOn_L1_enorm hΦ₀meas hy₀ (μ := polarLaw Γ)
    (Eventually.of_forall fun θ => subset_closure ⟨θ, rfl⟩) (hΦ₀.sub (integrable_const _)).2
  have hεV : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / polarWeight Γ) :=
    ENNReal.ofReal_pos.mpr (div_pos hε hV)
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hεV)).exists
  set φ := SimpleFunc.approxOn Φ₀ hΦ₀meas (Set.range Φ₀) (Φ₀ θ₁) hy₀ n with hφdef
  have hφint : Integrable φ (polarLaw Γ) :=
    SimpleFunc.integrable_approxOn hΦ₀meas hΦ₀ hy₀ (integrable_const _) n
  have hφmem : ∀ y ∈ φ.range, ∃ θ, Φ₀ θ = y := by
    intro y hy
    obtain ⟨θ, hθ⟩ := SimpleFunc.mem_range.mp hy
    obtain ⟨θ', hθ'⟩ := SimpleFunc.approxOn_mem hΦ₀meas hy₀ n θ
    exact ⟨θ', hθ'.trans hθ⟩
  choose! θy hθy using hφmem
  let e : φ.range ≃ Fin φ.range.card := φ.range.equivFin
  refine ⟨φ.range.card,
    fun i => ((polarWeight Γ * (polarLaw Γ).real (φ ⁻¹' {(e.symm i : K →ᵇ ℂ)}) : ℝ) : ℂ) *
      h₀ (θy (e.symm i)),
    fun i => θy (e.symm i), ?_⟩
  -- the atomic network is `V ∫ φ` on `K`
  have hatom : ∀ x (hx : x ∈ K), integralNetwork β (atomicMeasure
      (fun i => ((polarWeight Γ * (polarLaw Γ).real (φ ⁻¹' {(e.symm i : K →ᵇ ℂ)}) : ℝ) : ℂ) *
        h₀ (θy (e.symm i))) (fun i => θy (e.symm i))) x =
      polarWeight Γ • (∫ θ, φ θ ∂polarLaw Γ) ⟨x, hx⟩ := by
    intro x hx
    rw [integralNetwork_atomicMeasure, ← SimpleFunc.integral_eq_integral φ hφint,
      SimpleFunc.integral_eq]
    change _ = polarWeight Γ • (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : K))
      (∑ y ∈ φ.range, (polarLaw Γ).real (φ ⁻¹' {y}) • y)
    rw [map_sum, ← Finset.sum_coe_sort φ.range, ← Equiv.sum_comp e.symm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hy := hθy (e.symm i) (e.symm i).2
    have hyx : (Φ₀ (θy (e.symm i))) ⟨x, hx⟩ = (e.symm i : K →ᵇ ℂ) ⟨x, hx⟩ := by rw [hy]
    change _ = polarWeight Γ •
      ((polarLaw Γ).real (φ ⁻¹' {(e.symm i : K →ᵇ ℂ)}) • (e.symm i : K →ᵇ ℂ) ⟨x, hx⟩)
    rw [← hyx]
    simp only [hΦ₀def, BoundedContinuousFunction.coe_smul, smul_eq_mul, ridgeAtom_apply,
      Complex.real_smul, Complex.ofReal_mul]
    ring
  have hnorm : ‖∫ θ, φ θ ∂polarLaw Γ - ∫ θ, Φ₀ θ ∂polarLaw Γ‖ < ε / polarWeight Γ := by
    rw [← integral_sub hφint hΦ₀]
    refine (norm_integral_le_integral_norm _).trans_lt ?_
    rw [integral_norm_eq_lintegral_enorm (f := fun a => φ a - Φ₀ a)
      (hφint.sub hΦ₀).aestronglyMeasurable]
    exact ENNReal.toReal_lt_of_lt_ofReal hn
  refine lt_of_le_of_lt (compactSupNorm_le
    (a := polarWeight Γ * ‖∫ θ, φ θ ∂polarLaw Γ - ∫ θ, Φ₀ θ ∂polarLaw Γ‖)
    (mul_nonneg hV.le (norm_nonneg _)) fun x hx => ?_) ?_
  · rw [hatom x hx, hf x hx, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hV]
    refine mul_le_mul_of_nonneg_left ?_ hV.le
    exact BoundedContinuousFunction.norm_coe_le_norm
      (∫ θ, φ θ ∂polarLaw Γ - ∫ θ, Φ₀ θ ∂polarLaw Γ) ⟨x, hx⟩
  · calc polarWeight Γ * ‖∫ θ, φ θ ∂polarLaw Γ - ∫ θ, Φ₀ θ ∂polarLaw Γ‖
        < polarWeight Γ * (ε / polarWeight Γ) := mul_lt_mul_of_pos_left hnorm hV
      _ = ε := mul_div_cancel₀ ε hV.ne'

/-- **Corollary [cor:sampling-concentration]** Concentration for bounded parameters.  Under the
hypotheses of Theorem `thm:lipschitz-barron`, if `‖a‖² + |c|² ≤ B²` almost surely for some
`B ≥ 0` and `M_K = |β(0)| + Lip(β) R_K B`, then with probability at least `1 − δ`,
`‖f_N − f‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂) + V M_K √(2 log(1/δ)/N)`. -/
theorem cor_sampling_concentration [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ θ ∂polarLaw Γ, ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ B ^ 2) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    sampleLaw N (polarLaw Γ) {θ |
        8 * polarWeight Γ / Real.sqrt N *
            (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) +
          polarWeight Γ * (|β 0| + (L : ℝ) * compactRadius K * B) *
            Real.sqrt (2 * Real.log (1 / δ) / N) <
        compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x)} ≤
      ENNReal.ofReal δ := by
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN]
    simp
  haveI := isProbabilityMeasure_polarLaw Γ h0
  -- the bound is void for `δ ≥ 1`
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1)
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ hδ1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hV : 0 < polarWeight Γ := polarWeight_pos Γ h0
  have hR : 0 ≤ compactRadius K := compactRadius_nonneg K
  have hMK0 : 0 ≤ |β 0| + (L : ℝ) * compactRadius K * B := by positivity
  have hE0 : 0 ≤ 8 * polarWeight Γ / Real.sqrt N *
      (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
    positivity
  have hβc := continuous_ofReal_comp hβ
  -- the clamped, everywhere-bounded modification `g` of the atoms `Φ(θ) = h(θ) β(⟪a, ·⟫ + c)`
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  set h₀ := hh.mk (polarDensity Γ) with hh₀def
  have hh₀m : StronglyMeasurable h₀ := hh.stronglyMeasurable_mk
  have hh₀eq : polarDensity Γ =ᵐ[polarLaw Γ] h₀ := hh.ae_eq_mk
  set S : Set (H × ℝ) := {θ | ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ B ^ 2 ∧ ‖h₀ θ‖ ≤ 1} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_le (by fun_prop : Continuous fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2).measurable
      measurable_const).inter (measurableSet_le hh₀m.norm.measurable measurable_const)
  set g : H × ℝ → (K →ᵇ ℂ) := fun θ => if θ ∈ S then h₀ θ • ridgeAtom hK hβc θ else 0 with hgdef
  have hgm : StronglyMeasurable g :=
    StronglyMeasurable.ite hSm (hh₀m.smul (stronglyMeasurable_ridgeAtom hK hβc))
      stronglyMeasurable_const
  have hgM : ∀ θ, ‖g θ‖ ≤ |β 0| + (L : ℝ) * compactRadius K * B := by
    intro θ
    simp only [hgdef]
    split_ifs with hθ
    · rw [norm_smul]
      calc ‖h₀ θ‖ * ‖ridgeAtom hK hβc θ‖ ≤ 1 * (|β 0| + (L : ℝ) * compactRadius K * B) :=
            mul_le_mul hθ.2 (norm_ridgeAtom_le_of_sq_le hK hβ hB0 hθ.1) (norm_nonneg _)
              zero_le_one
        _ = _ := one_mul _
    · rw [norm_zero]
      exact hMK0
  have hgΦ : g =ᵐ[polarLaw Γ] fun θ => polarDensity Γ θ • ridgeAtom hK hβc θ := by
    filter_upwards [hB, hh1, hh₀eq] with θ h1 h2 h3
    have hθS : θ ∈ S := ⟨h1, by rw [← h3, h2]⟩
    simp only [hgdef, if_pos hθS, h3]
  have hgint : ∫ θ, g θ ∂polarLaw Γ = ∫ θ, polarDensity Γ θ • ridgeAtom hK hβc θ ∂polarLaw Γ :=
    integral_congr_ae hgΦ
  -- the error is `(V/N) F` almost surely, with `F(θ) = ‖∑_j g(θ_j) − N ∫ g‖`
  have herrF : ∀ᵐ θ ∂sampleLaw N (polarLaw Γ),
      compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) =
      polarWeight Γ / N * ‖∑ j, g (θ j) - (N : ℝ) • ∫ x, g x ∂polarLaw Γ‖ := by
    filter_upwards [ae_sampleLaw_forall (N := N) hgΦ] with θ hθ
    rw [compactSupNorm_polarSampledNetwork_sub_eq hK hβ Γ h0 hM hN θ, hgint,
      Finset.sum_congr rfl fun j _ => hθ j]
  have hErr := thm_lipschitz_barron_i hβ Γ hM hK hN
  have hEF : ∫ θ, compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) ∂sampleLaw N (polarLaw Γ) =
      polarWeight Γ / N *
        ∫ θ, ‖∑ j, g (θ j) - (N : ℝ) • ∫ x, g x ∂polarLaw Γ‖ ∂sampleLaw N (polarLaw Γ) := by
    rw [integral_congr_ae herrF, integral_const_mul]
  by_cases hMK : |β 0| + (L : ℝ) * compactRadius K * B = 0
  · -- degenerate case: the clamped atoms vanish, so the error is zero almost surely
    have hg0 : ∀ θ, g θ = 0 := fun θ => norm_le_zero_iff.mp (hMK ▸ hgM θ)
    have herr0 : ∀ᵐ θ ∂sampleLaw N (polarLaw Γ),
        compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) = 0 := by
      filter_upwards [herrF] with θ hθ
      rw [hθ]
      simp [hg0]
    have hnull : sampleLaw N (polarLaw Γ) {θ |
        8 * polarWeight Γ / Real.sqrt N *
            (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) +
          polarWeight Γ * (|β 0| + (L : ℝ) * compactRadius K * B) *
            Real.sqrt (2 * Real.log (1 / δ) / N) <
        compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x)} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp herr0)
      intro θ hθ hθ0
      simp only [Set.mem_setOf_eq] at hθ
      rw [hθ0, hMK, mul_zero, zero_mul, add_zero] at hθ
      exact absurd hθ (not_lt.mpr hE0)
    rw [hnull]
    exact zero_le
  have hMKpos : 0 < |β 0| + (L : ℝ) * compactRadius K * B := lt_of_le_of_ne hMK0 (Ne.symm hMK)
  -- the bounded-difference inequality for `F`, with deviation `ε = N M_K √(2 log(1/δ)/N)`
  set ε : ℝ := N * (|β 0| + (L : ℝ) * compactRadius K * B) *
    Real.sqrt (2 * Real.log (1 / δ) / N) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  set F := ∫ θ, ‖∑ j, g (θ j) - (N : ℝ) • ∫ x, g x ∂polarLaw Γ‖ ∂sampleLaw N (polarLaw Γ)
    with hFdef
  have hmc : sampleLaw N (polarLaw Γ)
      {θ | ε ≤ ‖∑ j, g (θ j) - (N : ℝ) • ∫ x, g x ∂polarLaw Γ‖ - F} ≤
      ENNReal.ofReal
        (Real.exp (-ε ^ 2 / (2 * N * (|β 0| + (L : ℝ) * compactRadius K * B) ^ 2))) :=
    measure_norm_sum_sub_sub_integral_ge_le (polarLaw Γ) hgm hMKpos hgM N hε0
  have hexp : Real.exp (-ε ^ 2 / (2 * N * (|β 0| + (L : ℝ) * compactRadius K * B) ^ 2)) = δ := by
    have hsq : Real.sqrt (2 * Real.log (1 / δ) / N) ^ 2 = 2 * Real.log (1 / δ) / N :=
      Real.sq_sqrt (by positivity)
    have hkey : -ε ^ 2 / (2 * N * (|β 0| + (L : ℝ) * compactRadius K * B) ^ 2) =
        -Real.log (1 / δ) := by
      rw [hεdef, mul_pow, hsq]
      field_simp
    rw [hkey, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  rw [hexp] at hmc
  refine le_trans (measure_mono_ae ?_) hmc
  filter_upwards [herrF] with θ hθ hthr
  replace hthr : _ < _ := hthr
  show ε ≤ _
  rw [hθ] at hthr
  have hVN : 0 < polarWeight Γ / N := by positivity
  have hVε : polarWeight Γ / N * ε =
      polarWeight Γ * (|β 0| + (L : ℝ) * compactRadius K * B) *
        Real.sqrt (2 * Real.log (1 / δ) / N) := by
    rw [hεdef]
    field_simp
  by_contra hcon
  have h1 := mul_lt_mul_of_pos_left (not_le.mp hcon) hVN
  rw [hVε, mul_sub, ← hEF] at h1
  linarith

section Hilbert

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.  For `Y ∈ L²(p; X)` with
values in a separable Hilbert space, independent copies `Y_j`, `f = V 𝔼Y`, and
`f_N = V N⁻¹ ∑_j Y_j`: `𝔼‖f_N − f‖² = (V²/N)(𝔼‖Y‖² − ‖𝔼Y‖²)`. -/
theorem lem_hilbert_sampling_i (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p =
      V ^ 2 / N * ((∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖∫ ω', Y ω' ∂p‖ ^ 2) :=
  integral_norm_sq_sampleMean p hY V hN

/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.
`𝔼‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_hilbert_sampling_ii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p ≤
      V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  rw [lem_hilbert_sampling_i p hY V hN]
  have h1 : 0 ≤ V ^ 2 / N := by positivity
  have h2 : 0 ≤ ‖∫ ω', Y ω' ∂p‖ ^ 2 := by positivity
  nlinarith

/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.  A deterministic sample
satisfies the same upper bound `‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_hilbert_sampling_iii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ ω : Fin N → Ω,
      ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ≤ V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  have hL : MemLp (fun ω : Fin N → Ω => (V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p) 2
      (sampleLaw N p) :=
    ((memLp_finsetSum Finset.univ fun j _ => memLp_eval_pi p hY j).const_smul
      (V / N : ℝ)).sub ((memLp_const _).const_smul V)
  obtain ⟨ω, hω⟩ := exists_le_integral ((memLp_two_iff_integrable_sq_norm hL.1).mp hL)
  exact ⟨ω, hω.trans (lem_hilbert_sampling_ii p hY V hN)⟩

end Hilbert

/-- **Corollary [cor:operator-sampling]** Sampling in operator parameters.  For a finite
complex measure `Γ_op` on `𝓛₂(H) × H` with polar decomposition `h_op |Γ_op|`,
`V_op = ‖Γ_op‖_TV`, `p_op = |Γ_op|/V_op`, real globally Lipschitz `β`, readout normalized by
`⟪ℓ, z⟫ = 1`, and `M_op² = ∫ (‖A^*ψ‖² + |⟪ψ, b⟫|²) dp_op < ∞`, sampling `(A_j, b_j)` from
`p_op` with the weights `h_op` gives
`𝔼‖f_{op,N} − S_op Γ_op‖_{C(K)} ≤ 8 V_op N^{-1/2} (|β(0)| + Lip(β) R_K M_op)`. -/
theorem cor_operator_sampling_i [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) [IsFiniteMeasure Γop.variation]
    (hHS : ∀ᵐ q ∂Γop.variation, IsHilbertSchmidt q.1)
    (hM : Integrable (fun q : OperatorRidgeParameter H =>
      ‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2) (polarLaw Γop))
    {ℓ z : H} (hℓz : ⟪ℓ, z⟫ = 1) {K : Set H} (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ ω, compactSupNorm K (fun x =>
          sampledOperatorNetwork (rankOneActivation β ψ z) ℓ (polarWeight Γop)
              (polarDensity Γop) ω x -
            operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x)
        ∂sampleLaw N (polarLaw Γop) ≤
      8 * polarWeight Γop / Real.sqrt N *
        (|β 0| + (L : ℝ) * compactRadius K *
          Real.sqrt (operatorSecondMoment ψ (polarLaw Γop))) := by
  have _hHS := hHS
  by_cases h0 : totalVariation Γop = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0]
    simp
  haveI := isProbabilityMeasure_polarLaw Γop h0
  have hπ : Measurable (operatorParameterMap ψ) := measurable_operatorParameterMap ψ
  have hM' : Integrable (fun q : OperatorRidgeParameter H =>
      ‖(operatorParameterMap ψ q).1‖ ^ 2 + |(operatorParameterMap ψ q).2| ^ 2) (polarLaw Γop) :=
    hM
  have hh : AEStronglyMeasurable (polarDensity Γop) (polarLaw Γop) :=
    aestronglyMeasurable_polarDensity Γop (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ q ∂polarLaw Γop, ‖polarDensity Γop q‖ ≤ 1 :=
    (ae_polarLaw_norm_polarDensity_eq_one Γop).mono fun q hq => hq.le
  have hΦ : Integrable (fun q => polarDensity Γop q •
      ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ q)) (polarLaw Γop) :=
    integrable_smul_ridgeAtom hK hβ (polarLaw Γop) hπ hh hh1 hM'
  have hneuron : ∀ (q : OperatorRidgeParameter H) (x : H),
      operatorNeuron (rankOneActivation β ψ z) ℓ q.1 q.2 x =
        β (⟪(operatorParameterMap ψ q).1, x⟫ + (operatorParameterMap ψ q).2) := fun q x => by
    rw [operatorNeuron_rankOneActivation, hℓz, one_mul]
    rfl
  have hpt : ∀ ω : Fin N → OperatorRidgeParameter H,
      compactSupNorm K (fun x =>
        sampledOperatorNetwork (rankOneActivation β ψ z) ℓ (polarWeight Γop) (polarDensity Γop)
            ω x - operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x) =
      polarWeight Γop / N * ‖∑ j, polarDensity Γop (ω j) •
          ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ (ω j)) -
        (N : ℝ) • ∫ q, polarDensity Γop q •
          ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ q) ∂polarLaw Γop‖ := by
    intro ω
    rw [← compactSupNorm_sampled_sub_eq (polarLaw Γop) (fun t => (β t : ℂ))
      (operatorParameterMap ψ) (polarDensity Γop)
      (smul_ridgeAtom_apply hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ)
        (polarDensity Γop)) hΦ (polarWeight_nonneg Γop) hN ω]
    refine compactSupNorm_congr fun x _ => ?_
    have hsyn : operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x =
        polarWeight Γop • ∫ q, (β (⟪(operatorParameterMap ψ q).1, x⟫ +
          (operatorParameterMap ψ q).2) : ℂ) • polarDensity Γop q ∂polarLaw Γop := by
      unfold operatorSynthesis
      simp_rw [hneuron]
      exact vectorIntegral_eq_integral_polarLaw Γop h0 (integrable_ridge_of_secondMoment
        (polarLaw Γop) hπ (lipschitzWith_ofReal_comp hβ) hM' x)
    rw [hsyn]
    simp only [sampledOperatorNetwork, operatorFiniteNetwork, hneuron, Complex.real_smul,
      smul_eq_mul]
  have hsqrt : Real.sqrt N / N = 1 / Real.sqrt N := Real.sqrt_div_self'
  calc ∫ ω, compactSupNorm K (fun x =>
          sampledOperatorNetwork (rankOneActivation β ψ z) ℓ (polarWeight Γop)
              (polarDensity Γop) ω x -
            operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x) ∂sampleLaw N (polarLaw Γop)
      = ∫ ω, polarWeight Γop / N * ‖∑ j, polarDensity Γop (ω j) •
            ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ (ω j)) -
          (N : ℝ) • ∫ q, polarDensity Γop q •
            ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ q) ∂polarLaw Γop‖
          ∂sampleLaw N (polarLaw Γop) := integral_congr_ae (Eventually.of_forall hpt)
    _ = polarWeight Γop / N * ∫ ω, ‖∑ j, polarDensity Γop (ω j) •
            ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ (ω j)) -
          (N : ℝ) • ∫ q, polarDensity Γop q •
            ridgeAtom hK (continuous_ofReal_comp hβ) (operatorParameterMap ψ q) ∂polarLaw Γop‖
          ∂sampleLaw N (polarLaw Γop) := integral_const_mul _ _
    _ ≤ polarWeight Γop / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
          Real.sqrt (∫ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2)
            ∂polarLaw Γop))) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_sum_smul_ridgeAtom_sub_le hK hβ (polarLaw Γop) hπ hh hh1 hM' N)
          (div_nonneg (polarWeight_nonneg Γop) (Nat.cast_nonneg N))
    _ = 8 * polarWeight Γop / Real.sqrt N * (|β 0| + (L : ℝ) * compactRadius K *
          Real.sqrt (operatorSecondMoment ψ (polarLaw Γop))) := by
        rw [operatorSecondMoment]
        calc polarWeight Γop / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2)
                  ∂polarLaw Γop)))
            = 8 * polarWeight Γop * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2)
                  ∂polarLaw Γop)) * (Real.sqrt N / N) := by ring
          _ = _ := by rw [hsqrt]; ring

/-- **Corollary [cor:operator-sampling]** Sampling in operator parameters.
`M_op² ≤ ‖ψ‖² ∫ (‖A‖²_{𝓛₂} + ‖b‖²) dp_op`. -/
theorem cor_operator_sampling_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) [IsFiniteMeasure Γop.variation]
    (hHS : ∀ᵐ q ∂Γop.variation, IsHilbertSchmidt q.1) :
    ∫⁻ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ₑ ^ 2 + ‖⟪ψ, q.2⟫‖ₑ ^ 2) ∂polarLaw Γop ≤
      ‖ψ‖ₑ ^ 2 * ∫⁻ q, (hsNormSq q.1 + ‖q.2‖ₑ ^ 2) ∂polarLaw Γop := by
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
  refine lintegral_mono_ae ?_
  have hHS' : ∀ᵐ q ∂polarLaw Γop, IsHilbertSchmidt q.1 := Measure.ae_smul_measure hHS _
  filter_upwards [hHS'] with q hq
  rw [mul_add]
  gcongr
  · have hA : ‖ContinuousLinearMap.adjoint q.1 ψ‖ ≤ hsNorm q.1 * ‖ψ‖ := by
      calc ‖ContinuousLinearMap.adjoint q.1 ψ‖
          ≤ ‖ContinuousLinearMap.adjoint q.1‖ * ‖ψ‖ := (ContinuousLinearMap.adjoint q.1).le_opNorm ψ
        _ = ‖q.1‖ * ‖ψ‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ hsNorm q.1 * ‖ψ‖ := by gcongr; exact opNorm_le_hsNorm hq
    have hsq : hsNormSq q.1 = ENNReal.ofReal (hsNorm q.1 ^ 2) := by
      rw [hsNorm, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hq]
    rw [hsq, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 ≤ (hsNorm q.1 * ‖ψ‖) ^ 2 := by gcongr
      _ = ‖ψ‖ ^ 2 * hsNorm q.1 ^ 2 := by ring
  · rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖⟪ψ, q.2⟫‖ ^ 2 ≤ (‖ψ‖ * ‖q.2‖) ^ 2 := by gcongr; exact norm_inner_le_norm ψ q.2
      _ = ‖ψ‖ ^ 2 * ‖q.2‖ ^ 2 := by ring

/-- **Corollary [cor:two-stage-error]** Input truncation and sampling are separate errors.  For
finite-rank orthogonal projections `Π_m` converging strongly to the identity, `f ∈ C(H)`, and
compact `K`, `‖f − f ∘ Π_m‖_{C(K)} → 0`. -/
theorem cor_two_stage_error_i [CompleteSpace H] (P : ℕ → (H →L[ℝ] H))
    (hP : ∀ m, IsFiniteRankProjection (P m))
    (hlim : ∀ x : H, Tendsto (fun m => P m x) atTop (𝓝 x)) {f : H → ℂ} (hf : Continuous f)
    {K : Set H} (hK : IsCompact K) :
    Tendsto (fun m => compactSupNorm K (fun x => f x - f (P m x))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcont : ∀ x : H, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε / 3 := fun x =>
    Metric.continuous_iff.mp hf x (ε / 3) (by positivity)
  choose δ hδpos hδ using hcont
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (δ x / 2))
    fun x _ => Metric.ball_mem_nhds x (by linarith [hδpos x])
  have hev : ∀ᶠ m in atTop, ∀ x ∈ t, dist (P m x) x < δ x / 2 := by
    rw [eventually_all_finset]
    intro x _
    exact Metric.tendsto_nhds.mp (hlim x) _ (by linarith [hδpos x])
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (compactSupNorm_nonneg _ _)]
  refine lt_of_le_of_lt (compactSupNorm_le (a := 2 * ε / 3) (by positivity) fun x hx => ?_)
    (by linarith)
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcover hx)
  rw [Metric.mem_ball] at hxi
  have h1 : dist (f x) (f i) < ε / 3 := hδ i x (by linarith [hδpos i])
  have h2 : dist (P m x) i < δ i := by
    calc dist (P m x) i ≤ dist (P m x) (P m i) + dist (P m i) i := dist_triangle _ _ _
      _ < δ i / 2 + δ i / 2 := by
          refine add_lt_add_of_le_of_lt ?_ (hM m hm i hi)
          rw [dist_eq_norm, ← map_sub]
          calc ‖P m (x - i)‖ ≤ ‖x - i‖ := (hP m).norm_apply_le _
            _ = dist x i := (dist_eq_norm x i).symm
            _ ≤ δ i / 2 := hxi.le
      _ = δ i := by ring
  have h3 : dist (f (P m x)) (f i) < ε / 3 := hδ i _ h2
  calc ‖f x - f (P m x)‖ = dist (f x) (f (P m x)) := (dist_eq_norm _ _).symm
    _ ≤ dist (f x) (f i) + dist (f i) (f (P m x)) := dist_triangle _ _ _
    _ ≤ ε / 3 + ε / 3 := by rw [dist_comm (f i)]; linarith
    _ = 2 * ε / 3 := by ring

/-- **Corollary [cor:two-stage-error]** Input truncation and sampling are separate errors.  If
`f = S_β Γ` satisfies the hypotheses of Theorem `thm:lipschitz-barron` and the same samples and
weights `(V/N) h(θ_j)` are used with the truncated directions `Π_m a_j` inside the activation,
`f_{m,N}(x) = (V/N) ∑_j h(θ_j) β(⟪Π_m a_j, x⟫ + c_j)`, then
`𝔼‖f − f_{m,N}‖_{C(K)} ≤ Lip(β) (∫ ‖a‖ d|Γ|) sup_K ‖x − Π_m x‖ +
(8V/√N)(|β(0)| + Lip(β) R_K M₂)`. -/
theorem cor_two_stage_error_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (P : ℕ → (H →L[ℝ] H)) (hP : ∀ m, IsFiniteRankProjection (P m))
    (hlim : ∀ x : H, Tendsto (fun m => P m x) atTop (𝓝 x)) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ∫ θ, compactSupNorm K (fun x =>
          integralNetwork (fun t => (β t : ℂ)) Γ x -
            finiteNetwork (fun t => (β t : ℂ))
              (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
              (fun j => P m (θ j).1) (fun j => (θ j).2) x)
        ∂sampleLaw N (polarLaw Γ) ≤
      (L : ℝ) * (∫ θ, ‖θ.1‖ ∂Γ.variation) * compactSupNorm K (fun x => x - P m x) +
        8 * polarWeight Γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
  have _hlim := hlim
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0,
      variation_eq_zero_of_totalVariation_eq_zero h0, integral_zero_measure]
    simp
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hV : 0 ≤ polarWeight Γ := polarWeight_nonneg Γ
  have hD0 : 0 ≤ compactSupNorm K (fun x => x - P m x) := compactSupNorm_nonneg _ _
  have hsa : IsSelfAdjoint (P m) := (hP m).isStarProjection.isSelfAdjoint
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ ≤ 1 :=
    (ae_polarLaw_norm_polarDensity_eq_one Γ).mono fun θ hθ => hθ.le
  -- `∫ ‖a‖ dp` and the expectation of `∑_j ‖a_j‖`
  have hint_a : Integrable (fun θ : H × ℝ => ‖θ.1‖) (polarLaw Γ) := by
    refine ((integrable_const 1).add hM).mono' measurable_fst.norm.aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    simp only [Pi.add_apply, norm_norm]
    nlinarith [sq_nonneg (‖θ.1‖ - 1), sq_nonneg |θ.2|]
  have hintj : ∀ j : Fin N,
      Integrable (fun θ : Fin N → H × ℝ => ‖(θ j).1‖) (sampleLaw N (polarLaw Γ)) := fun j =>
    (measurePreserving_eval (fun _ => polarLaw Γ) j).integrable_comp_of_integrable hint_a
  have hsum_int : Integrable (fun θ : Fin N → H × ℝ => ∑ j, ‖(θ j).1‖)
      (sampleLaw N (polarLaw Γ)) :=
    integrable_finsetSum Finset.univ fun j _ => hintj j
  have hsum_eq : ∫ θ, ∑ j, ‖(θ j).1‖ ∂sampleLaw N (polarLaw Γ) =
      N * ∫ θ, ‖θ.1‖ ∂polarLaw Γ := by
    rw [integral_finsetSum Finset.univ fun j _ => hintj j]
    simp_rw [sampleLaw, integral_eval_pi (polarLaw Γ) hint_a.aestronglyMeasurable]
    simp
  -- the sampling error of the untruncated network
  have herr_int : Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
      polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
        integralNetwork (fun t => (β t : ℂ)) Γ x)) (sampleLaw N (polarLaw Γ)) :=
    ((integrable_norm_sum_sub (polarLaw Γ) (integrable_polar_atom hK hβ Γ h0 hM) N).const_mul
      (polarWeight Γ / N)).congr (Eventually.of_forall fun θ =>
        (compactSupNorm_polarSampledNetwork_sub_eq hK hβ Γ h0 hM hN θ).symm)
  have herr_le := thm_lipschitz_barron_i hβ Γ hM hK hN
  -- the pointwise bound: sampling error plus truncation error
  have hpt : ∀ᵐ θ ∂sampleLaw N (polarLaw Γ),
      compactSupNorm K (fun x =>
        integralNetwork (fun t => (β t : ℂ)) Γ x -
          finiteNetwork (fun t => (β t : ℂ))
            (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
            (fun j => P m (θ j).1) (fun j => (θ j).2) x) ≤
      compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) +
        L * compactSupNorm K (fun x => x - P m x) * (polarWeight Γ / N * ∑ j, ‖(θ j).1‖) := by
    filter_upwards [ae_sampleLaw_forall (N := N) hh1] with θ hθ
    have herr0 : 0 ≤ compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) := compactSupNorm_nonneg _ _
    refine compactSupNorm_le (by positivity) fun x hx => ?_
    calc ‖integralNetwork (fun t => (β t : ℂ)) Γ x -
            finiteNetwork (fun t => (β t : ℂ))
              (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
              (fun j => P m (θ j).1) (fun j => (θ j).2) x‖
        = ‖(integralNetwork (fun t => (β t : ℂ)) Γ x -
              polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x) +
            (polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
              finiteNetwork (fun t => (β t : ℂ))
                (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
                (fun j => P m (θ j).1) (fun j => (θ j).2) x)‖ := by
          congr 1
          abel
      _ ≤ ‖integralNetwork (fun t => (β t : ℂ)) Γ x -
              polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x‖ +
            ‖polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
              finiteNetwork (fun t => (β t : ℂ))
                (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
                (fun j => P m (θ j).1) (fun j => (θ j).2) x‖ := norm_add_le _ _
      _ ≤ _ := by
          refine add_le_add ?_ ?_
          · rw [norm_sub_rev]
            exact norm_polarSampledNetwork_sub_le_compactSupNorm hK hβ Γ h0 hM hN θ hx
          · exact norm_sampledNetwork_sub_truncated_le hK hβ hsa hV (polarDensity Γ) θ hθ hx
  calc ∫ θ, compactSupNorm K (fun x =>
          integralNetwork (fun t => (β t : ℂ)) Γ x -
            finiteNetwork (fun t => (β t : ℂ))
              (fun j => ((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j))
              (fun j => P m (θ j).1) (fun j => (θ j).2) x) ∂sampleLaw N (polarLaw Γ)
      ≤ ∫ θ, (compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) +
          L * compactSupNorm K (fun x => x - P m x) *
            (polarWeight Γ / N * ∑ j, ‖(θ j).1‖)) ∂sampleLaw N (polarLaw Γ) :=
        integral_mono_of_nonneg (Eventually.of_forall fun θ => compactSupNorm_nonneg _ _)
          (herr_int.add ((hsum_int.const_mul _).const_mul _)) hpt
    _ = (∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) ∂sampleLaw N (polarLaw Γ)) +
          L * compactSupNorm K (fun x => x - P m x) *
            (polarWeight Γ / N * (N * ∫ θ, ‖θ.1‖ ∂polarLaw Γ)) := by
        rw [integral_add herr_int ((hsum_int.const_mul _).const_mul _), integral_const_mul,
          integral_const_mul, hsum_eq]
    _ ≤ 8 * polarWeight Γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) +
          L * compactSupNorm K (fun x => x - P m x) *
            (polarWeight Γ / N * (N * ∫ θ, ‖θ.1‖ ∂polarLaw Γ)) := add_le_add herr_le le_rfl
    _ = _ := by
        rw [integral_norm_fst_variation Γ h0, add_comm]
        field_simp

end OperatorRidgelet.Paper
