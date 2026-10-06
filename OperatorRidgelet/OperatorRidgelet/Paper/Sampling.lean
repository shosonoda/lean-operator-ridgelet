import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Sampling.Basic
import OperatorRidgelet.Sampling.Spectral
import OperatorRidgelet.Sampling.Universality
import OperatorRidgelet.Sampling.VectorConvergence
import OperatorRidgelet.Sampling.VectorBarron
import OperatorRidgelet.Sampling.FirstMoment
import OperatorRidgelet.Paper.Reconstruction

/-!
# Statements of Section 6 (finite-width approximation) and Appendix C

Each item is `theorem OperatorRidgelet.Paper.<kind>_<number>[_<part>]`, identical to its twin in
`Challenge.Sampling`, and proved from the library.

The probabilistic setup (the polar decomposition `Γ = h|Γ|`, `V = ‖Γ‖_TV`, `p = |Γ|/V`, the
product law of `N` independent samples, the Rademacher signs, the sampled network
`eq:polar-network`, the compact sup norm `‖·‖_{C(K)}`, `R_K`, and `M₂`) is documented in
`OperatorRidgelet.Sampling.Defs`.  Throughout, `Lip(β)` is any `L` with `LipschitzWith L β`,
and the width `N` is positive (for `N = 0` the manuscript's bounds `8V/√N` are void).

Theorems `thm:6.6` and `thm:6.8` are stated for the abstract direction measure `ν` used by the
supporting lemmas
(σ-finite, full support, homogeneous of degree `α`), as Theorem `thm:4.5` is in
`OperatorRidgelet.Paper.Reconstruction`, with the frequency window `I` of the band-pass filter
`ρ` explicit; the tempered activation `β` that is a continuous function `b` of polynomial
growth is the pair `(β, b)` with `IsTemperedFunction β b`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Section 6: approximation rates -/

/-- **Theorem [thm:6.3]** Compact-open approximation bound.  Whenever the
atoms `x ↦ h(θ) β(⟪a, x⟫ + c)` are measurable and integrably bounded in `C(K)` (they are the
values of a Bochner-integrable map `Φ : Θ → C(K)`), the sampled network of the polar
decomposition of `Γ` satisfies `𝔼‖f_N − f‖_{C(K)} ≤ 2V 𝔑_N(K; p, β)`. -/
theorem thm_6_3 [MeasurableSpace H] [BorelSpace H] (β : ℝ → ℂ)
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

/-- **Theorem [thm:6.5]** Dimension-free uniform Hilbert-valued Barron bound.  For a
finite-variation `Y`-valued measure `Γ = h|Γ|` with `V = ‖Γ‖_TV` and `p = |Γ|/V`, a real
globally Lipschitz `β`, and `M₂² = ∫ (‖a‖² + |c|²) dp < ∞`, the sampled network
`eq:polar-network` with `Y`-valued weights satisfies
`𝔼‖f_N − f‖_{C(K;Y)} ≤ (V/√N)(4|β(0)| + 8 Lip(β) R_K M₂)`.  The manuscript's conventions
`V = 0` (the zero network) and `K = ∅` (zero error) are instances of the statement. -/
theorem thm_6_5_i {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      polarWeight Γ / Real.sqrt N *
        (4 * |β 0| + 8 * (L : ℝ) * compactRadius K *
          Real.sqrt (secondMoment (polarLaw Γ))) := by
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0]
    simp
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hu : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  calc ∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) ∂sampleLaw N (polarLaw Γ)
      ≤ 2 * polarWeight Γ *
          rademacherComplexity N K (polarLaw Γ) (fun t => (β t : ℂ)) (polarDensity Γ) :=
        integral_polarSampledNetwork_compact_le (lipschitzWith_ofReal_comp hβ) Γ hM hK hN
    _ ≤ 2 * polarWeight Γ *
          ((2 * |β 0| + 4 * (L : ℝ) * compactRadius K *
            Real.sqrt (secondMoment (polarLaw Γ))) / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left
          (rademacherComplexity_vectorRidge_le hK hβ (polarLaw Γ) (polarDensity Γ) hh
            (hu.mono fun _ hθ => hθ.le) hM hN)
          (by linarith [polarWeight_nonneg Γ])
    _ = polarWeight Γ / Real.sqrt N *
          (4 * |β 0| + 8 * (L : ℝ) * compactRadius K *
            Real.sqrt (secondMoment (polarLaw Γ))) := by ring

/-- **Theorem [thm:6.5]** Dimension-free uniform Hilbert-valued Barron bound.  At
least one deterministic width-`N` realization satisfies the same bound
`‖f_N − f‖_{C(K;Y)} ≤ (V/√N)(4|β(0)| + 8 Lip(β) R_K M₂)`. -/
theorem thm_6_5_ii {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∃ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x) ≤
        polarWeight Γ / Real.sqrt N *
          (4 * |β 0| + 8 * (L : ℝ) * compactRadius K *
            Real.sqrt (secondMoment (polarLaw Γ))) := by
  by_cases h0 : totalVariation Γ = 0
  · refine ⟨fun _ => (0, 0), ?_⟩
    rw [polarWeight_eq_zero_of_totalVariation_eq_zero h0]
    refine le_of_le_of_eq (compactSupNorm_le le_rfl fun x _ => ?_) (by simp)
    rw [polarSampledNetwork_eq_zero _ h0, integralNetwork_eq_zero_of_totalVariation_eq_zero _ h0,
      sub_zero, norm_zero]
  haveI := isProbabilityMeasure_polarLaw Γ h0
  obtain ⟨θ, hθ⟩ := exists_realization_le_mean _ _
    (integrable_compactSupNorm_polarSampledNetwork_sub_vec hK hβ Γ hM hN)
  exact ⟨θ, hθ.trans (thm_6_5_i hβ Γ hM hK hN)⟩

/-- **Theorem [thm:6.5]** Dimension-free uniform Hilbert-valued Barron bound, in the
weaker form `𝔼‖f_N − f‖_{C(K;Y)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂)` of the second displayed
inequality. -/
theorem thm_6_5_iii {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
            integralNetwork (fun t => (β t : ℂ)) Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      8 * polarWeight Γ / Real.sqrt N *
        (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) := by
  refine (thm_6_5_i hβ Γ hM hK hN).trans ?_
  have hV : 0 ≤ polarWeight Γ / Real.sqrt N :=
    div_nonneg (polarWeight_nonneg Γ) (Real.sqrt_nonneg _)
  have hb : 0 ≤ |β 0| := abs_nonneg _
  have hdiff : 8 * polarWeight Γ / Real.sqrt N *
        (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (polarLaw Γ))) -
      polarWeight Γ / Real.sqrt N *
        (4 * |β 0| + 8 * (L : ℝ) * compactRadius K *
          Real.sqrt (secondMoment (polarLaw Γ))) =
      polarWeight Γ / Real.sqrt N * (4 * |β 0|) := by ring
  have hpos : 0 ≤ polarWeight Γ / Real.sqrt N * (4 * |β 0|) :=
    mul_nonneg hV (by linarith)
  linarith


/-! ## Section 6: finite total variation from the spectral density -/

section Spectral

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- **Theorem [thm:6.6]** Finite total variation and moments of the coefficient measure.  For a
band-pass `ρ`
with frequency window `I` there is a finite constant `c_ρ`, depending only on `ρ` and `α`,
such that every `G` regular along rays satisfies
`∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α ≤ c_ρ M₄(G)`. -/
theorem thm_6_6_i (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
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

/-- **Theorem [thm:6.6]** Finite total variation and moments of the coefficient measure.  For `G`
regular along
rays, `∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α < ∞`: the coefficient measure `γ_G λ_α` is finite with
finite second moment. -/
theorem thm_6_6_ii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
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

/-- **Theorem [thm:6.6]** Finite total variation and moments of the coefficient measure.
Consequently, for every
real `β` that is globally Lipschitz (a tempered activation that is the
function `b`), the target `C^{(α)}_{β,ρ} g_G` is the integral network `S_β[γ_G λ_α]`. -/
theorem thm_6_6_iii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) {L : ℝ≥0} (hb : LipschitzWith L b)
    (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
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
  rw [← thm_4_5_iii_c ν hα hν ρ hρ I hI β b hβ G hG x, integralNetworkDensity,
    parameterMeasure, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  show coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ) =
    (b (⟪a, x⟫ + c) : ℂ) * coefficientFormula ρ G (a, c)
  ring

/-- **Theorem [thm:6.6]** Finite total variation and moments of the coefficient measure.  For real
globally
Lipschitz `β`, the sampled network `eq:polar-network` of `γ_G λ_α`, with
`V = ‖γ_G‖_{L¹(λ_α)}` and `M₂` the second moment of `p = |γ_G| λ_α / V`, satisfies
`𝔼‖f_N − C^{(α)}_{β,ρ} g_G‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂)` for every compact
`K`. -/
theorem thm_6_6_iv (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) {L : ℝ≥0} (hb : LipschitzWith L b)
    (G : H → ℂ) (hG : IsRegularAlongRays ν I G) {K : Set H}
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
      rw [thm_6_6_iii ν hα hν ρ hρ I hI β b hβ hb G hG x]
  rw [integral_congr_ae (Eventually.of_forall hcongr)]
  exact integral_compactSupNorm_densitySampledNetwork_sub_le hK hb hγ hM hN

/-! ## Section 6: constructive universal approximation -/

/-- **Theorem [thm:6.8]** Constructive universal approximation with approximation rates.  For a
continuous,
polynomially growing, non-polynomial real `β` (the function `b` of the tempered `β`), a
band-pass `ρ` with `C^{(α)}_{β,ρ} = 1`, a continuous `f : H → ℂ`, a compact `K`, and `ε > 0`,
there is a spectral density `G`, regular along rays, smooth, and vanishing outside a bounded
set, such that (i) `‖f − g_G‖_{C(K)} < ε`; (ii) `g_G = S_β[γ_G λ_α]` with a coefficient
measure `γ_G λ_α` that is finite with finite moments of all orders; (iii) if `β` is globally
Lipschitz, the sampled network of `γ_G λ_α` satisfies
`𝔼‖f − f_N‖_{C(K)} ≤ ε + (8V/√N)(|β(0)| + Lip(β) R_K M₂)` with `V = ‖γ_G‖_{L¹(λ_α)}` and
`M₂` the second moment of `|γ_G| λ_α / V`, and at least one deterministic width-`N` network
satisfies the same bound.  The direction measure is assumed finite on bounded sets (`hfin`),
which Lemma `lem:3.2` supplies for the Gaussian mixture `ν_α` in infinite
dimension and which the manuscript uses throughout, since it states the theorem for `ν_α`
only; the abstract hypotheses (σ-finite, full support, homogeneous of degree `α > 0`) do not
imply it, so `hfin` is retained explicitly in the Lean statement. -/
theorem thm_6_8 (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (hfin : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
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
  -- Stone--Weierstrass for the characters, the normalized radial bumps of `bumpDensity`,
  -- Theorem `thm:4.5`(iii) with `C^{(α)}_{β,ρ} = 1`, the moments of all orders of Theorem
  -- `thm:6.6`, and the Barron bound of Theorem `thm:6.5`.  The hypothesis `hfin`
  -- is Step 2 in the proof of Theorem 6.8 (full support and finite mass on bounded sets): the
  -- normalization of a radial bump needs `ν (closedBall 0 R) < ⊤`.
  exact exists_spectralDensity_universal_approx ν hfin hν β b hβ ρ hρ hC I hI hf hK hε

/-- **Theorem [thm:6.8]** Constructive universal approximation with approximation rates.
In particular, under the hypotheses of the theorem, the finite-width networks with the continuous,
polynomially
growing, non-polynomial real activation `β` are dense in `C(H)` for the compact-open topology:
every continuous `f : H → ℂ` is approximated within `ε` on every compact `K` by a network of
some finite width `N`.  The manuscript states the sentence inside Theorem `thm:6.8`, under all
of its hypotheses, and derives it from (ii) together with Lemma `lem:6.7`
(from (iii) when `β` is in addition globally Lipschitz); the Lean statement therefore carries
the hypotheses of `thm_6_8`, including `hfin`. -/
theorem thm_6_8_dense (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (hfin : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hpoly : ¬ IsPolynomialFun b) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) {f : H → ℂ} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → ℂ) (a : Fin N → H) (c : Fin N → ℝ),
      compactSupNorm K (fun x => f x - finiteNetwork (fun t => (b t : ℂ)) v a c x) < ε := by
  -- Theorem `thm:6.8` with `ε/2` supplies the spectral density `G` and its coefficient measure
  obtain ⟨G, hGreg, -, hGsupp, hGapp, hgeq, hmom, -⟩ :=
    thm_6_8 ν hα hν hfin β b hβ hpoly ρ hρ hC I hI hf hK (half_pos hε)
  have hbC : Continuous fun t => (b t : ℂ) := Complex.continuous_ofReal.comp hβ.continuous
  -- `G` is bounded and vanishes outside a ball of finite `ν`-mass, so `g_G` is continuous
  have hGint : Integrable G ν := by
    obtain ⟨M, hM⟩ := hGreg.bounded
    obtain ⟨R, hR⟩ := hGsupp
    refine ⟨hGreg.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hle : ∀ ξ : H, ‖G ξ‖ₑ ≤
        (Metric.closedBall (0 : H) R).indicator (fun _ => ENNReal.ofReal M) ξ := fun ξ => by
      by_cases hξ : ξ ∈ Metric.closedBall (0 : H) R
      · rw [Set.indicator_of_mem hξ, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hM ξ)
      · rw [Set.indicator_of_notMem hξ,
          hR ξ (by simpa [Metric.mem_closedBall, dist_zero_right] using hξ)]
        simp
    calc ∫⁻ ξ, ‖G ξ‖ₑ ∂ν
        ≤ ∫⁻ ξ, (Metric.closedBall (0 : H) R).indicator (fun _ => ENNReal.ofReal M) ξ ∂ν :=
          lintegral_mono hle
      _ = ENNReal.ofReal M * ν (Metric.closedBall (0 : H) R) :=
          lintegral_indicator_const measurableSet_closedBall _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin R)
  have hgc : Continuous (spectralTarget ν G) := continuous_spectralTarget ν hGint
  -- the coefficient measure `Γ = γ_G λ_α` is finite and its integral network is `g_G`
  have hγ : Integrable (coefficientFormula ρ G) (parameterMeasure ν) :=
    coefficientFormulaVec_eq_coefficientFormula' ρ G ▸
      integrable_coefficientFormulaVec hρ hI hGreg
  haveI : IsFiniteMeasure
      ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)).variation :=
    isFiniteMeasure_variation_withDensityᵥ hγ
  have hΓnet : ∀ x : H, integralNetwork (fun t => (b t : ℂ))
      ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x = spectralTarget ν G x := by
    intro x
    have hint : Integrable (fun θ : H × ℝ =>
        (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ) (parameterMeasure ν) := by
      rw [parameterMeasure]
      refine (integrable_prod_smul_coefficientFormulaVec hρ hI hGreg hβ.continuous
        hβ.polynomialGrowth x).congr (Eventually.of_forall fun θ => ?_)
      show (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G (θ.1, θ.2) =
        (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ
      rw [Prod.mk.eta, coefficientFormulaVec_eq_coefficientFormula]
    rw [integralNetwork_withDensityᵥ hbC _ hγ hint, ← hgeq]
  -- Lemma `lem:6.7` discretizes `Γ` within `ε/2` in `C(K)`
  obtain ⟨n, w, θ, hlt⟩ := exists_atomicMeasure_compactSupNorm_integralNetwork_sub_lt hbC
    ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) hK
    (integrable_compactSupNorm_ridge_variation_withDensityᵥ hK hβ.continuous
      hβ.polynomialGrowth hγ hmom) (half_pos hε)
  refine ⟨n, w, fun j => (θ j).1, fun j => (θ j).2, ?_⟩
  have hatom : ∀ x : H,
      finiteNetwork (fun t => (b t : ℂ)) w (fun j => (θ j).1) (fun j => (θ j).2) x =
        integralNetwork (fun t => (b t : ℂ)) (atomicMeasure w θ) x := fun x =>
    (integralNetwork_atomicMeasure (fun t => (b t : ℂ)) w θ x).symm
  have hcontA : Continuous fun x : H =>
      integralNetwork (fun t => (b t : ℂ)) (atomicMeasure w θ) x := by
    have hfun : (fun x : H => integralNetwork (fun t => (b t : ℂ)) (atomicMeasure w θ) x) =
        fun x : H => ∑ j, (b (⟪(θ j).1, x⟫ + (θ j).2) : ℂ) • w j :=
      funext fun x => integralNetwork_atomicMeasure (fun t => (b t : ℂ)) w θ x
    rw [hfun]
    have hbc : Continuous b := hβ.continuous
    fun_prop
  have hcontB : Continuous fun x : H => integralNetwork (fun t => (b t : ℂ))
      ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x := by
    have hfun : (fun x : H => integralNetwork (fun t => (b t : ℂ))
        ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x) =
        spectralTarget ν G := funext hΓnet
    rw [hfun]
    exact hgc
  have hbdd1 : BddAbove ((fun x => ‖f x - spectralTarget ν G x‖) '' K) :=
    (hK.image (hf.sub hgc).norm).bddAbove
  have hbdd2 : BddAbove ((fun x => ‖integralNetwork (fun t => (b t : ℂ)) (atomicMeasure w θ) x -
      integralNetwork (fun t => (b t : ℂ))
        ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x‖) '' K) :=
    (hK.image (hcontA.sub hcontB).norm).bddAbove
  -- the triangle inequality on `K`
  have key : ∀ x ∈ K, ‖f x - finiteNetwork (fun t => (b t : ℂ)) w (fun j => (θ j).1)
      (fun j => (θ j).2) x‖ ≤
      compactSupNorm K (fun x => f x - spectralTarget ν G x) +
        compactSupNorm K (fun x => integralNetwork (fun t => (b t : ℂ)) (atomicMeasure w θ) x -
          integralNetwork (fun t => (b t : ℂ))
            ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x) := by
    intro x hx
    rw [hatom x, ← sub_add_sub_cancel (f x) (integralNetwork (fun t => (b t : ℂ))
      ((parameterMeasure ν).withDensityᵥ (coefficientFormula ρ G)) x)]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [hΓnet x]
      exact le_csSup hbdd1 ⟨x, hx, rfl⟩
    · rw [norm_sub_rev]
      exact le_csSup hbdd2 ⟨x, hx, rfl⟩
  exact lt_of_le_of_lt (compactSupNorm_le
    (add_nonneg (compactSupNorm_nonneg _ _) (compactSupNorm_nonneg _ _)) key) (by linarith)

/-- **Theorem [thm:6.8]** Constructive universal approximation with approximation rates.  The same
statements
hold for continuous `f : H → Y` with values in a separable complex Hilbert space: there is a
`Y`-valued spectral density `G`, regular along rays, smooth, and vanishing outside a bounded
set, with (i) `‖f − g_G‖_{C(K;Y)} < ε`, (ii) `g_G = S_β[γ_G λ_α]` with a finite coefficient
measure with finite moments of all orders, and (iii), for globally Lipschitz `β`, the same
explicit rate `𝔼‖f − f_N‖_{C(K;Y)} ≤ ε + (8V/√N)(|β(0)| + Lip(β) R_K M₂)` as in the scalar
case, by the Hilbert-valued Theorem `thm:6.5`, together with a deterministic
width-`N` realization.  As in `thm_6_8`, the direction measure is assumed finite on bounded sets
(`hfin`). -/
theorem thm_6_8_vec {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [SecondCountableTopology Y] (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hfin : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤) (β : TemperedDistribution ℝ ℂ)
    (b : ℝ → ℝ) (hβ : IsTemperedFunction β b) (hpoly : ¬ IsPolynomialFun b)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (hC : temperedAdmissibilityConst α β ρ = 1)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) {f : H → Y} (hf : Continuous f) {K : Set H}
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
        (∫ θ, compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) ≤
          ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormulaVec ρ G) / Real.sqrt N *
            (|b 0| + (L : ℝ) * compactRadius K *
              Real.sqrt
                (secondMoment
                  (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))))) ∧
        ∃ θ : Fin N → H × ℝ,
          compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x) ≤
            ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormulaVec ρ G) /
                Real.sqrt N *
              (|b 0| + (L : ℝ) * compactRadius K *
                Real.sqrt
                  (secondMoment
                    (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))))) := by
  -- Step 1 in the vector-valued case is `exists_character_approx_vec`: the compact set of
  -- values `f(K)` is covered by finitely many `ε`-balls whose bumps normalize into a partition
  -- of unity on `K`, which reduces `f` to a finite combination `∑ g_k • y_k` of continuous
  -- scalar functions with constant weights in `Y`, and Stone--Weierstrass over the characters
  -- (`exists_character_approx_continuousMap`) approximates each `g_k`.  Step 2 keeps the
  -- normalized radial bumps `bumpDensity` scalar and attaches the weights `w_i ∈ Y` afterwards,
  -- so `IsRegularAlongRays.finset_sum_smul` needs the ray-derivative measurability only for the
  -- `ℂ`-valued summands.  Steps 3--4 are the `Y`-valued moment bounds of `thm:6.6` and the
  -- vector-valued Rademacher bound `2V 𝔑^Y_N(K; p, β)` of `cor:6.10`(ii) for a
  -- coefficient measure with a density. The hypothesis `hfin` is Step 2 in the proof of
  -- Theorem 6.8, as
  -- in `thm_6_8`.
  exact exists_spectralDensity_universal_approx_vec ν hfin hν β b hβ ρ hρ hC I hI hf hK hε

end Spectral

/-! ## Section 6: vector-valued approximation -/

section VectorValued

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

/-- **Corollary [cor:6.10]** Vector-valued rates.  For globally Lipschitz `β`, a
`Y`-valued `Γ` whose law `p = |Γ|/V` has finite second moment, and every Borel probability
measure `ζ` on `H` with `∫ ‖x‖² dζ < ∞`,
`𝔼‖f_N − f‖²_{L²(ζ;Y)} ≤ (V²/N) ∫ ‖β(⟪a,·⟫ + c)‖²_{L²(ζ)} dp`. -/
theorem cor_6_10_i_a [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) {N : ℕ} (hN : 0 < N) :
    ∫ θ, (∫ x, ‖polarSampledNetwork β Γ θ x - integralNetwork β Γ x‖ ^ 2 ∂ζ)
        ∂sampleLaw N (polarLaw Γ) ≤
      polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ := by
  exact integral_polarSampledNetwork_sq_le hβ Γ hM ζ hζ hN

/-- **Corollary [cor:6.10]** Vector-valued rates.  The `L²(ζ;Y)` rate is explicit:
`(V²/N) ∫ ‖β(⟪a,·⟫ + c)‖²_{L²(ζ)} dp ≤ (2V²/N)(|β(0)|² + Lip(β)² (1 + ∫ ‖x‖² dζ) M₂²)`. -/
theorem cor_6_10_i_b [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) {N : ℕ} (hN : 0 < N) :
    polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ ≤
      2 * polarWeight Γ ^ 2 / N *
        (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * secondMoment (polarLaw Γ)) := by
  by_cases h0 : totalVariation Γ = 0
  · simp [polarWeight_eq_zero_of_totalVariation_eq_zero h0]
  · letI := isProbabilityMeasure_polarLaw Γ h0
    have h := mul_le_mul_of_nonneg_left
      (integral_integral_norm_ridge_sq_le hβ (polarLaw Γ) hM ζ hζ)
      (show 0 ≤ polarWeight Γ ^ 2 / (N : ℝ) by positivity)
    exact h.trans_eq (by ring)

/-- **Corollary [cor:6.10]** Vector-valued rates.  For every compact `K`,
`𝔼‖f_N − f‖_{C(K;Y)} ≤ 2V 𝔑^Y_N(K; p, β)`, where `𝔑^Y_N` is the Rademacher complexity with the
absolute value replaced by the norm of `Y`. -/
theorem cor_6_10_ii_a [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      2 * polarWeight Γ * rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ) := by
  exact integral_polarSampledNetwork_compact_le_firstMoment hβ Γ hM hK hN

/-- **Corollary [cor:6.10]** Vector-valued rates.  For every compact `K`,
`𝔑^Y_N(K; p, β) → 0` as `N → ∞`. -/
theorem cor_6_10_ii_b [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) :
    Tendsto (fun N : ℕ => rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ)) atTop
      (𝓝 0) := by
  exact tendsto_rademacherComplexity_vector_firstMoment hβ Γ hM hK

end VectorValued

/-! ## Section 6 and Appendix C: supplementary approximation results -/

/-- **Lemma [lem:6.7]** Qualitative finite-atomic approximation.  For
continuous `β`, compact `K`, and `∫ ‖β(⟪a,·⟫ + c)‖_{C(K)} d|Γ| < ∞`, for every `ε > 0` there
is a finite atomic complex measure `Γ_ε = ∑_j w_j δ_{θ_j}` with
`‖S_β Γ_ε − S_β Γ‖_{C(K)} < ε`. -/
theorem lem_6_7 [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ}
    (hβ : Continuous β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation] {K : Set H}
    (hK : IsCompact K)
    (hint : Integrable (fun θ : H × ℝ => compactSupNorm K fun x => β (⟪θ.1, x⟫ + θ.2))
      Γ.variation)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℂ) (θ : Fin n → H × ℝ),
      compactSupNorm K
        (fun x => integralNetwork β (atomicMeasure w θ) x - integralNetwork β Γ x) < ε :=
  exists_atomicMeasure_compactSupNorm_integralNetwork_sub_lt hβ Γ hK hint hε

/-- **Corollary [cor:C.1]** Concentration for bounded parameters.  Under the
hypotheses of Theorem `thm:6.5`, if `‖a‖² + |c|² ≤ B²` almost surely for some
`B ≥ 0` and `M_K = |β(0)| + Lip(β) R_K B`, then with probability at least `1 − δ`,
`‖f_N − f‖_{C(K)} ≤ (8V/√N)(|β(0)| + Lip(β) R_K M₂) + V M_K √(2 log(1/δ)/N)`. -/
theorem cor_C_1 [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0}
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
  have hErr := integral_compactSupNorm_polarSampledNetwork_sub_le hβ Γ hM hK hN
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
/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
For `Y ∈ L²(p; X)` with values in a separable Hilbert space, independent copies `Y_j`, `f = V 𝔼Y`,
and
`f_N = V N⁻¹ ∑_j Y_j`: `𝔼‖f_N − f‖² = (V²/N)(𝔼‖Y‖² − ‖𝔼Y‖²)`. -/
theorem lem_6_9_i (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p =
      V ^ 2 / N * ((∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖∫ ω', Y ω' ∂p‖ ^ 2) :=
  integral_norm_sq_sampleMean p hY V hN

/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
`𝔼‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_6_9_ii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p ≤
      V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  rw [lem_6_9_i p hY V hN]
  have h1 : 0 ≤ V ^ 2 / N := by positivity
  have h2 : 0 ≤ ‖∫ ω', Y ω' ∂p‖ ^ 2 := by positivity
  nlinarith

/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
A deterministic sample satisfies the same upper bound `‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_6_9_iii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ ω : Fin N → Ω,
      ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ≤ V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  have hL : MemLp (fun ω : Fin N → Ω => (V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p) 2
      (sampleLaw N p) :=
    ((memLp_finsetSum Finset.univ fun j _ => memLp_eval_pi p hY j).const_smul
      (V / N : ℝ)).sub ((memLp_const _).const_smul V)
  obtain ⟨ω, hω⟩ := exists_le_integral ((memLp_two_iff_integrable_sq_norm hL.1).mp hL)
  exact ⟨ω, hω.trans (lem_6_9_ii p hY V hN)⟩

end Hilbert

/-- **Corollary [cor:C.2]** Input truncation and finite-width approximation errors.  For
finite-rank orthogonal projections `Π_m` converging strongly to the identity, `f ∈ C(H)`, and
compact `K`, `‖f − f ∘ Π_m‖_{C(K)} → 0`. -/
theorem cor_C_2_i [CompleteSpace H] (P : ℕ → (H →L[ℝ] H))
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

/-- **Corollary [cor:C.2]** Input truncation and finite-width approximation errors.  If
`f = S_β Γ` satisfies the hypotheses of Theorem `thm:6.5` and the same samples and
weights `(V/N) h(θ_j)` are used with the truncated directions `Π_m a_j` inside the activation,
`f_{m,N}(x) = (V/N) ∑_j h(θ_j) β(⟪Π_m a_j, x⟫ + c_j)`, then
`𝔼‖f − f_{m,N}‖_{C(K)} ≤ Lip(β) (∫ ‖a‖ d|Γ|) sup_K ‖x − Π_m x‖ +
(8V/√N)(|β(0)| + Lip(β) R_K M₂)`. -/
theorem cor_C_2_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
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
  -- the approximation error of the untruncated network
  have herr_int : Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
      polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
        integralNetwork (fun t => (β t : ℂ)) Γ x)) (sampleLaw N (polarLaw Γ)) :=
    ((integrable_norm_sum_sub (polarLaw Γ) (integrable_polar_atom hK hβ Γ h0 hM) N).const_mul
      (polarWeight Γ / N)).congr (Eventually.of_forall fun θ =>
        (compactSupNorm_polarSampledNetwork_sub_eq hK hβ Γ h0 hM hN θ).symm)
  have herr_le := integral_compactSupNorm_polarSampledNetwork_sub_le hβ Γ hM hK hN
  -- the pointwise bound: approximation error plus truncation error
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
