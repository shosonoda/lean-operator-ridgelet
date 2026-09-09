import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Const

/-!
# comparator challenge: Section 6 (finite-width approximation) and Appendix D

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Sampling`.  This module
imports only definition modules, never `OperatorRidgelet.Paper`.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Theorem [thm:E]** Finite variation and moments of the coefficient.  For `G` regular along
rays, `∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α < ∞`: the coefficient measure `γ_G λ_α` is finite with
finite second moment. -/
theorem thm_E_ii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖)
      (parameterMeasure ν) := by
  sorry

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
  sorry

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
  sorry

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
satisfies the same bound.  The direction measure is assumed finite on bounded sets (`hfin`),
which Lemma `lem:homogeneous-mixture` supplies for the Gaussian mixture `ν_α` in infinite
dimension and which the manuscript uses throughout, since it states the theorem for `ν_α`
only; the abstract hypotheses (σ-finite, full support, homogeneous of degree `α > 0`) do not
imply it, and Theorem `thm:general-weights` deliberately does not extend `thm:D` to abstract
weights. -/
theorem thm_D (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
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
`cor:vector-rates`.  As in `thm_D`, the direction measure is assumed finite on bounded sets
(`hfin`). -/
theorem thm_D_vec {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
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
  sorry

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
  sorry

section Hilbert

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]

/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.  For `Y ∈ L²(p; X)` with
values in a separable Hilbert space, independent copies `Y_j`, `f = V 𝔼Y`, and
`f_N = V N⁻¹ ∑_j Y_j`: `𝔼‖f_N − f‖² = (V²/N)(𝔼‖Y‖² − ‖𝔼Y‖²)`. -/
theorem lem_hilbert_sampling_i (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p =
      V ^ 2 / N * ((∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖∫ ω', Y ω' ∂p‖ ^ 2) := by
  sorry

/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.
`𝔼‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_hilbert_sampling_ii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p ≤
      V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  sorry

/-- **Lemma [lem:hilbert-sampling]** Hilbert-valued sampling identity.  A deterministic sample
satisfies the same upper bound `‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_hilbert_sampling_iii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ ω : Fin N → Ω,
      ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ≤ V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  sorry

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
  sorry

/-- **Corollary [cor:operator-sampling]** Sampling in operator parameters.
`M_op² ≤ ‖ψ‖² ∫ (‖A‖²_{𝓛₂} + ‖b‖²) dp_op`. -/
theorem cor_operator_sampling_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) [IsFiniteMeasure Γop.variation]
    (hHS : ∀ᵐ q ∂Γop.variation, IsHilbertSchmidt q.1) :
    ∫⁻ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ₑ ^ 2 + ‖⟪ψ, q.2⟫‖ₑ ^ 2) ∂polarLaw Γop ≤
      ‖ψ‖ₑ ^ 2 * ∫⁻ q, (hsNormSq q.1 + ‖q.2‖ₑ ^ 2) ∂polarLaw Γop := by
  sorry

/-- **Corollary [cor:two-stage-error]** Input truncation and sampling are separate errors.  For
finite-rank orthogonal projections `Π_m` converging strongly to the identity, `f ∈ C(H)`, and
compact `K`, `‖f − f ∘ Π_m‖_{C(K)} → 0`. -/
theorem cor_two_stage_error_i [CompleteSpace H] (P : ℕ → (H →L[ℝ] H))
    (hP : ∀ m, IsFiniteRankProjection (P m))
    (hlim : ∀ x : H, Tendsto (fun m => P m x) atTop (𝓝 x)) {f : H → ℂ} (hf : Continuous f)
    {K : Set H} (hK : IsCompact K) :
    Tendsto (fun m => compactSupNorm K (fun x => f x - f (P m x))) atTop (𝓝 0) := by
  sorry

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
  sorry

end OperatorRidgelet.Paper
