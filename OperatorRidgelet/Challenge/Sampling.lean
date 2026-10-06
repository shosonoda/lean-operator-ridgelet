import Mathlib.MeasureTheory.Measure.Complex
import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Const

/-!
# comparator challenge: Section 6 (finite-width approximation) and Appendix C

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Sampling`.  This module
imports only definition modules, never `OperatorRidgelet.Paper`.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-! ## Section 6: finite total variation from the spectral density -/

section Spectral

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
  sorry

/-- **Theorem [thm:6.6]** Finite total variation and moments of the coefficient measure.  For `G`
regular along
rays, `∫ (1 + ‖a‖² + |c|²) |γ_G| dλ_α < ∞`: the coefficient measure `γ_G λ_α` is finite with
finite second moment. -/
theorem thm_6_6_ii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormula ρ G θ‖)
      (parameterMeasure ν) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Corollary [cor:6.10]** Vector-valued rates.  The `L²(ζ;Y)` rate is explicit:
`(V²/N) ∫ ‖β(⟪a,·⟫ + c)‖²_{L²(ζ)} dp ≤ (2V²/N)(|β(0)|² + Lip(β)² (1 + ∫ ‖x‖² dζ) M₂²)`. -/
theorem cor_6_10_i_b [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) {N : ℕ} (hN : 0 < N) :
    polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ ≤
      2 * polarWeight Γ ^ 2 / N *
        (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * secondMoment (polarLaw Γ)) := by
  sorry

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
  sorry

/-- **Corollary [cor:6.10]** Vector-valued rates.  For every compact `K`,
`𝔑^Y_N(K; p, β) → 0` as `N → ∞`. -/
theorem cor_6_10_ii_b [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) (polarLaw Γ)) {K : Set H}
    (hK : IsCompact K) :
    Tendsto (fun N : ℕ => rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ)) atTop
      (𝓝 0) := by
  sorry

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
        (fun x => integralNetwork β (atomicMeasure w θ) x - integralNetwork β Γ x) < ε := by
  sorry

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
  sorry

section Hilbert

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]

/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
For `Y ∈ L²(p; X)` with values in a separable Hilbert space, independent copies `Y_j`, `f = V 𝔼Y`,
and
`f_N = V N⁻¹ ∑_j Y_j`: `𝔼‖f_N − f‖² = (V²/N)(𝔼‖Y‖² − ‖𝔼Y‖²)`. -/
theorem lem_6_9_i (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p =
      V ^ 2 / N * ((∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖∫ ω', Y ω' ∂p‖ ^ 2) := by
  sorry

/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
`𝔼‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_6_9_ii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂sampleLaw N p ≤
      V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  sorry

/-- **Lemma [lem:6.9]** Mean-square error identity for Hilbert-valued averages.
A deterministic sample satisfies the same upper bound `‖f_N − f‖² ≤ (V²/N) 𝔼‖Y‖²`. -/
theorem lem_6_9_iii (p : Measure Ω) [IsProbabilityMeasure p] {Y : Ω → X}
    (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ ω : Fin N → Ω,
      ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ≤ V ^ 2 / N * ∫ ω', ‖Y ω'‖ ^ 2 ∂p := by
  sorry

end Hilbert

/-- **Corollary [cor:C.2]** Input truncation and finite-width approximation errors.  For
finite-rank orthogonal projections `Π_m` converging strongly to the identity, `f ∈ C(H)`, and
compact `K`, `‖f − f ∘ Π_m‖_{C(K)} → 0`. -/
theorem cor_C_2_i [CompleteSpace H] (P : ℕ → (H →L[ℝ] H))
    (hP : ∀ m, IsFiniteRankProjection (P m))
    (hlim : ∀ x : H, Tendsto (fun m => P m x) atTop (𝓝 x)) {f : H → ℂ} (hf : Continuous f)
    {K : Set H} (hK : IsCompact K) :
    Tendsto (fun m => compactSupNorm K (fun x => f x - f (P m x))) atTop (𝓝 0) := by
  sorry

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
  sorry

end OperatorRidgelet.Paper
