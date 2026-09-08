import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Architecture.Defs

/-!
# comparator challenge: Section 2 (networks with Hilbert-space inputs) and Appendix F (operator-valued parameters)

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Networks`.  This module
imports only definition modules, never `OperatorRidgelet.Paper`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Topology
open scoped ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Section 2: integral networks -/

/-- **Definition [def:integral-network]** Integral network.  If `β` is globally Lipschitz and
`∫ (1 + ‖a‖ + |c|) d|Γ| < ∞`, then the Bochner integral defining `S_β[Γ](x)` exists for every
`x`. -/
theorem def_integral_network_i [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hmom : Integrable (fun θ : H × ℝ => 1 + ‖θ.1‖ + |θ.2|) Γ.variation) (x : H) :
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) := by
  sorry

/-- **Definition [def:integral-network]** Integral network.  For `Γ = γ λ` with a density `γ`
with respect to a σ-finite reference measure `λ`, the integral network `S_β[Γ]` is the Bochner
integral `S_β[γ](x) = ∫ β(⟪a, x⟫ + c) γ(a, c) λ(da, dc)`, whenever the latter exists. -/
theorem def_integral_network_ii [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ}
    (hβ : Continuous β) (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (x : H)
    (hint : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) • γ θ) lam) :
    integralNetwork β (lam.withDensityᵥ γ) x = integralNetworkDensity β lam γ x := by
  sorry

/-! ## Appendix F: Hilbert–Schmidt reduction and the rank-one lift -/

/-- **Lemma [lem:hs-reduction]** Hilbert–Schmidt reduction.  For globally Lipschitz `σ`, the
spans of the operator neurons with `A ∈ 𝓛(H)` and with `A ∈ 𝓛₂(H)` have the same compact-open
closure in `C(H; ℝ)`. -/
theorem lem_hs_reduction [CompleteSpace H] [SecondCountableTopology H] {σ : H → H} {L : ℝ≥0}
    (hσ : LipschitzWith L σ) :
    closure (Submodule.span ℝ (operatorNeuronSet σ Set.univ) : Set C(H, ℝ)) =
      closure (Submodule.span ℝ (operatorNeuronSet σ {A | IsHilbertSchmidt A}) :
        Set C(H, ℝ)) := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `A_a = ‖ψ‖⁻² ψ ⊗ a` is
Hilbert–Schmidt. -/
theorem lem_rank_one_lift_i (ψ a : H) : IsHilbertSchmidt (rankOneLift ψ a) := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `‖A_a‖_{𝓛₂} = ‖a‖ / ‖ψ‖`. -/
theorem lem_rank_one_lift_ii {ψ : H} (hψ : ψ ≠ 0) (a : H) :
    hsNorm (rankOneLift ψ a) = ‖a‖ / ‖ψ‖ := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `‖b_c‖ = |c| / ‖ψ‖`. -/
theorem lem_rank_one_lift_iii {ψ : H} (hψ : ψ ≠ 0) (c : ℝ) :
    ‖biasLift ψ c‖ = |c| / ‖ψ‖ := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `π_ψ(A_a, b_c) = (a, c)`. -/
theorem lem_rank_one_lift_iv [CompleteSpace H] {ψ : H} (hψ : ψ ≠ 0) (a : H) (c : ℝ) :
    operatorParameterMap ψ (operatorRidgeletSection ψ (a, c)) = (a, c) := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  The section `J_ψ(a, c) = (A_a, b_c)` is
continuous into `𝓛₂(H) × H`: the Hilbert–Schmidt distance of the operator components plus the
distance of the biases tends to `0` at every `(a, c)`. -/
theorem lem_rank_one_lift_v {ψ : H} (hψ : ψ ≠ 0) (a : H) (c : ℝ) :
    Filter.Tendsto
      (fun p : H × ℝ =>
        hsNorm (rankOneLift ψ p.1 - rankOneLift ψ a) + ‖biasLift ψ p.2 - biasLift ψ c‖)
      (𝓝 (a, c)) (𝓝 0) := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  Every scalar integral network with
activation `β` lifts exactly to the operator architecture with activation `σ_β` and readout
normalized by `⟪ℓ, z⟫ = 1`: `S_op[(J_ψ)_# Γ] = S_β[Γ]`. -/
theorem lem_rank_one_lift_vi [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0) (hℓz : inner ℝ ℓ z = 1)
    (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ (Γ.map (operatorRidgeletSection ψ)) =
      integralNetwork (fun t => (β t : ℂ)) Γ := by
  sorry

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  Every scalar finite-width network with
activation `β` lifts exactly to the operator architecture with activation `σ_β`, parameters
`(A_{a_j}, b_{c_j})`, and readout normalized by `⟪ℓ, z⟫ = 1`. -/
theorem lem_rank_one_lift_vii [CompleteSpace H] {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0)
    (hℓz : inner ℝ ℓ z = 1) {N : ℕ} (v : Fin N → Y) (a : Fin N → H) (c : Fin N → ℝ) :
    operatorFiniteNetwork (rankOneActivation β ψ z) ℓ v (fun j => rankOneLift ψ (a j))
        (fun j => biasLift ψ (c j)) =
      finiteNetwork (fun t => (β t : ℂ)) v a c := by
  sorry

/-! ## Appendix F: compact-open universality -/

/-- **Proposition [prop:scalar-universality]** Compact-open universality by finite-dimensional
reduction.  For continuous non-polynomial `β : ℝ → ℝ`, finite linear combinations of
`β(⟪a, x⟫ + c)` are dense in `C(H; ℝ)` for uniform convergence on compact sets. -/
theorem prop_scalar_universality_i [CompleteSpace H] [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) :
    Dense (Submodule.span ℝ (ridgeSet (H := H) β) : Set C(H, ℝ)) := by
  sorry

/-- **Proposition [prop:scalar-universality]** Compact-open universality by finite-dimensional
reduction.  For continuous non-polynomial `β : ℝ → ℝ` and nonzero `ψ, z`, finite linear
combinations of the operator neurons with the rank-one activation `σ_β` and Hilbert–Schmidt
parameters are dense in `C(H; ℝ)` for uniform convergence on compact sets. -/
theorem prop_scalar_universality_ii [CompleteSpace H] [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) {ψ z : H} (hψ : ψ ≠ 0) (hz : z ≠ 0) :
    Dense (Submodule.span ℝ
      (operatorNeuronSet (rankOneActivation β ψ z) {A | IsHilbertSchmidt A}) : Set C(H, ℝ)) := by
  sorry

/-! ## Appendix F: bounded synthesis and exact transport of measures -/

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.  For
real globally Lipschitz `β`, `ψ ≠ 0`, a finite complex Borel measure `Γ_op` on `𝓛₂(H) × H`
with `∫ (1 + ‖A‖_{𝓛₂} + ‖b‖) d|Γ_op| < ∞`, and readout normalized by `⟪ℓ, z⟫ = 1`,
`S_op Γ_op = S_β[(π_ψ)_# Γ_op]`. -/
theorem lem_measure_transport_i [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (ψ : H) (Γop : ComplexMeasure (OperatorRidgeParameter H))
    [IsFiniteMeasure Γop.variation] (hHS : ∀ᵐ p ∂Γop.variation, IsHilbertSchmidt p.1)
    (hmom : Integrable (fun p : OperatorRidgeParameter H => 1 + hsNorm p.1 + ‖p.2‖)
      Γop.variation)
    {ℓ z : H} (hℓz : inner ℝ ℓ z = 1) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ Γop =
      integralNetwork (fun t => (β t : ℂ)) (Γop.map (operatorParameterMap ψ)) := by
  sorry

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.  The
variation of the pushforward is dominated by the pushforward of the variation:
`|(π_ψ)_# Γ_op| ≤ (π_ψ)_# |Γ_op|`. -/
theorem lem_measure_transport_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) :
    (Γop.map (operatorParameterMap ψ)).variation ≤
      Γop.variation.map (operatorParameterMap ψ) := by
  sorry

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.  For
compact `K` with `r_K = sup_K ‖x‖`,
`‖S_op Γ_op‖_{C(K)} ≤ ∫ [|β(0)| + Lip(β) ‖ψ‖ (r_K ‖A‖_{𝓛₂} + ‖b‖)] d|Γ_op|`. -/
theorem lem_measure_transport_iii [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (ψ : H) (Γop : ComplexMeasure (OperatorRidgeParameter H))
    [IsFiniteMeasure Γop.variation] (hHS : ∀ᵐ p ∂Γop.variation, IsHilbertSchmidt p.1)
    (hmom : Integrable (fun p : OperatorRidgeParameter H => 1 + hsNorm p.1 + ‖p.2‖)
      Γop.variation)
    {ℓ z : H} (hℓz : inner ℝ ℓ z = 1) {K : Set H} (hK : IsCompact K) :
    ∀ x ∈ K, ‖operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x‖ ≤
      ∫ p, (|β 0| + (L : ℝ) * ‖ψ‖ * (sSup ((fun y : H => ‖y‖) '' K) * hsNorm p.1 + ‖p.2‖))
        ∂Γop.variation := by
  sorry

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.
Conversely, `(π_ψ)_# (J_ψ)_# Γ = Γ`. -/
theorem lem_measure_transport_iv [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] {ψ : H}
    (hψ : ψ ≠ 0) (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    (Γ.map (operatorRidgeletSection ψ)).map (operatorParameterMap ψ) = Γ := by
  sorry

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.
Conversely, `S_op (J_ψ)_# Γ = S_β Γ` with readout normalized by `⟪ℓ, z⟫ = 1`. -/
theorem lem_measure_transport_v [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0)
    (hℓz : inner ℝ ℓ z = 1) (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ (Γ.map (operatorRidgeletSection ψ)) =
      integralNetwork (fun t => (β t : ℂ)) Γ := by
  sorry

end OperatorRidgelet.Paper
