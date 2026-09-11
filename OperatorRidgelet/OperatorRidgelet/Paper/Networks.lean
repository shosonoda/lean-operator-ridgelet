import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Architecture.Defs
import OperatorRidgelet.Architecture.Basic
import OperatorRidgelet.ToMathlib.VectorMeasureWithDensity
import OperatorRidgelet.Architecture.Reduction
import OperatorRidgelet.Architecture.Universality

/-!
# Statements of Section 2 (networks with Hilbert-space inputs) and Appendix F (operator-valued parameters)

Each item is `theorem OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, identical to its twin in
`Challenge.Networks`, proved from the library or left as `sorry`.

The ambient space `H` is a real Hilbert space; the manuscript's separability, Borel structure,
and the output Hilbert space `Y` enter as explicit instance hypotheses where the statement uses
them.  Vector measures of bounded variation are `MeasureTheory.VectorMeasure` with finite
`variation` (see `OperatorRidgelet.Network.Defs`), and `𝓛₂(H)` is the set of bounded operators
satisfying `IsHilbertSchmidt` (see `OperatorRidgelet.Architecture.Defs`).
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
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) :=
  integrable_ridge_of_lipschitz hβ Γ hmom x

/-- **Definition [def:integral-network]** Integral network.  For `Γ = γ λ` with a density `γ`
with respect to a σ-finite reference measure `λ`, the integral network `S_β[Γ]` is the Bochner
integral `S_β[γ](x) = ∫ β(⟪a, x⟫ + c) γ(a, c) λ(da, dc)`, whenever the latter exists. -/
theorem def_integral_network_ii [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ}
    (hβ : Continuous β) (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (x : H)
    (hint : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) • γ θ) lam) :
    integralNetwork β (lam.withDensityᵥ γ) x = integralNetworkDensity β lam γ x := by
  unfold integralNetwork integralNetworkDensity
  have hmeas : AEStronglyMeasurable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2)) lam :=
    (hβ.comp (by fun_prop : Continuous fun θ : H × ℝ => inner ℝ θ.1 x + θ.2)).aestronglyMeasurable
  have hf : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2))
      (lam.withDensity fun θ => ‖γ θ‖ₑ) := by
    refine (integrable_withDensity_iff_integrable_coe_smul₀
      hγ.aestronglyMeasurable.nnnorm.aemeasurable).mpr ?_
    refine hint.norm.mono' (hγ.aestronglyMeasurable.norm.smul hmeas)
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [norm_smul, norm_smul, coe_nnnorm, Real.norm_eq_abs, abs_norm, mul_comm]
  rw [VectorMeasure.integral_withDensityᵥ hγ hf]
  rfl

/-! ## Appendix F: Hilbert–Schmidt reduction and the rank-one lift -/

/-- **Lemma [lem:hs-reduction]** Hilbert–Schmidt reduction.  For globally Lipschitz `σ`, the
spans of the operator neurons with `A ∈ 𝓛(H)` and with `A ∈ 𝓛₂(H)` have the same compact-open
closure in `C(H; ℝ)`. -/
theorem lem_hs_reduction [CompleteSpace H] [SecondCountableTopology H] {σ : H → H} {L : ℝ≥0}
    (hσ : LipschitzWith L σ) :
    closure (Submodule.span ℝ (operatorNeuronSet σ Set.univ) : Set C(H, ℝ)) =
      closure (Submodule.span ℝ (operatorNeuronSet σ {A | IsHilbertSchmidt A}) :
        Set C(H, ℝ)) := by
  apply le_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rw [← Submodule.topologicalClosure_coe]
    refine SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr ?_)
    rintro F ⟨ℓ, b, A, -, hF⟩
    rw [SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact operatorNeuron_mem_closure_span_hilbertSchmidt hσ ℓ A b hF
  · exact closure_mono (Submodule.span_mono fun F ⟨ℓ, b, A, _, hF⟩ => ⟨ℓ, b, A, trivial, hF⟩)

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `A_a = ‖ψ‖⁻² ψ ⊗ a` is
Hilbert–Schmidt. -/
theorem lem_rank_one_lift_i (ψ a : H) : IsHilbertSchmidt (rankOneLift ψ a) :=
  isHilbertSchmidt_rankOneLift ψ a

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `‖A_a‖_{𝓛₂} = ‖a‖ / ‖ψ‖`. -/
theorem lem_rank_one_lift_ii {ψ : H} (hψ : ψ ≠ 0) (a : H) :
    hsNorm (rankOneLift ψ a) = ‖a‖ / ‖ψ‖ :=
  hsNorm_rankOneLift hψ a

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `‖b_c‖ = |c| / ‖ψ‖`. -/
theorem lem_rank_one_lift_iii {ψ : H} (hψ : ψ ≠ 0) (c : ℝ) :
    ‖biasLift ψ c‖ = |c| / ‖ψ‖ :=
  norm_biasLift hψ c

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  `π_ψ(A_a, b_c) = (a, c)`. -/
theorem lem_rank_one_lift_iv [CompleteSpace H] {ψ : H} (hψ : ψ ≠ 0) (a : H) (c : ℝ) :
    operatorParameterMap ψ (operatorRidgeletSection ψ (a, c)) = (a, c) :=
  operatorParameterMap_section ψ hψ (a, c)

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  The section `J_ψ(a, c) = (A_a, b_c)` is
continuous into `𝓛₂(H) × H`: the Hilbert–Schmidt distance of the operator components plus the
distance of the biases tends to `0` at every `(a, c)`. -/
theorem lem_rank_one_lift_v {ψ : H} (hψ : ψ ≠ 0) (a : H) (c : ℝ) :
    Filter.Tendsto
      (fun p : H × ℝ =>
        hsNorm (rankOneLift ψ p.1 - rankOneLift ψ a) + ‖biasLift ψ p.2 - biasLift ψ c‖)
      (𝓝 (a, c)) (𝓝 0) :=
  tendsto_hsNorm_rankOneLift_sub_add_norm_biasLift_sub hψ a c

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  Every scalar integral network with
activation `β` lifts exactly to the operator architecture with activation `σ_β` and readout
normalized by `⟪ℓ, z⟫ = 1`: `S_op[(J_ψ)_# Γ] = S_β[Γ]`. -/
theorem lem_rank_one_lift_vi [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0) (hℓz : inner ℝ ℓ z = 1)
    (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ (Γ.map (operatorRidgeletSection ψ)) =
      integralNetwork (fun t => (β t : ℂ)) Γ :=
  operatorSynthesis_map_section β hψ hℓz Γ

/-- **Lemma [lem:rank-one-lift]** Exact rank-one lift.  Every scalar finite-width network with
activation `β` lifts exactly to the operator architecture with activation `σ_β`, parameters
`(A_{a_j}, b_{c_j})`, and readout normalized by `⟪ℓ, z⟫ = 1`. -/
theorem lem_rank_one_lift_vii [CompleteSpace H] {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0)
    (hℓz : inner ℝ ℓ z = 1) {N : ℕ} (v : Fin N → Y) (a : Fin N → H) (c : Fin N → ℝ) :
    operatorFiniteNetwork (rankOneActivation β ψ z) ℓ v (fun j => rankOneLift ψ (a j))
        (fun j => biasLift ψ (c j)) =
      finiteNetwork (fun t => (β t : ℂ)) v a c :=
  operatorFiniteNetwork_section β hψ hℓz v a c

/-! ## Appendix F: compact-open universality -/

/-- **Proposition [prop:scalar-universality]** Compact-open universality by finite-dimensional
reduction.  For continuous non-polynomial `β : ℝ → ℝ`, finite linear combinations of
`β(⟪a, x⟫ + c)` are dense in `C(H; ℝ)` for uniform convergence on compact sets. -/
theorem prop_scalar_universality_i [CompleteSpace H] [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) :
    Dense (Submodule.span ℝ (ridgeSet (H := H) β) : Set C(H, ℝ)) := by
  exact dense_ridgeSpan hβ hpoly

/-- **Proposition [prop:scalar-universality]** Compact-open universality by finite-dimensional
reduction.  For continuous non-polynomial `β : ℝ → ℝ` and nonzero `ψ, z`, finite linear
combinations of the operator neurons with the rank-one activation `σ_β` and Hilbert–Schmidt
parameters are dense in `C(H; ℝ)` for uniform convergence on compact sets. -/
theorem prop_scalar_universality_ii [CompleteSpace H] [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) {ψ z : H} (hψ : ψ ≠ 0) (hz : z ≠ 0) :
    Dense (Submodule.span ℝ
      (operatorNeuronSet (rankOneActivation β ψ z) {A | IsHilbertSchmidt A}) : Set C(H, ℝ)) := by
  exact dense_operatorNeuronSpan hβ hpoly hψ hz

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
      integralNetwork (fun t => (β t : ℂ)) (Γop.map (operatorParameterMap ψ)) :=
  operatorSynthesis_eq_integralNetwork_map hβ ψ Γop hHS hmom hℓz

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.  The
variation of the pushforward is dominated by the pushforward of the variation:
`|(π_ψ)_# Γ_op| ≤ (π_ψ)_# |Γ_op|`. -/
theorem lem_measure_transport_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) :
    (Γop.map (operatorParameterMap ψ)).variation ≤
      Γop.variation.map (operatorParameterMap ψ) :=
  VectorMeasure.variation_map_le

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
        ∂Γop.variation :=
  fun x hx => norm_operatorSynthesis_le hβ ψ Γop hHS hmom hℓz
    (le_csSup (hK.image continuous_norm).bddAbove ⟨x, hx, rfl⟩)

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.
Conversely, `(π_ψ)_# (J_ψ)_# Γ = Γ`. -/
theorem lem_measure_transport_iv [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] {ψ : H}
    (hψ : ψ ≠ 0) (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    (Γ.map (operatorRidgeletSection ψ)).map (operatorParameterMap ψ) = Γ :=
  operatorValuedRidgeletTransform_pushforward ψ hψ (fun _ : Unit => Γ) ()

/-- **Lemma [lem:measure-transport]** Bounded synthesis and exact transport of measures.
Conversely, `S_op (J_ψ)_# Γ = S_β Γ` with readout normalized by `⟪ℓ, z⟫ = 1`. -/
theorem lem_measure_transport_v [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0)
    (hℓz : inner ℝ ℓ z = 1) (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ (Γ.map (operatorRidgeletSection ψ)) =
      integralNetwork (fun t => (β t : ℂ)) Γ :=
  operatorSynthesis_map_section β hψ hℓz Γ

end OperatorRidgelet.Paper
