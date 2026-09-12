import OperatorRidgelet.Reconstruction.FiniteOrderDefs

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
/-- **Lemma [lem:spectral-target-basic]** The spectral target has the uniform L¹ norm bound. -/
theorem lem_spectral_target_basic_i (ν : Measure H) (G : H → Y) (_hG : Integrable G ν) :
    ∀ x : H, ‖spectralTarget ν G x‖ ≤ ∫ ξ, ‖G ξ‖ ∂ν := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:spectral-target-basic]** An integrable spectral density has a continuous target. -/
theorem lem_spectral_target_basic_ii (ν : Measure H) (G : H → Y) (hG : Integrable G ν) :
    Continuous (spectralTarget ν G) := by
  sorry

/-- **Lemma [lem:spectral-target-basic]** A spectral density is determined by its target. -/
theorem lem_spectral_target_basic_iii (ν : Measure H) (G : H → Y) (hG : Integrable G ν)
    (hzero : spectralTarget ν G = 0) : G =ᵐ[ν] 0 := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:coefficient-finite-order]** A bounded density with a finite ray moment is L¹∩L². -/
theorem lem_coefficient_finite_order_i (ν : Measure H) {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (G : H → Y) (hG : StronglyMeasurable G)
    (hbound : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M) (r : ℕ)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    Integrable G ν ∧ MemLp G 2 ν := by
  sorry

/-- **Lemma [lem:coefficient-finite-order]** The inverse integral represents the coefficient. -/
theorem lem_coefficient_finite_order_ii (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (G : H → Y) (hG : StronglyMeasurable G)
    (hbound : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M) (r : ℕ)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    StronglyMeasurable (coefficientFormulaVec ρ G) ∧
      (spectralCoefficientVec ν ρ G : H × ℝ → Y) =ᵐ[parameterMeasure ν]
        coefficientFormulaVec ρ G := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  [CompleteSpace Y] [SecondCountableTopology Y] in
/-- **Lemma [lem:coefficient-finite-order]** Finitely many ray derivatives give pointwise decay. -/
theorem lem_coefficient_finite_order_iii (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (r : ℕ) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧ ∀ G : H → Y,
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U) →
      ∀ (a : H) (c : ℝ),
        ENNReal.ofReal ((1 + |c|) ^ (r + 2)) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
          K * rayDerivBound I G (r + 2) a := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:coefficient-finite-order]** The parameter moment is bounded by A_{r+2,r}. -/
theorem lem_coefficient_finite_order_iv (ν : Measure H) [SigmaFinite ν]
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ G : H → Y, StronglyMeasurable G →
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U) →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ r) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        C * finiteRayMoment ν I G (r + 2) r := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Lemma [lem:coefficient-finite-order]** Finite ray data imply a finite parameter moment. -/
theorem lem_coefficient_finite_order_v (ν : Measure H) [SigmaFinite ν]
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (G : H → Y) (hG : StronglyMeasurable G) (r : ℕ)
    (hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (r + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U)
    (hM : finiteRayMoment ν I G (r + 2) r < ⊤) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ r *
      ‖coefficientFormulaVec ρ G θ‖) (parameterMeasure ν) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Theorem [thm:E]** All parameter moments are bounded, also for vector-valued densities. -/
theorem thm_E_moments (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I) (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ G : H → Y, IsRegularAlongRays ν I G →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ r) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        C * rayMoment ν I G (r + 2) := by
  sorry

/-- **Theorem [thm:A]** Tempered synthesis is jointly absolutely integrable. -/
theorem thm_A_iii_e (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b)
    (G : H → ℂ) (hG : IsRegularAlongRays ν I G) (x : H) :
    Integrable (fun θ : H × ℝ => coefficientFormula ρ G θ *
      (b (⟪θ.1, x⟫ + θ.2) : ℂ)) (parameterMeasure ν) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Theorem [thm:vector-valued]** Tempered synthesis is Bochner integrable on the product. -/
theorem thm_vector_valued_A_iii_e (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b)
    (G : H → Y) (hG : IsRegularAlongRays ν I G) (x : H) :
    Integrable (fun θ : H × ℝ => (b (⟪θ.1, x⟫ + θ.2) : ℂ) •
      coefficientFormulaVec ρ G θ) (parameterMeasure ν) := by
  sorry

end OperatorRidgelet.Paper
