/-! Historical fragments; see the archive README for their original context. -/

/-- **Corollary [cor:D.7]** Approximation with operator-valued parameters.  For a finite
complex measure `Γ_op` on `𝓛₂(H) × H` with polar decomposition `h_op |Γ_op|`,
`V_op = ‖Γ_op‖_TV`, `p_op = |Γ_op|/V_op`, real globally Lipschitz `β`, readout normalized by
`⟪ℓ, z⟫ = 1`, and `M_op² = ∫ (‖A^*ψ‖² + |⟪ψ, b⟫|²) dp_op < ∞`, sampling `(A_j, b_j)` from
`p_op` with the weights `h_op` gives
`𝔼‖f_{op,N} − S_op Γ_op‖_{C(K)} ≤ 8 V_op N^{-1/2} (|β(0)| + Lip(β) R_K M_op)`. -/
theorem cor_D_7_i [CompleteSpace H] [SecondCountableTopology H]
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

/-- **Corollary [cor:D.7]** Approximation with operator-valued parameters.
`M_op² ≤ ‖ψ‖² ∫ (‖A‖²_{𝓛₂} + ‖b‖²) dp_op`. -/
theorem cor_D_7_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
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
