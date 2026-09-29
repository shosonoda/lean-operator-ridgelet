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
  sorry

/-- **Corollary [cor:D.7]** Approximation with operator-valued parameters.
`M_op² ≤ ‖ψ‖² ∫ (‖A‖²_{𝓛₂} + ‖b‖²) dp_op`. -/
theorem cor_D_7_ii [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) [IsFiniteMeasure Γop.variation]
    (hHS : ∀ᵐ q ∂Γop.variation, IsHilbertSchmidt q.1) :
    ∫⁻ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ₑ ^ 2 + ‖⟪ψ, q.2⟫‖ₑ ^ 2) ∂polarLaw Γop ≤
      ‖ψ‖ₑ ^ 2 * ∫⁻ q, (hsNormSq q.1 + ‖q.2‖ₑ ^ 2) ∂polarLaw Γop := by
  sorry
