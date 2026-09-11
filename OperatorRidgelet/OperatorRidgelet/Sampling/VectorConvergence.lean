import OperatorRidgelet.Sampling.VectorCompact

/-! # Vanishing of vector Rademacher complexity on compact sets -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {K : Set H}

/-- The vector complexity is the expected norm of the signed average of its compact atoms. -/
theorem rademacherComplexity_eq_integral_norm_vec (N : ℕ) (p : Measure (H × ℝ))
    (β : ℝ → ℂ) (h : H × ℝ → Y) {Φ : H × ℝ → (K →ᵇ Y)}
    (hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) • h θ) :
    rademacherComplexity N K p β h =
      ∫ z, ‖(N : ℝ)⁻¹ • ∑ j, z.2 j • Φ (z.1 j)‖
        ∂((sampleLaw N p).prod (rademacherMeasure N)) := by
  apply MeasureTheory.integral_congr_ae
  exact Eventually.of_forall fun z => by
    apply compactSupNorm_eq_norm_of_forall
    intro x
    change (N : ℝ)⁻¹ • (BoundedContinuousFunction.evalCLM ℂ x) (∑ j, z.2 j • Φ (z.1 j)) = _
    rw [map_sum]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.coe_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change (z.2 j : ℝ) • Φ (z.1 j) x = _
    rw [hΦ]

/-- The Rademacher average of any integrable separable Banach-valued atom map tends to zero. -/
theorem tendsto_signed_sample_average {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → E} (hint : Integrable Φ p) :
    Tendsto (fun N : ℕ => ∫ z : (Fin N → Ω) × (Fin N → ℝ),
      ‖(N : ℝ)⁻¹ • ∑ j, z.2 j • Φ (z.1 j)‖
        ∂((Measure.pi fun _ : Fin N => p).prod (rademacherMeasure N))) atTop (𝓝 0) := by
  have hsign : Integrable (fun t : ℝ => t) rademacherSign := by
    apply Integrable.smul_measure _ (by finiteness)
    exact (integrable_add_measure.mpr ⟨integrable_dirac (by finiteness),
      integrable_dirac (by finiteness)⟩)
  let Ψ : Ω × ℝ → E := fun z => z.2 • Φ z.1
  have hΨ : Integrable Ψ (p.prod rademacherSign) := (hsign.smul_prod hint).swap
  have hzero : ∫ z, Ψ z ∂p.prod rademacherSign = 0 := by
    have hz : ∫ t : ℝ, t ∂rademacherSign = 0 := by
      rw [rademacherSign, integral_smul_measure,
        integral_add_measure (integrable_dirac (by finiteness))
          (integrable_dirac (by finiteness))]
      simp
    rw [integral_prod _ hΨ]
    simp only [Ψ, integral_smul_const, hz, zero_smul, integral_zero]
  have ht := tendsto_integral_norm_sampleMean_ae (p.prod rademacherSign) hΨ
  simp only [hzero, sub_zero] at ht
  apply ht.congr
  intro N
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω ℝ (Fin N)
  have hmp := measurePreserving_arrowProdEquivProdArrow Ω ℝ (Fin N)
    (fun _ => p) (fun _ => rademacherSign)
  simpa only [Ψ, rademacherMeasure_eq, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk] using
    hmp.integral_comp' (fun z : (Fin N → Ω) × (Fin N → ℝ) =>
      ‖(N : ℝ)⁻¹ • ∑ j, z.2 j • Φ (z.1 j)‖)

/-- Vector Rademacher complexity tends to zero for compact input sets. -/
theorem tendsto_rademacherComplexity_vector [BorelSpace H] [SecondCountableTopology H]
    [SecondCountableTopology Y] {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ))
    (hK : IsCompact K) :
    Tendsto (fun N : ℕ => rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ))
      atTop (𝓝 0) := by
  by_cases h0 : totalVariation Γ = 0
  · apply tendsto_congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩) |>.mpr tendsto_const_nhds
    simp [rademacherComplexity, polarLaw_eq_zero_of_totalVariation_eq_zero h0,
      sampleLaw_zero (by omega : 0 < N)]
  letI := isProbabilityMeasure_polarLaw Γ h0
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : SecondCountableTopology K := EMetric.secondCountable_of_sigmaCompact K
  haveI : SecondCountableTopology C(K, Y) := ContinuousMap.instSecondCountableTopology
  haveI : SecondCountableTopology (K →ᵇ Y) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K Y).toHomeomorph.symm.secondCountableTopology
  letI : MeasurableSpace (K →ᵇ Y) := borel _
  letI : BorelSpace (K →ᵇ Y) := ⟨rfl⟩
  let Φ : H × ℝ → (K →ᵇ Y) := fun θ => vectorRidgeAtom hK hβ.continuous θ (polarDensity Γ θ)
  have hi := integrable_vectorRidgeAtom hK hβ (polarLaw Γ) (polarDensity Γ)
    (aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0))
    (ae_polarLaw_norm_polarDensity_eq_one Γ) hM
  have ht := tendsto_signed_sample_average (polarLaw Γ) hi
  apply ht.congr
  intro N
  exact (rademacherComplexity_eq_integral_norm_vec N (polarLaw Γ) β (polarDensity Γ)
    (Φ := Φ) (fun _ _ => rfl)).symm

end OperatorRidgelet
