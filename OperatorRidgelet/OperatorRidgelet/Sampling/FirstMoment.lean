import OperatorRidgelet.Sampling.VectorConvergence

/-! # Compact vector sampling under a first parameter moment -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  {K : Set H}

/-- A Lipschitz ridge is integrable under a first parameter moment. -/
theorem integrable_ridge_firstMoment {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) p) (x : H) :
    Integrable (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) p := by
  have hm : AEStronglyMeasurable (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) p :=
    (hβ.continuous.comp
      ((continuous_fst.inner continuous_const).add continuous_snd)).aestronglyMeasurable
  have hb : Integrable (fun θ : H × ℝ =>
      (‖β 0‖ + (L : ℝ) * max ‖x‖ 1) * (1 + (‖θ.1‖ + |θ.2|))) p :=
    ((integrable_const _).add hM).const_mul _
  apply hb.mono' hm
  exact Eventually.of_forall fun θ => by
    simpa only [add_assoc] using norm_ridge_le hβ x θ

variable [SecondCountableTopology H]

/-- The vector atoms with a measurable unit phase and finite parameter moment are integrable. -/
theorem integrable_vectorRidgeAtom_firstMoment (hK : IsCompact K) {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (h : H × ℝ → Y) (hh : AEStronglyMeasurable h p) (hu : ∀ᵐ θ ∂p, ‖h θ‖ = 1)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) p) :
    Integrable (fun θ => vectorRidgeAtom hK hβ.continuous θ (h θ)) p := by
  have hm := (continuous_vectorRidgeAtom hK hβ.continuous).comp_aestronglyMeasurable
    (aestronglyMeasurable_id.prodMk hh)
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let C := ‖β 0‖ + (L : ℝ) * max r 1
  have hb : Integrable (fun θ : H × ℝ => C * (1 + (‖θ.1‖ + |θ.2|))) p :=
    ((integrable_const _).add hM).const_mul C
  apply hb.mono' hm
  filter_upwards [hu] with θ hθ
  refine (norm_vectorRidgeAtom hK hβ.continuous θ (h θ)).trans ?_
  rw [hθ, mul_one]
  have ha : ‖ridgeAtom hK hβ.continuous θ‖ ≤ C * (1 + ‖θ.1‖ + |θ.2|) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact (norm_ridge_le hβ (x : H) θ).trans (by dsimp [C]; gcongr; exact hr x x.2)
  simpa only [add_assoc] using ha

/-- The compact-open vector sampling bound from symmetrization of the integrable atom map. -/
theorem integral_polarSampledNetwork_compact_le_firstMoment {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) (polarLaw Γ))
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      2 * polarWeight Γ * rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ) := by
  let Φ : H × ℝ → (K →ᵇ Y) := fun θ => vectorRidgeAtom hK hβ.continuous θ (polarDensity Γ θ)
  have hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) • polarDensity Γ θ := fun _ _ => rfl
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0, mul_zero, zero_mul]
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  have hint : Integrable Φ (polarLaw Γ) := integrable_vectorRidgeAtom_firstMoment hK hβ (polarLaw Γ)
    (polarDensity Γ) hh hh1 hM
  have hΦ' : ∀ θ (x : K), Φ θ x = β (⟪(id θ).1, (x : H)⟫ + (id θ).2) • polarDensity Γ θ := hΦ
  have hpt : ∀ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x) =
        polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖ := by
    intro θ
    rw [← compactSupNorm_sampled_sub_eq_vec (polarLaw Γ) β id (polarDensity Γ) hΦ' hint
      (polarWeight_nonneg Γ) hN θ]
    refine compactSupNorm_congr fun x hx => ?_
    rw [integralNetwork_eq_integral_polarLaw β Γ h0
      (integrable_ridge_firstMoment hβ (polarLaw Γ) hM x)]
    rfl
  have hsym := integral_norm_sum_sub_le (polarLaw Γ) hint (signVector (N := N))
    (fun _ => (2 ^ N : ℝ)⁻¹) (fun _ => by positivity) (sum_signs_inv_pow_two N)
    fun σ j => signVector_eq_one_or_neg_one σ j
  rw [rademacherComplexity_eq_sum_signs_vec N (polarLaw Γ) β (polarDensity Γ) hΦ hint]
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

variable [SecondCountableTopology Y]

/-- Vector Rademacher complexity tends to zero for compact input sets. -/
theorem tendsto_rademacherComplexity_vector_firstMoment
    {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ + |θ.2|) (polarLaw Γ))
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
  have hi := integrable_vectorRidgeAtom_firstMoment hK hβ (polarLaw Γ) (polarDensity Γ)
    (aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0))
    (ae_polarLaw_norm_polarDensity_eq_one Γ) hM
  have ht := tendsto_signed_sample_average (polarLaw Γ) hi
  apply ht.congr
  intro N
  exact (rademacherComplexity_eq_integral_norm_vec N (polarLaw Γ) β (polarDensity Γ)
    (Φ := Φ) (fun _ _ => rfl)).symm

end OperatorRidgelet
