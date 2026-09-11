import OperatorRidgelet.Filters.Admissible
import OperatorRidgelet.Tempered.Regularized
import OperatorRidgelet.Tempered.Frame
import OperatorRidgelet.Reconstruction.Representation
import OperatorRidgelet.ToMathlib.TemperedDistributionConvolution

/-!
# Reconstruction with a tempered activation

Theorem `thm:tempered-reconstruction`: for a real tempered `β`, a band-pass `ρ`, a cutoff `χ`,
and an approximate identity `(η_ε)`, the regularized syntheses `S_{β_ε} R_ρ f` converge in
`𝓔_α'` to `C^{(α)}_{β,ρ} T_α f` (`tendsto_regularizedSynthesis`), so that the tempered
synthesis is `S_β R_ρ f = C^{(α)}_{β,ρ} T_α f` (`temperedSynthesis_ridgeletExtension_eq`).

Each `β_ε` is a real Schwartz function with `β̂_ε ∈ C_c^∞(ℝ ∖ {0})`, hence either zero or
band-pass, and the cross frame identity `S_{β_ε} R_ρ f = C^{(α)}_{ρ,β_ε} T_α f`
(`synthesis_ridgeletExtension_eq_of_bandLimited`) holds.  The constant is
`C^{(α)}_{ρ,β_ε} = (2π)⁻¹ ∫ (β̂ * η_ε)(ω) ρ̂(-ω)|ω|^{-α} dω`
(`crossAdmissibilityConst_regularizedActivation`), which by
`TemperedDistribution.integral_mul_apply_translate` is `(2π)⁻¹ ⟨β̂, T ⋆ η_ε⟩` with `T` the test
filter, and `T ⋆ η_ε → T` in the Schwartz topology as `ε ↓ 0`
(`tendsto_crossAdmissibilityConst_regularizedActivation`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform ComplexConjugate Convolution ENNReal

/-! ### The zero filter -/

section ZeroFilter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

omit [OpensMeasurableSpace H] in
/-- The transform with the zero filter is zero. -/
theorem ridgelet_zero_filter (μ : Measure H) (f : H → ℂ) : ridgelet μ (0 : ℝ → ℝ) f = 0 := by
  funext p
  simp [ridgelet]

/-- The extension of the zero filter is zero. -/
theorem ridgeletExtension_zero (μ ν : Measure H) [IsFiniteMeasure μ] :
    ridgeletExtension μ ν (0 : ℝ → ℝ) = 0 := by
  classical
  have hex : ∃ R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ 0 f :=
    ⟨0, fun f => by
      rw [ridgelet_zero_filter, zero_apply]
      exact Lp.coeFn_zero _ _ _⟩
  rw [ridgeletExtension, dif_pos hex]
  have hd := denseRange_spectralEmbedₗ μ ν
  have h := hd.equalizer hex.choose.continuous continuous_const (funext fun f => by
    simp only [Function.comp_apply, spectralEmbedₗ_apply]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have := hex.choose_spec f
    rwa [ridgelet_zero_filter] at this)
  exact ContinuousLinearMap.ext fun g => congrFun h g

end ZeroFilter

/-! ### The frame identity for a band-limited synthesis filter -/

section FrameIdentity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The cross frame identity for a real Schwartz `ρ₁` with `ρ̂₁ ∈ C_c^∞(ℝ ∖ {0})`, possibly
zero, and a band-pass `ρ`. -/
theorem synthesis_ridgeletExtension_eq_of_bandLimited (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) {ρ₁ ρ : SchwartzMap ℝ ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) (filterFourier ρ₁)) (h₁c : HasCompactSupport (filterFourier ρ₁))
    (h₁0 : (0 : ℝ) ∉ tsupport (filterFourier ρ₁)) (hρ : IsBandPass ρ) (f : spectralRange μ ν) :
    synthesis μ ν ρ₁ (ridgeletExtension μ ν ρ f) =
      crossAdmissibilityConst α ρ ρ₁ • rieszMap μ ν f := by
  by_cases h0 : ρ₁ = 0
  · subst h0
    have hC : crossAdmissibilityConst α ρ (0 : SchwartzMap ℝ ℝ) = 0 := by
      unfold crossAdmissibilityConst
      simp [show (⇑(0 : SchwartzMap ℝ ℝ) : ℝ → ℝ) = 0 from rfl, filterFourier_zero]
    rw [hC]
    unfold synthesis
    rw [show (⇑(0 : SchwartzMap ℝ ℝ) : ℝ → ℝ) = 0 from rfl, ridgeletExtension_zero,
      ContinuousLinearMap.comp_zero]
    exact (zero_smul ℂ (rieszMap μ ν f)).symm
  · exact synthesis_ridgeletExtension_eq μ ν hν (IsBandPass.isAdmissible ⟨h0, h₁, h₁c, h₁0⟩ α)
      (hρ.isAdmissible α) f

end FrameIdentity

/-! ### The constants `C^{(α)}_{ρ,β_ε}` and their limit -/

/-- The cutoff is one where `ρ̂(-·)` does not vanish. -/
theorem IsCutoff.apply_eq_one_of_filterFourier_neg_ne_zero {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) {ω : ℝ} (h : filterFourier ρ (-ω) ≠ 0) : χ ω = 1 := by
  have hmem : -ω ∈ tsupport (filterFourier ρ) := subset_tsupport _ (Function.mem_support.mpr h)
  have h1 : χ (-ω) = 1 :=
    ((eventually_nhdsSet_iff_forall.mp hχ.eventuallyEq_one) (-ω) hmem).self_of_nhds
  rw [← hχ.even ω]
  exact h1

/-- `C^{(α)}_{ρ,β_ε} = (2π)⁻¹ ∫ ρ̂(-ω)|ω|^{-α} (β̂ * η_ε)(ω) dω`. -/
theorem crossAdmissibilityConst_regularizedActivation {α : ℝ} {β : TemperedDistribution ℝ ℂ}
    (hβ : IsRealDistribution β) {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ} (hη : IsApproximateIdentity η) {ε : ℝ} (hε : 0 < ε) :
    crossAdmissibilityConst α ρ (regularizedActivation β χ η ε) = ((2 * Real.pi)⁻¹ : ℝ) *
      ∫ ω : ℝ, temperedTestFilter α ρ ω *
        distributionConvolution (angularFourierDistribution β) (η ε) ω := by
  unfold crossAdmissibilityConst
  congr 1
  have hsub := Measure.integral_comp_mul_left (fun ω : ℝ => filterFourier ρ ω *
    conj (filterFourier (regularizedActivation β χ η ε) ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at hsub
  rw [← hsub]
  apply integral_congr_ae
  filter_upwards with ω
  rw [filterFourier_regularizedActivation hβ hχ hη hε, conj_regularizedSpectrum_neg hβ hχ hη hε,
    hρ.temperedTestFilter_apply]
  unfold regularizedSpectrum
  by_cases hT : filterFourier ρ (-ω) = 0
  · rw [hT]
    simp
  · rw [hχ.apply_eq_one_of_filterFourier_neg_ne_zero hT]
    push_cast
    ring

/-- The test filter of a band-pass filter has compact support. -/
theorem IsBandPass.hasCompactSupport_temperedTestFilter {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (α : ℝ) : HasCompactSupport ⇑(temperedTestFilter α ρ) := by
  have h : ⇑(temperedTestFilter α ρ) = fun ω => filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) :=
    funext (hρ.temperedTestFilter_apply α)
  rw [h]
  exact (hρ.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).mul_right

/-- The constants `C^{(α)}_{ρ,β_ε}` converge to `C^{(α)}_{β,ρ}` as `ε ↓ 0`. -/
theorem tendsto_crossAdmissibilityConst_regularizedActivation {α : ℝ}
    {β : TemperedDistribution ℝ ℂ} (hβ : IsRealDistribution β) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {χ : ℝ → ℝ} (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ}
    (hη : IsApproximateIdentity η) :
    Tendsto (fun ε => crossAdmissibilityConst α ρ (regularizedActivation β χ η ε)) (𝓝[>] 0)
      (𝓝 (temperedAdmissibilityConst α β ρ)) := by
  classical
  set T := temperedTestFilter α ρ with hTdef
  have hTs : ContDiff ℝ (⊤ : ℕ∞) ⇑T := T.smooth ⊤
  have hTc : HasCompactSupport ⇑T := hρ.hasCompactSupport_temperedTestFilter α
  have hηs : ∀ ε, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) fun x => (η ε x : ℂ) := fun ε hε =>
    contDiff_ofReal_comp (hη.contDiff ε hε)
  have hηc : ∀ ε, 0 < ε → HasCompactSupport fun x => (η ε x : ℂ) := fun ε hε =>
    hasCompactSupport_ofReal_comp (hη.hasCompactSupport ε hε)
  let convS : ℝ → SchwartzMap ℝ ℂ := fun ε =>
    if hε : 0 < ε then
      TemperedDistribution.convolutionSchwartz ⇑T (fun t => ((η ε (-t) : ℝ) : ℂ))
        hTs.continuous.locallyIntegrable hTc (TemperedDistribution.contDiff_reflect (hηs ε hε))
        (TemperedDistribution.hasCompactSupport_reflect (hηc ε hε))
    else T
  have hC : ∀ ε, 0 < ε → crossAdmissibilityConst α ρ (regularizedActivation β χ η ε) =
      ((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β (convS ε) := by
    intro ε hε
    rw [crossAdmissibilityConst_regularizedActivation hβ hρ hχ hη hε]
    congr 1
    simp only [convS, dif_pos hε]
    rw [← TemperedDistribution.integral_mul_apply_translate _ (hηs ε hε) (hηc ε hε) hTs hTc]
    congr 1
    funext ω
    rw [distributionConvolution_eq _ (hη.contDiff ε hε) (hη.hasCompactSupport ε hε)]
  have hconv : Tendsto convS (𝓝[>] 0) (𝓝 T) := by
    rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
    intro m ε' hε'
    obtain ⟨K, hK0, hK⟩ :=
      TemperedDistribution.norm_iteratedDeriv_convolution_sub_le hTs hTc m.1 m.2
    set δ := min 1 (ε' / (K + 1)) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hKδ : K * δ < ε' := by
      calc K * δ ≤ K * (ε' / (K + 1)) := by
            gcongr
            exact min_le_right _ _
        _ < ε' := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
    have hsupp : ∀ᶠ ε in 𝓝[>] 0, tsupport (η ε) ⊆ Metric.closedBall 0 δ :=
      (Filter.tendsto_smallSets_iff.mp hη.tendsto_tsupport) _ (Metric.closedBall_mem_nhds 0 hδpos)
    filter_upwards [hsupp, self_mem_nhdsWithin] with ε hεs hε
    have hε0 : 0 < ε := hε
    have hcoe : ⇑(convS ε - T) =
        ((fun s => ((η ε s : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ] ⇑T) - ⇑T := by
      have hrefl : (fun t => ((η ε (-t) : ℝ) : ℂ)) = fun s => ((η ε s : ℝ) : ℂ) :=
        funext fun t => by rw [hη.even ε hε0]
      have hcomm : ((fun s => ((η ε s : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ] ⇑T) =
          ⇑T ⋆[ContinuousLinearMap.mul ℝ ℂ] fun s => ((η ε s : ℝ) : ℂ) := by
        have := convolution_flip (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) (f := ⇑T)
          (g := fun s => ((η ε s : ℝ) : ℂ))
        rwa [ContinuousLinearMap.flip_mul] at this
      rw [hcomm]
      funext x
      simp only [convS, dif_pos hε0, sub_apply, Pi.sub_apply, hrefl]
      rfl
    have hle : SchwartzMap.seminorm ℂ m.1 m.2 (convS ε - T) ≤ K * δ := by
      apply SchwartzMap.seminorm_le_bound' ℂ _ _ _ (by positivity)
      intro x
      rw [hcoe]
      exact hK (η ε) δ hδpos hδ1 (hη.nonneg ε hε0)
        ((hη.contDiff ε hε0).continuous.integrable_of_hasCompactSupport
          (hη.hasCompactSupport ε hε0))
        (hη.integral_eq_one ε hε0) hεs x
    exact lt_of_le_of_lt hle hKδ
  have h3 : Tendsto (fun ε => ((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β (convS ε))
      (𝓝[>] 0) (𝓝 (((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β T)) :=
    tendsto_const_nhds.mul (((angularFourierDistribution β).continuous.tendsto T).comp hconv)
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hC ε hε).symm

/-! ### The frame identity for the tempered synthesis -/

section Synthesis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- `S_{β_ε} R_ρ f → C^{(α)}_{β,ρ} T_α f` in `𝓔_α'` as `ε ↓ 0`. -/
theorem tendsto_regularizedSynthesis (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    {α : ℝ} (hν : IsHomogeneous α ν) {β : TemperedDistribution ℝ ℂ} (hβ : IsRealDistribution β)
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {χ : ℝ → ℝ} (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ}
    (hη : IsApproximateIdentity η) (f : spectralRange μ ν) :
    Tendsto (fun ε : ℝ => regularizedSynthesis μ ν β χ η ε (ridgeletExtension μ ν ρ f))
      (𝓝[>] 0) (𝓝 (temperedAdmissibilityConst α β ρ • rieszMap μ ν f)) := by
  have h1 := (tendsto_crossAdmissibilityConst_regularizedActivation (α := α) hβ hρ hχ hη).smul_const
    (rieszMap μ ν f)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold regularizedSynthesis
  have hF' : filterFourier (regularizedActivation β χ η ε) = regularizedSpectrum β χ η ε :=
    funext (filterFourier_regularizedActivation hβ hχ hη hε)
  rw [synthesis_ridgeletExtension_eq_of_bandLimited μ ν hν (by
      rw [hF']
      exact hχ.contDiff_regularizedSpectrum hη hε β) (by
      rw [hF']
      exact hχ.hasCompactSupport_regularizedSpectrum η ε β) (by
      rw [hF']
      exact hχ.zero_notMem_tsupport_regularizedSpectrum η ε β) hρ f]

/-- **Theorem `thm:tempered-reconstruction`**, the frame identity
`S_β R_ρ f = C^{(α)}_{β,ρ} T_α f`. -/
theorem temperedSynthesis_ridgeletExtension_eq (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) {β : TemperedDistribution ℝ ℂ}
    (hβ : IsRealDistribution β) {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ} (hη : IsApproximateIdentity η) (f : spectralRange μ ν) :
    temperedSynthesis μ ν β χ η (ridgeletExtension μ ν ρ f) =
      temperedAdmissibilityConst α β ρ • rieszMap μ ν f := by
  classical
  have ht := tendsto_regularizedSynthesis μ ν hν hβ hρ hχ hη f
  have hex : ∃ F : SpectralAntiDual μ ν,
      Tendsto (fun ε : ℝ => regularizedSynthesis μ ν β χ η ε (ridgeletExtension μ ν ρ f))
        (𝓝[>] 0) (𝓝 F) := ⟨_, ht⟩
  rw [temperedSynthesis, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec ht

end Synthesis

/-! ### Reality of ReLU -/

/-- A tempered distribution acting by integration against a real function is real. -/
theorem isRealDistribution_of_integral {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ}
    (hβ : ∀ φ : SchwartzMap ℝ ℂ, β φ = ∫ x : ℝ, φ x * (b x : ℂ)) : IsRealDistribution β := by
  ext φ
  rw [temperedDistributionConjugation_apply, hβ, hβ, ← integral_conj]
  congr 1
  funext x
  rw [schwartzConjugation_apply, map_mul, conj_conj, Complex.conj_ofReal]

/-- `ReLU ∈ 𝒮'(ℝ)` is a real distribution. -/
theorem isRealDistribution_reluDistribution : IsRealDistribution reluDistribution :=
  isRealDistribution_of_integral (reluTemperedDistribution_apply 2 (by norm_num))

end OperatorRidgelet
