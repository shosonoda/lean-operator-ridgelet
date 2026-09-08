import OperatorRidgelet.Tempered.Fourier

/-!
# Weighted Sobolev activation spaces: the coordinate isometry and the duality bound

Lemma `lem:weighted-duality` of the manuscript (Appendix C).  With the vendored objects
`temperedWeightMultiplier r = ⟨·⟩^r`, `angularBesselPotential r = B^r`,
`angularFourierDistribution = F`, and `MemActivationSpace s t β ↔ B^s ⟨·⟩^{-t} β ∈ L²`, the
coordinate `⟨ω⟩^s B^{-t} β̂ = activationFourierCoordinate s t β` of `β ∈ 𝒜_{s,t}` is represented
by the `L²` function `activationCoordinate s t β`, the coordinate map is injective, every
`σ ∈ L²` is the coordinate of the vendored `activationRealization s t σ ∈ 𝒜_{s,t}`, and the
pairing `⟨β̂, r⟩` with a Schwartz test filter is the `L²` pairing of the coordinate with the test
coordinate `⟨ω⟩^{-s} B^t r = testFilterCoordinate s t r`, whence the duality bound by
Cauchy–Schwarz and its extension to `L²(ℝ)`.

The surjectivity of the vendored `L²` angular Fourier transform `angularFourierLp`
(`angularFourierLp_surjective`) is proved from the Plancherel identity (closed range) and the
density of Schwartz functions.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform

/-! ### The coordinate of an activation -/

/-- `⟨ω⟩^s B^{-t} β̂ = ⟨ω⟩^s F(⟨x⟩^{-t} β)`. -/
theorem activationFourierCoordinate_eq (s t : ℝ) (β : TemperedDistribution ℝ ℂ) :
    activationFourierCoordinate s t β =
      temperedWeightMultiplier s
        (angularFourierDistribution (temperedWeightMultiplier (-t) β)) := by
  rw [activationFourierCoordinate, angularBesselPotential_angularFourierDistribution]

/-- **Lemma `lem:weighted-duality`(i)**: the coordinate of `β ∈ 𝒜_{s,t}` is an `L²` function. -/
theorem exists_activationCoordinate_of_mem {s t : ℝ} {β : TemperedDistribution ℝ ℂ}
    (hβ : MemActivationSpace s t β) :
    ∃ σ : L2 ℝ volume,
      Lp.toTemperedDistributionCLM ℂ volume 2 σ = activationFourierCoordinate s t β := by
  obtain ⟨f, hf⟩ := hβ
  refine ⟨angularFourierLp f, ?_⟩
  rw [toTemperedDistribution_angularFourierLp, activationFourierCoordinate_eq]
  have hv : temperedWeightMultiplier (-t) β =
      angularBesselPotential (-s) (Lp.toTemperedDistributionCLM ℂ volume 2 f) := by
    rw [Lp.toTemperedDistributionCLM_apply, ← hf, angularBesselPotential_neg_angularBesselPotential]
  rw [hv, angularFourierDistribution_angularBesselPotential,
    temperedWeightMultiplier_temperedWeightMultiplier_neg]

/-- The chosen `L²` coordinate represents `⟨ω⟩^s B^{-t} β̂`. -/
theorem toTemperedDistribution_activationCoordinate {s t : ℝ}
    {β : TemperedDistribution ℝ ℂ} (hβ : MemActivationSpace s t β) :
    Lp.toTemperedDistributionCLM ℂ volume 2 (activationCoordinate s t β) =
      activationFourierCoordinate s t β := by
  classical
  rw [activationCoordinate, dif_pos (exists_activationCoordinate_of_mem hβ)]
  exact (exists_activationCoordinate_of_mem hβ).choose_spec

/-- `β` is recovered from its coordinate: `β = ⟨x⟩^t F⁻¹ ⟨ω⟩^{-s} (coordinate)`. -/
theorem eq_of_activationFourierCoordinate_eq {s t : ℝ} {β β' : TemperedDistribution ℝ ℂ}
    (h : activationFourierCoordinate s t β = activationFourierCoordinate s t β') : β = β' := by
  have h' := congrArg (fun u => temperedWeightMultiplier t
    (angularFourierInvDistribution (temperedWeightMultiplier (-s) u))) h
  simpa only [activationFourierCoordinate_eq, temperedWeightMultiplier_neg_temperedWeightMultiplier,
    angularFourierInvDistribution_angularFourierDistribution,
    temperedWeightMultiplier_temperedWeightMultiplier_neg] using h'

/-- **Lemma `lem:weighted-duality`(ii)**: the coordinate map is injective on `𝒜_{s,t}`. -/
theorem eq_of_activationCoordinate_eq {s t : ℝ}
    {β β' : TemperedDistribution ℝ ℂ} (hβ : MemActivationSpace s t β)
    (hβ' : MemActivationSpace s t β')
    (h : activationCoordinate s t β = activationCoordinate s t β') : β = β' := by
  apply eq_of_activationFourierCoordinate_eq (s := s) (t := t)
  rw [← toTemperedDistribution_activationCoordinate hβ,
    ← toTemperedDistribution_activationCoordinate hβ', h]

/-! ### Surjectivity of the `L²` angular Fourier transform -/

/-- Plancherel for the angular transform on Schwartz functions, in the `L²` norm. -/
theorem norm_toLp_angularFourierSchwartz (φ : SchwartzMap ℝ ℂ) :
    ‖(angularFourierSchwartz φ).toLp 2 volume‖ = Real.sqrt (2 * Real.pi) * ‖φ.toLp 2 volume‖ := by
  have hsq : ‖(angularFourierSchwartz φ).toLp 2 volume‖ ^ 2 =
      2 * Real.pi * ‖φ.toLp 2 volume‖ ^ 2 := by
    rw [norm_schwartz_toLp_two_sq, norm_schwartz_toLp_two_sq]
    have hplancherel := angular_plancherel_schwartz_inner (V := ℝ) φ
    rw [Module.finrank_self, pow_one] at hplancherel
    rw [← hplancherel]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [angularFourierSchwartz_eq_angularFourierIntegralInner]
  have h1 : (0 : ℝ) ≤ ‖(angularFourierSchwartz φ).toLp 2 volume‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * ‖φ.toLp 2 volume‖ := by positivity
  apply (sq_eq_sq₀ h1 h2).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hsq]

/-- Plancherel for the `L²` angular transform: `‖F f‖ = √(2π) ‖f‖`. -/
theorem norm_angularFourierLp (f : L2 ℝ volume) :
    ‖angularFourierLp f‖ = Real.sqrt (2 * Real.pi) * ‖f‖ := by
  refine (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).induction_on f ?_ ?_
  · exact isClosed_eq (continuous_norm.comp angularFourierLp.continuous)
      (continuous_const.mul continuous_norm)
  · intro φ
    change ‖angularFourierLp (φ.toLp 2 volume)‖ = Real.sqrt (2 * Real.pi) * ‖φ.toLp 2 volume‖
    rw [angularFourierLp_toLp, norm_toLp_angularFourierSchwartz]

/-- The `L²` angular transform has closed range. -/
theorem isClosed_range_angularFourierLp : IsClosed (Set.range angularFourierLp) := by
  have hanti : AntilipschitzWith (Real.toNNReal (Real.sqrt (2 * Real.pi))⁻¹) angularFourierLp := by
    apply angularFourierLp.antilipschitz_of_bound
    intro f
    rw [norm_angularFourierLp, Real.coe_toNNReal _ (by positivity), ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  exact hanti.isClosed_range angularFourierLp.uniformContinuous

/-- Every Schwartz function is an angular Fourier transform. -/
theorem angularFourierSchwartz_surjective : Function.Surjective angularFourierSchwartz := by
  intro ψ
  refine ⟨(2 * (Real.pi : ℂ))⁻¹ • angularFourierSchwartz (reflectSchwartz ψ), ?_⟩
  rw [← angularFourierSchwartzCLM_apply, map_smul, angularFourierSchwartzCLM_apply]
  ext x
  change (2 * (Real.pi : ℂ))⁻¹ *
    angularFourierSchwartz (angularFourierSchwartz (reflectSchwartz ψ)) x = ψ x
  rw [angularFourierSchwartz_angularFourierSchwartz, reflectSchwartz_apply, neg_neg, ← mul_assoc,
    inv_mul_cancel₀ two_mul_pi_complex_ne_zero, one_mul]

/-- The `L²` angular Fourier transform is surjective. -/
theorem angularFourierLp_surjective : Function.Surjective angularFourierLp := by
  have hdense : Dense (Set.range angularFourierLp) := by
    refine (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).mono ?_
    rintro - ⟨ψ, rfl⟩
    obtain ⟨φ, hφ⟩ := angularFourierSchwartz_surjective ψ
    refine ⟨φ.toLp 2 volume, ?_⟩
    rw [angularFourierLp_toLp, hφ]
    rfl
  have hrange : Set.range angularFourierLp = Set.univ :=
    isClosed_range_angularFourierLp.closure_eq ▸ hdense.closure_eq
  exact Set.range_eq_univ.mp hrange

/-! ### The realization of a coordinate -/

/-- **Lemma `lem:weighted-duality`(iii)**, membership: `F⁻¹ B^t ⟨ω⟩^{-s} σ ∈ 𝒜_{s,t}`. -/
theorem memActivationSpace_activationRealization (s t : ℝ) (σ : L2 ℝ volume) :
    MemActivationSpace s t (activationRealization s t σ) := by
  obtain ⟨τ, hτ⟩ := angularFourierLp_surjective σ
  refine ⟨τ, ?_⟩
  unfold activationRealization activationSpectrum
  simp only [ContinuousLinearMap.comp_apply]
  rw [← angularFourierInvDistribution_angularBesselPotential,
    angularBesselPotential_neg_angularBesselPotential,
    ← angularFourierInvDistribution_temperedWeightMultiplier,
    temperedWeightMultiplier_temperedWeightMultiplier_neg, ← hτ,
    toTemperedDistribution_angularFourierLp, angularFourierInvDistribution_angularFourierDistribution]
  rfl

/-- The coordinate of the realization of `σ` is `σ`, as a distribution. -/
theorem activationFourierCoordinate_activationRealization (s t : ℝ) (σ : L2 ℝ volume) :
    activationFourierCoordinate s t (activationRealization s t σ) =
      Lp.toTemperedDistributionCLM ℂ volume 2 σ := by
  unfold activationFourierCoordinate activationRealization activationSpectrum
  simp only [ContinuousLinearMap.comp_apply]
  rw [angularFourierDistribution_angularFourierInvDistribution,
    angularBesselPotential_neg_angularBesselPotential,
    temperedWeightMultiplier_temperedWeightMultiplier_neg]

/-- **Lemma `lem:weighted-duality`(iii)**, the coordinate of the realization of `σ` is `σ`. -/
theorem activationCoordinate_activationRealization (s t : ℝ) (σ : L2 ℝ volume) :
    activationCoordinate s t (activationRealization s t σ) = σ := by
  have h := toTemperedDistribution_activationCoordinate
    (memActivationSpace_activationRealization s t σ)
  rw [activationFourierCoordinate_activationRealization] at h
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℝ)))
  exact h

/-! ### The pairing with a test filter -/

/-- `⟨β̂, r⟩ = ∫ (⟨ω⟩^{-s} B^t r)(ω) σ(ω) dω` with `σ` the coordinate of `β ∈ 𝒜_{s,t}`. -/
theorem angularFourierDistribution_apply_eq_integral {s t : ℝ}
    {β : TemperedDistribution ℝ ℂ} (hβ : MemActivationSpace s t β) (r : SchwartzMap ℝ ℂ) :
    angularFourierDistribution β r =
      ∫ ω : ℝ, testFilterCoordinate s t r ω * activationCoordinate s t β ω := by
  have h := toTemperedDistribution_activationCoordinate hβ
  have hF : angularFourierDistribution β =
      angularBesselPotential t (temperedWeightMultiplier (-s)
        (Lp.toTemperedDistributionCLM ℂ volume 2 (activationCoordinate s t β))) := by
    rw [h, activationFourierCoordinate, temperedWeightMultiplier_neg_temperedWeightMultiplier,
      angularBesselPotential_angularBesselPotential_neg]
  rw [hF]
  unfold angularBesselPotential temperedWeightMultiplier
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply,
    fourier_smulLeft_fourierInv_of_even (hasTemperateGrowth_angularBesselSymbol t)
      (angularBesselSymbol_neg t), TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  rfl

/-- The norm of the conjugate of an `L²` function. -/
theorem norm_star_L2 (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => norm_star _)

/-- The pairing as an `L²` inner product: `∫ ψ σ = ⟪conj ψ, σ⟫`. -/
theorem inner_star_toLp_eq_integral (ψ : SchwartzMap ℝ ℂ) (σ : L2 ℝ volume) :
    inner ℂ (star (ψ.toLp 2 volume)) σ = ∫ ω : ℝ, ψ ω * σ ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (ψ.toLp 2 volume), ψ.coeFn_toLp 2 volume] with x hx hx'
  rw [hx, Pi.star_apply, hx', RCLike.inner_apply, Complex.star_def, Complex.conj_conj, mul_comm]

/-- **Lemma `lem:weighted-duality`(iv)**: `|⟨β̂, r⟩| ≤ ‖β‖_{𝒜_{s,t}} ‖r‖_{ℋ^♯_{s,t}}`. -/
theorem norm_angularFourierDistribution_apply_le {s t : ℝ}
    {β : TemperedDistribution ℝ ℂ} (hβ : MemActivationSpace s t β) (r : SchwartzMap ℝ ℂ) :
    ‖angularFourierDistribution β r‖ ≤ activationNorm s t β * testFilterNorm s t r := by
  rw [angularFourierDistribution_apply_eq_integral hβ r, ← inner_star_toLp_eq_integral]
  calc ‖inner ℂ (star ((testFilterCoordinate s t r).toLp 2 volume)) (activationCoordinate s t β)‖
      ≤ ‖star ((testFilterCoordinate s t r).toLp 2 volume)‖ * ‖activationCoordinate s t β‖ :=
        norm_inner_le_norm _ _
    _ = activationNorm s t β * testFilterNorm s t r := by
        rw [norm_star_L2, mul_comm]
        rfl

/-- **Lemma `lem:weighted-duality`(v)**: the pairing extends to `L²(ℝ)` as the functional
`ψ ↦ (2π)⁻¹ ⟪conj σ, ψ⟫`. -/
theorem exists_pairing_extension {s t : ℝ} {β : TemperedDistribution ℝ ℂ}
    (hβ : MemActivationSpace s t β) :
    ∃ Φ : L2 ℝ volume →L[ℂ] ℂ, ‖Φ‖ ≤ (2 * Real.pi)⁻¹ * activationNorm s t β ∧
      ∀ r : SchwartzMap ℝ ℂ,
        Φ ((testFilterCoordinate s t r).toLp 2 volume) =
          ((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β r := by
  refine ⟨(((2 * Real.pi)⁻¹ : ℝ) : ℂ) • innerSL ℂ (star (activationCoordinate s t β)), ?_, ?_⟩
  · rw [norm_smul, innerSL_apply_norm, norm_star_L2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    unfold activationNorm
    exact le_rfl
  · intro r
    change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * inner ℂ (star (activationCoordinate s t β))
      ((testFilterCoordinate s t r).toLp 2 volume) = _
    rw [angularFourierDistribution_apply_eq_integral hβ r]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star (activationCoordinate s t β),
      (testFilterCoordinate s t r).coeFn_toLp 2 volume] with x hx hx'
    rw [hx, Pi.star_apply, hx', RCLike.inner_apply, Complex.star_def, Complex.conj_conj]

end OperatorRidgelet
