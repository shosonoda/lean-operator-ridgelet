import OperatorRidgelet.Reconstruction.VectorBiasFourierUnitary

/-! # The vector coefficient operator and its ray-average adjoint -/

noncomputable section
open MeasureTheory Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace OperatorRidgelet
variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] {ν : Measure H} [SFinite ν]
  {α : ℝ} {ρ : SchwartzMap ℝ ℝ}

/-- Finite vector ray energy implies absolute convergence of the backprojection integral. -/
theorem integrable_backprojectionOfVec_integrand (hρ : IsAdmissible α ρ)
    {Φ : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ)) {ξ : H}
    (hξ : rayEnergyVec α Φ ξ < ⊤) :
    Integrable fun ω : ℝ =>
      (conj (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) • Φ (-(ω⁻¹ • ξ)) ω := by
  borelize Y
  have hΦm : Measurable fun ω : ℝ => Φ (-(ω⁻¹ • ξ)) ω :=
    hΦ.measurable.comp (measurable_raySubst.comp (measurable_const.prodMk measurable_id))
  have hmeas := (stronglyMeasurable_backprojectionOfVec_integrand α ρ hΦ).comp_measurable
    ((measurable_const (a := ξ)).prodMk measurable_id)
  have h2 : Integrable fun ω : ℝ => |ω| ^ (-α) * ‖Φ (-(ω⁻¹ • ξ)) ω‖ ^ 2 := by
    refine ⟨((continuous_abs.measurable.pow_const (-α)).mul
      (hΦm.norm.pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) hξ
    rw [Real.enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  refine Integrable.mono' (hρ.integrable.add h2) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  simp only [Pi.add_apply]
  rw [norm_smul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hw : 0 ≤ |ω| ^ (-α) := Real.rpow_nonneg (abs_nonneg _) _
  nlinarith [mul_nonneg hw (sq_nonneg (‖filterFourier ρ ω‖ - ‖Φ (-(ω⁻¹ • ξ)) ω‖)),
    mul_nonneg (mul_nonneg (norm_nonneg (filterFourier ρ ω)) hw)
      (norm_nonneg (Φ (-(ω⁻¹ • ξ)) ω))]

/-- The vector backprojection ray integral converges absolutely almost everywhere. -/
theorem IsHomogeneous.ae_integrable_backprojectionOfVec_integrand (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) {γ : H × ℝ → Y} (hγ : MemLp γ 2 (ν.prod volume))
    {Φ : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (h : HasBiasFourierVec ν γ Φ) :
    ∀ᵐ ξ ∂ν, Integrable fun ω : ℝ =>
      (conj (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) • Φ (-(ω⁻¹ • ξ)) ω := by
  have hfin : ∫⁻ ξ, rayEnergyVec α Φ ξ ∂ν < ⊤ := by
    rw [hν.lintegral_rayEnergyVec hΦ]
    exact (h.memLp_uncurry hγ hΦ).lintegral_enorm_sq_lt_top
  filter_upwards [ae_lt_top (measurable_rayEnergyVec α hΦ) hfin.ne] with ξ hξ
  exact integrable_backprojectionOfVec_integrand hρ hΦ hξ

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] in
/-- A bias-Fourier representative agrees with the angular partial Fourier unitary. -/
theorem HasBiasFourierVec.ae_eq_angularPartialFourierL2Equiv
    {γ : Lp Y 2 (parameterMeasure ν)} {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (h : HasBiasFourierVec ν γ Φ) :
    Function.uncurry Φ =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)]
      ⇑(angularPartialFourierL2Equiv ν γ) := by
  borelize Y
  obtain ⟨Ψ, hΨ, hB, he⟩ := exists_hasBiasFourierVec_angularPartialFourierL2Equiv ν γ
  apply Filter.EventuallyEq.trans _ he
  rw [Measure.prod_smul_right]
  apply Measure.ae_smul_measure
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hΦ.measurable hΨ.measurable)).mpr
    (h.ae_ae_eq hB)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] in
/-- Parseval's identity for two jointly measurable vector bias-Fourier representatives. -/
theorem HasBiasFourierVec.integral_inner
    {γ δ : Lp Y 2 (parameterMeasure ν)} {Φ Ψ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (h : HasBiasFourierVec ν γ Φ)
    (hΨ : StronglyMeasurable (Function.uncurry Ψ)) (h' : HasBiasFourierVec ν δ Ψ) :
    (∫ p, inner ℂ (γ p) (δ p) ∂parameterMeasure ν) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ p, inner ℂ (Function.uncurry Φ p) (Function.uncurry Ψ p) ∂ν.prod volume := by
  calc
    (∫ p, inner ℂ (γ p) (δ p) ∂parameterMeasure ν) = inner ℂ γ δ := rfl
    _ = inner ℂ (angularPartialFourierL2Equiv ν γ) (angularPartialFourierL2Equiv ν δ) :=
      ((angularPartialFourierL2Equiv ν).inner_map_map γ δ).symm
    _ = ∫ p, inner ℂ (Function.uncurry Φ p) (Function.uncurry Ψ p)
        ∂ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume) := by
      apply integral_congr_ae
      filter_upwards [h.ae_eq_angularPartialFourierL2Equiv hΦ,
        h'.ae_eq_angularPartialFourierL2Equiv hΨ] with p hp hq
      rw [hp, hq]
    _ = _ := by
      rw [Measure.prod_smul_right, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

variable (hν : IsHomogeneous α ν) (hα : 0 < α) (hρ : IsAdmissible α ρ)

omit [MeasurableSpace H] [BorelSpace H] [CompleteSpace Y] [SecondCountableTopology Y] in
/-- The explicit vector coefficient commutes with complex scalar multiplication. -/
theorem coefficientFormulaVec_const_smul (z : ℂ) (G : H → Y) :
    coefficientFormulaVec ρ (fun a => z • G a) = fun p => z • coefficientFormulaVec ρ G p := by
  funext p
  unfold coefficientFormulaVec
  rw [smul_comm z]
  congr 1
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with ω
  exact smul_comm _ z _

include hν hα hρ

/-- The vector coefficient operator respects scalar multiplication of square-integrable classes. -/
theorem spectralCoefficientVec_coeFn_smul (z : ℂ) (u : Lp Y 2 ν) :
    spectralCoefficientVec ν ρ (z • u : Lp Y 2 ν) = z • spectralCoefficientVec ν ρ u := by
  rw [spectralCoefficientVec_congr_ae hν ρ (Lp.coeFn_smul z u),
    spectralCoefficientVec_eq_toLp hν hα hρ ((Lp.stronglyMeasurable u).const_smul z)
      ((Lp.memLp u).const_smul z),
    spectralCoefficientVec_eq_toLp hν hα hρ (Lp.stronglyMeasurable u) (Lp.memLp u),
    ← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _
    (Eventually.of_forall (congrFun (coefficientFormulaVec_const_smul z u)))

/-- The vector coefficient operator is complex linear. -/
def spectralCoefficientVecLM : Lp Y 2 ν →ₗ[ℂ] Lp Y 2 (parameterMeasure ν) where
  toFun u := spectralCoefficientVec ν ρ u
  map_add' u v := by
    have hsub := spectralCoefficientVec_coeFn_sub hν hα hρ (u + v) v
    rw [add_sub_cancel_right] at hsub
    exact (sub_eq_iff_eq_add.mp hsub.symm)
  map_smul' z u := by
    simpa using spectralCoefficientVec_coeFn_smul hν hα hρ z u

/-- The vector coefficient operator has norm bound `sqrt C`. -/
theorem norm_spectralCoefficientVec_coeFn_le (u : Lp Y 2 ν) :
    ‖spectralCoefficientVec ν ρ u‖ ≤ Real.sqrt (admissibilityConst α ρ) * ‖u‖ := by
  refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_)
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_spectralCoefficientVec_coeFn_sq hν hα hρ]

/-- The vector coefficient operator as a bounded complex linear map. -/
def spectralCoefficientVecCLM : Lp Y 2 ν →L[ℂ] Lp Y 2 (parameterMeasure ν) :=
  (spectralCoefficientVecLM hν hα hρ).mkContinuous (Real.sqrt (admissibilityConst α ρ))
    (norm_spectralCoefficientVec_coeFn_le hν hα hρ)

/-- The bundled vector coefficient operator evaluates to the coefficient class. -/
theorem spectralCoefficientVecCLM_apply (u : Lp Y 2 ν) :
    spectralCoefficientVecCLM hν hα hρ u = spectralCoefficientVec ν ρ u := rfl

/-- The vector coefficient and backprojection are adjoint under the `L²` pairing. -/
theorem IsHomogeneous.inner_spectralCoefficientVec (γ : Lp Y 2 (parameterMeasure ν))
    (F : Lp Y 2 ν) :
    inner ℂ (spectralCoefficientVec ν ρ F) γ =
      ∫ ξ, inner ℂ (F ξ) (backprojectionVec α ν ρ γ ξ) ∂ν := by
  borelize Y
  obtain ⟨Φ, hΦ, hB, hΛ⟩ := backprojectionVec_eq_of_exists α ν ρ γ
  let Θ : H → ℝ → Y := fun a ω => filterFourier ρ ω • F (-(ω • a))
  have hΘ : StronglyMeasurable (Function.uncurry Θ) :=
    stronglyMeasurable_coefficient_representative_vec (Lp.stronglyMeasurable F)
  have hΘB : HasBiasFourierVec ν (spectralCoefficientVec ν ρ F) Θ := by
    apply (hasBiasFourierVec_coefficientFormulaVec hα hν hρ
      (Lp.stronglyMeasurable F) (Lp.memLp F)).congr_left
    rw [spectralCoefficientVec_eq_toLp hν hα hρ (Lp.stronglyMeasurable F) (Lp.memLp F)]
    exact (MemLp.coeFn_toLp _).symm
  have hΘ₂ := hΘB.memLp_uncurry (Lp.memLp _) hΘ
  have hΦ₂ := hB.memLp_uncurry (Lp.memLp γ) hΦ
  let K : H × ℝ → ℂ := fun p => inner ℂ (Function.uncurry Θ p) (Function.uncurry Φ p)
  have hK : Measurable K := (hΘ.inner hΦ).measurable
  have hKint : Integrable K (ν.prod volume) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (hΘ₂.toLp _) (hΦ₂.toLp _)).congr
    filter_upwards [hΘ₂.coeFn_toLp, hΦ₂.coeFn_toLp] with p hp hq
    simp only [hp, hq, K]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by simp [ae_iff]
  have hω0 : ∀ᵐ p ∂ν.prod (volume : Measure ℝ), p.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae h0
  rw [hΛ]
  calc
    inner ℂ (spectralCoefficientVec ν ρ F) γ =
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ p, K p ∂ν.prod volume :=
      hΘB.integral_inner hΘ hΦ hB
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ p,
        ((|p.2| ^ (-α) : ℝ) : ℂ) * K (raySubst p) ∂ν.prod volume := by
      rw [hν.integral_raySubst hKint.aestronglyMeasurable]
    _ = ∫ ξ, inner ℂ (F ξ) (backprojectionOfVec α ρ Φ ξ) ∂ν := by
      rw [integral_prod _ (hν.integrable_raySubst hK hKint), ← integral_smul]
      apply integral_congr_ae
      filter_upwards [hν.ae_integrable_backprojectionOfVec_integrand hρ (Lp.memLp γ) hΦ hB,
        Measure.ae_ae_of_ae_prod hω0] with ξ hξ h0
      have hbp : inner ℂ (F ξ) (backprojectionOfVec α ρ Φ ξ) =
          ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω, inner ℂ (F ξ)
            ((conj (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) • Φ (-(ω⁻¹ • ξ)) ω) := by
        unfold backprojectionOfVec
        rw [← Complex.coe_smul, inner_smul_right, ← integral_inner hξ, Complex.real_smul]
      rw [hbp]
      congr 1
      apply integral_congr_ae
      filter_upwards [h0] with ω hω
      have hξω : -(ω • -(ω⁻¹ • ξ)) = ξ := by
        rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
      simp only [K, Θ, Function.uncurry_apply_pair, raySubst, hξω,
        inner_smul_left, inner_smul_right]
      ring

omit hα in
/-- The chosen backprojection class is represented by the vector ray average. -/
theorem coeFn_backprojectionLpVec (γ : Lp Y 2 (parameterMeasure ν)) :
    ⇑(backprojectionLpVec α ν ρ γ) =ᵐ[ν] backprojectionVec α ν ρ γ := by
  have hm := (hν.memLp_backprojectionVec hρ γ).1
  unfold backprojectionLpVec
  rw [dif_pos hm]
  exact hm.coeFn_toLp

/-- The adjoint of the bounded vector coefficient operator is the backprojection. -/
theorem spectralCoefficientVecCLM_adjoint_apply (γ : Lp Y 2 (parameterMeasure ν)) :
    (spectralCoefficientVecCLM hν hα hρ).adjoint γ = backprojectionLpVec α ν ρ γ := by
  apply ext_inner_left ℂ
  intro F
  rw [ContinuousLinearMap.adjoint_inner_right, spectralCoefficientVecCLM_apply,
    hν.inner_spectralCoefficientVec hα hρ]
  apply integral_congr_ae
  filter_upwards [coeFn_backprojectionLpVec hν hρ γ] with ξ hξ
  rw [hξ]

/-- The vector coefficient operator has operator norm at most `sqrt C`. -/
theorem norm_spectralCoefficientVecCLM_le :
    ‖spectralCoefficientVecCLM (Y := Y) hν hα hρ‖ ≤ Real.sqrt (admissibilityConst α ρ) :=
  (spectralCoefficientVecCLM (Y := Y) hν hα hρ).opNorm_le_bound (Real.sqrt_nonneg _)
    (norm_spectralCoefficientVec_coeFn_le hν hα hρ)

/-- The vector backprojection has norm at most `sqrt C` times the coefficient norm. -/
theorem norm_backprojectionLpVec_le (γ : Lp Y 2 (parameterMeasure ν)) :
    ‖backprojectionLpVec α ν ρ γ‖ ≤ Real.sqrt (admissibilityConst α ρ) * ‖γ‖ := by
  rw [← spectralCoefficientVecCLM_adjoint_apply hν hα hρ]
  apply ((spectralCoefficientVecCLM (Y := Y) hν hα hρ).adjoint.le_opNorm γ).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa using norm_spectralCoefficientVecCLM_le (Y := Y) hν hα hρ

/-- Applying the adjoint after vector coefficient analysis yields the admissibility constant. -/
theorem spectralCoefficientVecCLM_adjoint_apply_self (F : Lp Y 2 ν) :
    (spectralCoefficientVecCLM hν hα hρ).adjoint (spectralCoefficientVecCLM hν hα hρ F) =
      (admissibilityConst α ρ : ℂ) • F := by
  rw [spectralCoefficientVecCLM_apply, spectralCoefficientVecCLM_adjoint_apply]
  apply Lp.ext
  exact (coeFn_backprojectionLpVec hν hρ _).trans
    ((hν.backprojectionVec_spectralCoefficientVec hα hρ
      (Lp.stronglyMeasurable F) (Lp.memLp F)).trans (Lp.coeFn_smul _ _).symm)

/-- The bounded coefficient operator has the ray-average adjoint and the scaled left inverse. -/
theorem exists_spectralCoefficientVecCLM_adjoint :
    ∃ W : Lp Y 2 ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      (∀ F, W F = spectralCoefficientVec ν ρ F) ∧
      (∀ γ, W.adjoint γ = backprojectionLpVec α ν ρ γ) ∧
      ‖W‖ ≤ Real.sqrt (admissibilityConst α ρ) ∧
      (∀ γ : Lp Y 2 (parameterMeasure ν), ‖backprojectionLpVec α ν ρ γ‖ ≤
        Real.sqrt (admissibilityConst α ρ) * ‖γ‖) ∧
      ∀ F, W.adjoint (W F) = (admissibilityConst α ρ : ℂ) • F :=
  ⟨spectralCoefficientVecCLM hν hα hρ, spectralCoefficientVecCLM_apply hν hα hρ,
    spectralCoefficientVecCLM_adjoint_apply hν hα hρ, norm_spectralCoefficientVecCLM_le hν hα hρ,
    norm_backprojectionLpVec_le hν hα hρ, spectralCoefficientVecCLM_adjoint_apply_self hν hα hρ⟩

omit hα hρ in
/-- Every jointly measurable Fourier representative gives the same vector backprojection. -/
theorem IsHomogeneous.backprojectionVec_ae_eq_of_hasBiasFourierVec
    (γ : Lp Y 2 (parameterMeasure ν)) {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (hB : HasBiasFourierVec ν γ Φ) :
    backprojectionVec α ν ρ γ =ᵐ[ν] backprojectionOfVec α ρ Φ := by
  obtain ⟨Ψ, hΨ, hΨB, hΛ⟩ := backprojectionVec_eq_of_exists α ν ρ γ
  rw [hΛ]
  exact hν.backprojectionOfVec_ae_eq ρ hΨ hΦ hΨB hB

end OperatorRidgelet
