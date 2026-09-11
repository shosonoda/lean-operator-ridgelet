import OperatorRidgelet.Reconstruction.VectorCoefficient
import OperatorRidgelet.Reconstruction.Backprojection
import OperatorRidgelet.ToMathlib.HilbertBasisIntegral

/-! # Bounded vector-valued backprojection and inversion of the coefficient operator -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

variable {H Y : Type*} [MeasurableSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] {ν : Measure H} [SFinite ν]

/-- A scalar square-integrable test function pairs integrably with a vector-valued one. -/
theorem integrable_conj_smul_vec {f : ℝ → Y} {g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => (starRingEnd ℂ) (g x) • f x) := by
  have hc : MemLp (fun x => (starRingEnd ℂ) (g x)) 2 volume :=
    hg.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun x => le_of_eq (Complex.norm_conj (g x)))
  exact memLp_one_iff_integrable.mp (hf.smul hc)

/-- Pairing a vector-valued bias Fourier identity with a fixed vector gives the scalar identity. -/
theorem HasBiasFourierVec.const_inner {γ : H × ℝ → Y} (hγ : MemLp γ 2 (ν.prod volume))
    {Φ : H → ℝ → Y} (h : HasBiasFourierVec ν γ Φ) (y : Y) :
    HasBiasFourier ν (fun p => inner ℂ y (γ p)) (fun a ω => inner ℂ y (Φ a ω)) := by
  refine ⟨h.memLp.mono (fun a ha => ha.const_inner y), ?_⟩
  filter_upwards [h.parseval, h.memLp, ae_memLp_slice_vec hγ] with a ha hΦa hγa φ
  have hL := (innerSL ℂ y).integral_comp_comm (integrable_schwartz_smul_vec hγa φ)
  have hR := (innerSL ℂ y).integral_comp_comm
    (integrable_conj_smul_vec hΦa (memLp_lineFourier φ))
  have he := congrArg (inner ℂ y) (ha φ)
  rw [← Complex.coe_smul, inner_smul_right] at he
  simp only [innerSL_apply_apply] at hL hR
  rw [← hL, ← hR] at he
  simpa only [inner_smul_right, mul_comm] using he

/-- The product Plancherel identity for a jointly strongly measurable vector representative. -/
theorem HasBiasFourierVec.lintegral_uncurry_enorm_sq {γ : H × ℝ → Y}
    (hγ : MemLp γ 2 (ν.prod volume)) {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (h : HasBiasFourierVec ν γ Φ) :
    ∫⁻ p, ‖Function.uncurry Φ p‖ₑ ^ 2 ∂ν.prod volume =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂ν.prod volume := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ Y
  letI : Countable ι := b.orthonormal.countable_index
  rw [b.lintegral_enorm_sq hΦ.aestronglyMeasurable, b.lintegral_enorm_sq hγ.1,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro i
  have hm : Measurable (Function.uncurry fun a ω => inner ℂ (b i) (Φ a ω)) :=
    ((innerSL ℂ (b i)).continuous.comp_stronglyMeasurable hΦ).measurable
  exact HasBiasFourier.lintegral_uncurry_enorm_sq (hγ.const_inner (b i)) hm
    (h.const_inner hγ (b i))

/-- A strongly measurable vector bias Fourier representative is square integrable on the product. -/
theorem HasBiasFourierVec.memLp_uncurry {γ : H × ℝ → Y}
    (hγ : MemLp γ 2 (ν.prod volume)) {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) (h : HasBiasFourierVec ν γ Φ) :
    MemLp (Function.uncurry Φ) 2 (ν.prod volume) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top hΦ.aestronglyMeasurable ?_
  rw [h.lintegral_uncurry_enorm_sq hγ hΦ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγ.lintegral_enorm_sq_lt_top

/-- Square-integrable vector-valued functions are determined by Fourier-Schwartz tests. -/
theorem ae_eq_of_forall_integral_conj_lineFourier_smul_eq {f g : ℝ → Y}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ ω, (starRingEnd ℂ) (lineFourier φ ω) • f ω =
        ∫ ω, (starRingEnd ℂ) (lineFourier φ ω) • g ω) : f =ᵐ[volume] g := by
  have hloc : LocallyIntegrable (fun ω => f ω - g ω) volume :=
    (hf.sub hg).locallyIntegrable one_le_two
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun r hr hrs => ?_
  · filter_upwards [h0] with ω hω
    exact sub_eq_zero.mp hω
  obtain ⟨φ, hφ⟩ := exists_schwartz_lineFourier_eq hr hrs
  have hval : ∀ ω, r ω • (f ω - g ω) =
      (starRingEnd ℂ) (lineFourier φ ω) • f ω -
        (starRingEnd ℂ) (lineFourier φ ω) • g ω := by
    intro ω
    simp only [hφ ω, Complex.conj_ofReal, Complex.coe_smul, smul_sub]
  simp_rw [hval]
  rw [integral_sub (integrable_conj_smul_vec hf (memLp_lineFourier φ))
      (integrable_conj_smul_vec hg (memLp_lineFourier φ)), h φ, sub_self]

/-- Two vector-valued Fourier representatives of the same coefficient agree almost everywhere. -/
theorem HasBiasFourierVec.ae_ae_eq {γ : H × ℝ → Y} {Φ Φ' : H → ℝ → Y}
    (h : HasBiasFourierVec ν γ Φ) (h' : HasBiasFourierVec ν γ Φ') :
    ∀ᵐ a ∂ν, Φ a =ᵐ[volume] Φ' a := by
  filter_upwards [h.memLp, h'.memLp, h.parseval, h'.parseval] with a h1 h2 h3 h4
  apply ae_eq_of_forall_integral_conj_lineFourier_smul_eq h1 h2
  intro φ
  exact smul_right_injective Y (by positivity : (2 * Real.pi)⁻¹ ≠ (0 : ℝ))
    ((h3 φ).symm.trans (h4 φ))

section Rays

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H]

/-- The integrand of a vector-valued ray average is jointly strongly measurable. -/
theorem stronglyMeasurable_backprojectionOfVec_integrand (α : ℝ) (ρ : SchwartzMap ℝ ℝ)
    {Φ : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ)) :
    StronglyMeasurable fun p : H × ℝ => ((starRingEnd ℂ) (filterFourier ρ p.2) *
      ((|p.2| ^ (-α) : ℝ) : ℂ)) • Φ (-(p.2⁻¹ • p.1)) p.2 :=
  (((Complex.continuous_conj.comp (continuous_filterFourier ρ)).measurable.comp
    measurable_snd).mul (Complex.measurable_ofReal.comp
      ((continuous_abs.measurable.comp measurable_snd).pow_const (-α)))).stronglyMeasurable.smul
    (hΦ.comp_measurable measurable_raySubst)

/-- The vector-valued ray average is strongly measurable. -/
theorem stronglyMeasurable_backprojectionOfVec (α : ℝ) (ρ : SchwartzMap ℝ ℝ)
    {Φ : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ)) :
    StronglyMeasurable (backprojectionOfVec α ρ Φ) :=
  (stronglyMeasurable_backprojectionOfVec_integrand α ρ hΦ).integral_prod_right'.const_smul _

/-- The weighted squared norm of a vector-valued Fourier representative on a ray. -/
def rayEnergyVec (α : ℝ) (Φ : H → ℝ → Y) (ξ : H) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|ω| ^ (-α)) * ‖Φ (-(ω⁻¹ • ξ)) ω‖ₑ ^ 2

/-- The vector ray energy is measurable. -/
theorem measurable_rayEnergyVec (α : ℝ) {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) : Measurable (rayEnergyVec α Φ) :=
  ((measurable_rayWeight α).mul
    ((hΦ.comp_measurable measurable_raySubst).enorm.pow_const 2)).lintegral_prod_right'

variable {α : ℝ} (hν : IsHomogeneous α ν)
include hν

/-- Integrating the vector ray energy recovers the squared norm on the product space. -/
theorem IsHomogeneous.lintegral_rayEnergyVec {Φ : H → ℝ → Y}
    (hΦ : StronglyMeasurable (Function.uncurry Φ)) :
    ∫⁻ ξ, rayEnergyVec α Φ ξ ∂ν = ∫⁻ p, ‖Function.uncurry Φ p‖ₑ ^ 2 ∂ν.prod volume := by
  unfold rayEnergyVec
  rw [← hν.lintegral_raySubst (hΦ.enorm.pow_const 2), lintegral_prod
    (fun p : H × ℝ => ENNReal.ofReal (|p.2| ^ (-α)) * ‖Function.uncurry Φ (raySubst p)‖ₑ ^ 2)
    ((measurable_rayWeight α).mul
      ((hΦ.comp_measurable measurable_raySubst).enorm.pow_const 2)).aemeasurable]
  rfl

omit hν in
/-- Weighted Cauchy–Schwarz bounds the squared norm of the vector ray average. -/
theorem enorm_backprojectionOfVec_sq_le {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
    {Φ : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ)) (ξ : H) :
    ‖backprojectionOfVec α ρ Φ ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergyVec α Φ ξ := by
  borelize Y
  set f : ℝ → ℂ := fun ω => filterFourier ρ ω * ((|ω| ^ (-α / 2) : ℝ) : ℂ) with hf
  set g : ℝ → Y := fun ω => ((|ω| ^ (-α / 2) : ℝ) : ℂ) • Φ (-(ω⁻¹ • ξ)) ω with hg
  have hΦm : Measurable fun ω : ℝ => Φ (-(ω⁻¹ • ξ)) ω :=
    hΦ.measurable.comp (measurable_raySubst.comp (measurable_const.prodMk measurable_id))
  have hwm : Measurable fun ω : ℝ => ((|ω| ^ (-α / 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (continuous_abs.measurable.pow_const _)
  have hfm : AEMeasurable f volume := ((continuous_filterFourier ρ).measurable.mul hwm).aemeasurable
  have hgm : AEMeasurable g volume := (hwm.smul hΦm).aemeasurable
  have hw : ∀ ω : ℝ, ‖((|ω| ^ (-α / 2) : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (|ω| ^ (-α)) := by
    intro ω
    rw [enorm_ofReal_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← ENNReal.ofReal_pow
      (Real.rpow_nonneg (abs_nonneg _) _), rpow_neg_eq_sq]
  have hpt : ∀ ω, ‖((starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) •
      Φ (-(ω⁻¹ • ξ)) ω‖ₑ = ‖f ω‖ₑ * ‖g ω‖ₑ := by
    intro ω
    simp only [hf, hg, enorm_smul, enorm_mul, RCLike.enorm_conj]
    rw [enorm_ofReal_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← hw ω, sq]
    ring
  have hf2 : ∫⁻ ω, ‖f ω‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi * admissibilityConst α ρ) := by
    rw [← hρ.lintegral_enorm_sq_mul]
    refine lintegral_congr fun ω => ?_
    simp only [hf, enorm_smul, enorm_mul, mul_pow, hw]
  have hg2 : ∫⁻ ω, ‖g ω‖ₑ ^ 2 = rayEnergyVec α Φ ξ := by
    unfold rayEnergyVec
    refine lintegral_congr fun ω => ?_
    simp only [hg, enorm_smul, enorm_mul, mul_pow, hw]
  have hCS := lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two volume hfm hgm
  have h1 : ‖backprojectionOfVec α ρ Φ ξ‖ₑ ≤
      ENNReal.ofReal (2 * Real.pi)⁻¹ * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by
    unfold backprojectionOfVec
    rw [enorm_smul, Real.enorm_eq_ofReal (by positivity)]
    refine mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans ?_)
    simp_rw [hpt]
    exact hCS
  calc ‖backprojectionOfVec α ρ Φ ξ‖ₑ ^ 2
      ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ * (eLpNorm f 2 volume * eLpNorm g 2 volume)) ^ 2 :=
        ENNReal.pow_le_pow_left h1
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 2 * ((∫⁻ ω, ‖f ω‖ₑ ^ 2) * ∫⁻ ω, ‖g ω‖ₑ ^ 2) := by
        rw [mul_pow, mul_pow, eLpNorm_two_sq_eq_lintegral_enorm_sq',
          eLpNorm_two_sq_eq_lintegral_enorm_sq']
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergyVec α Φ ξ := by
        rw [hf2, hg2, ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- The vector-valued backprojection has operator bound given by the admissibility constant. -/
theorem IsHomogeneous.memLp_backprojectionVec {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsAdmissible α ρ) (γ : Lp Y 2 (parameterMeasure ν)) :
    MemLp (backprojectionVec α ν ρ γ) 2 ν ∧
      ∫ ξ, ‖backprojectionVec α ν ρ γ ξ‖ ^ 2 ∂ν ≤ admissibilityConst α ρ * ‖γ‖ ^ 2 := by
  unfold backprojectionVec
  split_ifs with hex
  swap
  · refine ⟨MemLp.zero, ?_⟩
    simp only [Pi.zero_apply, norm_zero, zero_pow (by omega : 2 ≠ 0), integral_zero]
    exact mul_nonneg hρ.pos.le (sq_nonneg _)
  let Φ := hex.choose
  have hΦ : StronglyMeasurable (Function.uncurry Φ) := hex.choose_spec.1
  have hγΦ : HasBiasFourierVec ν γ Φ := hex.choose_spec.2
  have hmeas := stronglyMeasurable_backprojectionOfVec α ρ hΦ
  have hlin : ∫⁻ ξ, ‖backprojectionOfVec α ρ Φ ξ‖ₑ ^ 2 ∂ν ≤
      ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν := by
    calc ∫⁻ ξ, ‖backprojectionOfVec α ρ Φ ξ‖ₑ ^ 2 ∂ν
        ≤ ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergyVec α Φ ξ ∂ν :=
          lintegral_mono fun ξ => enorm_backprojectionOfVec_sq_le hρ hΦ ξ
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) *
            (ENNReal.ofReal (2 * Real.pi) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν) := by
          rw [lintegral_const_mul _ (measurable_rayEnergyVec α hΦ), hν.lintegral_rayEnergyVec hΦ,
            hγΦ.lintegral_uncurry_enorm_sq (Lp.memLp γ) hΦ]
          rfl
      _ = ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hρ.pos.le)]
          congr 2
          field_simp
  have hfin : ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp γ).lintegral_enorm_sq_lt_top).ne
  refine ⟨memLp_two_of_lintegral_enorm_sq_lt_top hmeas.aestronglyMeasurable
    (hlin.trans_lt hfin.lt_top), ?_⟩
  rw [integral_norm_sq_eq_toReal_lintegral' hmeas.aestronglyMeasurable,
    Lp.norm_sq_eq_integral_norm_sq, integral_norm_sq_eq_toReal_lintegral'
    (Lp.aestronglyMeasurable γ), ← ENNReal.toReal_ofReal hρ.pos.le, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin hlin

omit hν in
/-- The representative of a vector coefficient operator is jointly strongly measurable. -/
theorem stronglyMeasurable_coefficient_representative_vec {ρ : SchwartzMap ℝ ℝ} {F : H → Y}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (Function.uncurry fun a ω => filterFourier ρ ω • F (-(ω • a))) :=
  ((continuous_filterFourier ρ).measurable.comp measurable_snd).stronglyMeasurable.smul
    (hF.comp_measurable (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable)

/-- The vector-valued ray average depends only on the Fourier representative's
almost-everywhere class. -/
theorem IsHomogeneous.backprojectionOfVec_ae_eq (ρ : ℝ → ℝ) {γ : H × ℝ → Y}
    {Φ Φ' : H → ℝ → Y} (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hΦ' : StronglyMeasurable (Function.uncurry Φ'))
    (h : HasBiasFourierVec ν γ Φ) (h' : HasBiasFourierVec ν γ Φ') :
    backprojectionOfVec α ρ Φ =ᵐ[ν] backprojectionOfVec α ρ Φ' := by
  borelize Y
  have hae : Function.uncurry Φ =ᵐ[ν.prod volume] Function.uncurry Φ' :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hΦ.measurable hΦ'.measurable)).mpr
      (h.ae_ae_eq h')
  have hae' := hν.quasiMeasurePreserving_raySubst.ae_eq_comp hae
  filter_upwards [Measure.ae_ae_of_ae_prod hae'] with ξ hξ
  unfold backprojectionOfVec
  congr 1
  apply integral_congr_ae
  filter_upwards [hξ] with ω hω
  exact congrArg _ hω

omit hν in
/-- The ray average of an explicit vector coefficient representative is the admissibility constant
times its spectral density. -/
theorem backprojectionOfVec_coefficient_representative (α : ℝ) (ρ : SchwartzMap ℝ ℝ)
    (F : H → Y) (ξ : H) :
    backprojectionOfVec α ρ (fun a ω => filterFourier ρ ω • F (-(ω • a))) ξ =
      (admissibilityConst α ρ : ℂ) • F ξ := by
  unfold backprojectionOfVec admissibilityConst
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  rw [Complex.ofReal_mul, mul_smul, Complex.coe_smul]
  congr 1
  calc ∫ ω, ((starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) •
        (filterFourier ρ ω • F (-(ω • -(ω⁻¹ • ξ))))
      = ∫ ω, ((‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ) • F ξ := by
        apply integral_congr_ae
        filter_upwards [h0] with ω hω
        have hξ : -(ω • -(ω⁻¹ • ξ)) = ξ := by
          rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
        rw [hξ, smul_smul, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        congr 1
        ring
    _ = _ := by
      rw [integral_smul_const]
      congr 1
      exact integral_ofReal

/-- Backprojection inverts the vector coefficient operator up to the admissibility constant. -/
theorem IsHomogeneous.backprojectionVec_spectralCoefficientVec {ρ : SchwartzMap ℝ ℝ}
    (hα : 0 < α) (hρ : IsAdmissible α ρ) {F : H → Y}
    (hF : StronglyMeasurable F) (hF₂ : MemLp F 2 ν) :
    backprojectionVec α ν ρ (spectralCoefficientVec ν ρ F) =ᵐ[ν]
      fun ξ => (admissibilityConst α ρ : ℂ) • F ξ := by
  have hΘ : HasBiasFourierVec ν (spectralCoefficientVec ν ρ F)
      (fun a ω => filterFourier ρ ω • F (-(ω • a))) :=
    (hasBiasFourierVec_coefficientFormulaVec hα hν hρ hF hF₂).congr_left (by
      rw [spectralCoefficientVec_eq_toLp hν hα hρ hF hF₂]
      exact (MemLp.coeFn_toLp _).symm)
  have hex : ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
      HasBiasFourierVec ν (spectralCoefficientVec ν ρ F) Φ :=
    ⟨_, stronglyMeasurable_coefficient_representative_vec hF, hΘ⟩
  unfold backprojectionVec
  rw [dif_pos hex]
  filter_upwards [hν.backprojectionOfVec_ae_eq ρ hex.choose_spec.1
    (stronglyMeasurable_coefficient_representative_vec hF) hex.choose_spec.2 hΘ] with ξ hξ
  rw [hξ, backprojectionOfVec_coefficient_representative]

end Rays

end OperatorRidgelet
