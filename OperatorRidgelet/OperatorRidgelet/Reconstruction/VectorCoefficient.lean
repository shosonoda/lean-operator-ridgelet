import OperatorRidgelet.Reconstruction.VectorValued
import OperatorRidgelet.Examples.SliceCoefficientVec

/-! # The vector-valued coefficient operator

Uniqueness of bias Fourier transforms, the Plancherel identity for the explicit coefficient,
and the factorization of the ridgelet extension through its spectral density. -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform
variable {H Y : Type*} [MeasurableSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

/-- Multiplication of a vector-valued square-integrable function by a Schwartz test function
is integrable. -/
theorem integrable_schwartz_smul_vec {f : ℝ → Y} (hf : MemLp f 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun c => (starRingEnd ℂ) (φ c) • f c) := by
  have hc : MemLp (fun c => (starRingEnd ℂ) (φ c)) 2 volume :=
    (φ.memLp 2 volume).of_le (Complex.continuous_conj.comp φ.continuous).aestronglyMeasurable
      (Eventually.of_forall fun c => le_of_eq (Complex.norm_conj (φ c)))
  exact memLp_one_iff_integrable.mp (hf.smul hc)

/-- Almost every bias section of a square-integrable vector function is square integrable. -/
theorem ae_memLp_slice_vec {ν : Measure H} [SFinite ν] {γ : H × ℝ → Y}
    (h : MemLp γ 2 (ν.prod volume)) :
    ∀ᵐ a ∂ν, MemLp (fun c : ℝ => γ (a, c)) 2 volume := by
  filter_upwards [h.integrable_norm_sq.prod_right_ae, h.aestronglyMeasurable.prodMk_left]
    with a ha hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ha

/-- `HasBiasFourierVec` only depends on the `λ`-class of `γ`. -/
theorem HasBiasFourierVec.congr_left {ν : Measure H} [SFinite ν] {γ γ' : H × ℝ → Y}
    {Φ : H → ℝ → Y} (h : HasBiasFourierVec ν γ Φ) (hγ : γ =ᵐ[ν.prod volume] γ') :
    HasBiasFourierVec ν γ' Φ := by
  refine ⟨h.memLp, ?_⟩
  filter_upwards [h.parseval, Measure.ae_ae_of_ae_prod hγ] with a ha hae φ
  rw [← ha φ]
  apply integral_congr_ae
  filter_upwards [hae] with c hc
  rw [hc]

/-- `HasBiasFourierVec` only depends on the almost-everywhere classes of the ray functions
`Φ a`. -/
theorem HasBiasFourierVec.congr_right {ν : Measure H} {γ : H × ℝ → Y} {Φ Φ' : H → ℝ → Y}
    (h : HasBiasFourierVec ν γ Φ) (hΦ : ∀ᵐ a ∂ν, Φ a =ᵐ[volume] Φ' a) :
    HasBiasFourierVec ν γ Φ' := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.memLp, hΦ] with a ha hae
    exact ha.ae_eq hae
  filter_upwards [h.parseval, hΦ] with a ha hae φ
  rw [ha φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hae] with ω hω
  rw [hω]

/-- **Uniqueness**: two square-integrable functions on `H × ℝ` with the same partial Fourier
transform in the bias agree `λ`-almost everywhere. -/
theorem HasBiasFourierVec.ae_eq {ν : Measure H} [SFinite ν] {γ₁ γ₂ : H × ℝ → Y}
    (h₁ : MemLp γ₁ 2 (ν.prod volume)) (h₂ : MemLp γ₂ 2 (ν.prod volume)) {Φ : H → ℝ → Y}
    (hΦ₁ : HasBiasFourierVec ν γ₁ Φ) (hΦ₂ : HasBiasFourierVec ν γ₂ Φ) :
    γ₁ =ᵐ[ν.prod volume] γ₂ := by
  borelize Y
  have key : ∀ᵐ a ∂ν, ∀ᵐ c : ℝ ∂volume, γ₁ (a, c) = γ₂ (a, c) := by
    filter_upwards [hΦ₁.parseval, hΦ₂.parseval, ae_memLp_slice_vec h₁, ae_memLp_slice_vec h₂]
      with a ha₁ ha₂ hm₁ hm₂
    have hloc : LocallyIntegrable (fun c : ℝ => γ₁ (a, c) - γ₂ (a, c)) volume :=
      (hm₁.sub hm₂).locallyIntegrable one_le_two
    have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g g_diff g_supp => ?_
    · filter_upwards [h0] with c hc
      exact sub_eq_zero.mp hc
    · have hr₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_supp.comp_left rfl
      have hr₂ := Complex.ofRealCLM.contDiff.comp g_diff
      set φ : SchwartzMap ℝ ℂ := hr₁.toSchwartzMap hr₂ with hφ
      have hval : ∀ c : ℝ, g c • (γ₁ (a, c) - γ₂ (a, c)) =
          (starRingEnd ℂ) (φ c) • γ₁ (a, c) - (starRingEnd ℂ) (φ c) • γ₂ (a, c) := by
        intro c
        change g c • (γ₁ (a, c) - γ₂ (a, c)) =
          (starRingEnd ℂ) ((g c : ℂ)) • γ₁ (a, c) - (starRingEnd ℂ) ((g c : ℂ)) • γ₂ (a, c)
        simp only [Complex.conj_ofReal, Complex.coe_smul, smul_sub]
      simp_rw [hval]
      rw [integral_sub (integrable_schwartz_smul_vec hm₁ φ) (integrable_schwartz_smul_vec hm₂ φ),
        ha₁ φ, ha₂ φ, sub_self]
  set γ₁' := h₁.1.mk γ₁ with hγ₁'
  set γ₂' := h₂.1.mk γ₂ with hγ₂'
  have e₁ : γ₁ =ᵐ[ν.prod volume] γ₁' := h₁.1.ae_eq_mk
  have e₂ : γ₂ =ᵐ[ν.prod volume] γ₂' := h₂.1.ae_eq_mk
  have key' : ∀ᵐ a ∂ν, ∀ᵐ c : ℝ ∂volume, γ₁' (a, c) = γ₂' (a, c) := by
    filter_upwards [key, Measure.ae_ae_of_ae_prod e₁, Measure.ae_ae_of_ae_prod e₂]
      with a ha ha₁ ha₂
    filter_upwards [ha, ha₁, ha₂] with c hc hc₁ hc₂
    rw [← hc₁, ← hc₂, hc]
  have hprod : ∀ᵐ z ∂ν.prod volume, γ₁' z = γ₂' z :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun h₁.1.stronglyMeasurable_mk.measurable
      h₂.1.stronglyMeasurable_mk.measurable)).mpr key'
  filter_upwards [hprod, e₁, e₂] with z hz hz₁ hz₂
  rw [hz₁, hz₂, hz]


section Coefficient

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H]
  {ν : Measure H} [SFinite ν] {α : ℝ} {ρ : SchwartzMap ℝ ℝ} {G : H → Y}

/-- Almost every spectral ray of a square-integrable vector density is square integrable. -/
theorem ae_memLp_ray_vec (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    ∀ᵐ a ∂ν, MemLp (fun ω : ℝ => filterFourier ρ ω • G (-(ω • a))) 2 volume := by
  apply ae_memLp_slice_vec (γ := fun p : H × ℝ => filterFourier ρ p.2 • G (-(p.2 • p.1)))
  refine memLp_two_of_lintegral_enorm_sq_lt_top ?_ ?_
  · exact (((continuous_filterFourier ρ).measurable.comp measurable_snd).stronglyMeasurable.smul
      (hG.comp_measurable (by fun_prop : Continuous fun p : H × ℝ =>
        -(p.2 • p.1)).measurable)).aestronglyMeasurable
  · simp only [enorm_smul, mul_pow]
    exact hρ.lintegral_prod_enorm_sq_vec_lt_top hν hG.enorm hG₂

/-- Plancherel's identity along a vector-valued spectral ray. -/
theorem lintegral_coefficientFormulaVec_slice_sq (ρ : SchwartzMap ℝ ℝ)
    (hG : StronglyMeasurable G) {a : H}
    (ha₁ : Integrable fun ω : ℝ => filterFourier ρ ω • G (-(ω • a)))
    (ha₂ : MemLp (fun ω : ℝ => filterFourier ρ ω • G (-(ω • a))) 2 volume) :
    ∫⁻ c, ‖coefficientFormulaVec ρ G (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
  set Ψ : ℝ → Y := fun u => filterFourier ρ (2 * Real.pi * u) • G (-((2 * Real.pi * u) • a))
    with hΨ
  have hΦmeas : StronglyMeasurable fun ω : ℝ => filterFourier ρ ω • G (-(ω • a)) :=
    (continuous_filterFourier ρ).stronglyMeasurable.smul
      (hG.comp_measurable (by fun_prop : Continuous fun ω : ℝ => -(ω • a)).measurable)
  have hΨ₁ : Integrable Ψ := ha₁.comp_mul_left' (by positivity)
  have hΨsq : ∫⁻ u, ‖Ψ u‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi)⁻¹ *
      ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
    have := lintegral_comp_mul_left_real
      (F := fun ω => ‖filterFourier ρ ω • G (-(ω • a))‖ₑ ^ 2) (hΦmeas.enorm.pow_const 2)
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [abs_of_pos (by positivity)] at this
    simp only [hΨ, enorm_smul, mul_pow] at this ⊢
    exact this
  have hΨ₂ : MemLp Ψ 2 volume := by
    refine memLp_two_of_lintegral_enorm_sq_lt_top hΨ₁.aestronglyMeasurable ?_
    rw [hΨsq]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have := ha₂.lintegral_enorm_sq_lt_top
    simpa only [enorm_smul, mul_pow] using this
  calc ∫⁻ c, ‖coefficientFormulaVec ρ G (a, c)‖ₑ ^ 2
      = ∫⁻ c, ‖𝓕 Ψ (-c)‖ₑ ^ 2 := by
        refine lintegral_congr fun c => ?_
        rw [coefficientFormulaVec_eq_fourier ρ G a c]
    _ = ∫⁻ c, ‖𝓕 Ψ c‖ₑ ^ 2 := lintegral_neg_eq_self (fun c => ‖𝓕 Ψ c‖ₑ ^ 2)
    _ = ∫⁻ u, ‖Ψ u‖ₑ ^ 2 := hΨ₁.lintegral_enorm_fourier_sq hΨ₂
    _ = _ := hΨsq

/-- The squared `L²(λ)` norm of the explicit coefficient:
`∫⁻ ‖γ_G‖ₑ² dλ = C_ρ ∫⁻ ‖G‖ₑ² dν`. -/
theorem lintegral_coefficientFormulaVec_sq (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    ∫⁻ p, ‖coefficientFormulaVec ρ G p‖ₑ ^ 2 ∂parameterMeasure ν =
      ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  have hmeas : Measurable fun p : H × ℝ => ‖coefficientFormulaVec ρ G p‖ₑ ^ 2 :=
    (stronglyMeasurable_coefficientFormulaVec ρ hG).enorm.pow_const 2
  have hmeas' : Measurable fun p : H × ℝ =>
      ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 :=
    (((continuous_filterFourier ρ).comp continuous_snd).measurable.enorm.pow_const 2).mul
      ((hG.comp_measurable hc.measurable).enorm.pow_const 2)
  unfold parameterMeasure
  rw [lintegral_prod _ hmeas.aemeasurable]
  have key : ∀ᵐ a ∂ν, ∫⁻ c, ‖coefficientFormulaVec ρ G (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖G (-(ω • a))‖ₑ ^ 2 := by
    filter_upwards [ae_integrable_ray_vec hα hν hρ hG hG₂,
      ae_memLp_ray_vec hν hρ hG hG₂] with a ha₁ ha₂
    exact lintegral_coefficientFormulaVec_slice_sq ρ hG ha₁ ha₂
  rw [lintegral_congr_ae key, lintegral_const_mul _ hmeas'.lintegral_prod_right',
    ← lintegral_prod _ hmeas'.aemeasurable, hρ.lintegral_prod_enorm_sq_vec hν hG.enorm, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel_left₀ (by positivity)]

/-- The explicit coefficient `γ_G` is square integrable on `H × ℝ`. -/
theorem memLp_coefficientFormulaVec (hα : 0 < α) (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    MemLp (coefficientFormulaVec ρ G) 2 (parameterMeasure ν) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top
    (stronglyMeasurable_coefficientFormulaVec ρ hG).aestronglyMeasurable ?_
  rw [lintegral_coefficientFormulaVec_sq hα hν hρ hG hG₂]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hG₂.lintegral_enorm_sq_lt_top)

/-- The scaled isometry `‖γ_G‖²_{L²(λ)} = C_ρ ‖G‖²_{L²(ν)}`. -/
theorem integral_coefficientFormulaVec_norm_sq (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖coefficientFormulaVec ρ G p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν := by
  rw [integral_norm_sq_eq_toReal_lintegral
      (stronglyMeasurable_coefficientFormulaVec ρ hG).aestronglyMeasurable,
    integral_norm_sq_eq_toReal_lintegral hG.aestronglyMeasurable,
    lintegral_coefficientFormulaVec_sq hα hν hρ hG hG₂, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.pos.le]

/-- The explicit vector coefficient has the prescribed partial Fourier transform. -/
theorem hasBiasFourierVec_coefficientFormulaVec (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    HasBiasFourierVec ν (coefficientFormulaVec ρ G)
      (fun a ω => filterFourier ρ ω • G (-(ω • a))) := by
  refine ⟨ae_memLp_ray_vec hν hρ hG hG₂, ?_⟩
  filter_upwards [ae_integrable_ray_vec hα hν hρ hG hG₂] with a ha φ
  let Φ : ℝ → Y := fun ω => filterFourier ρ ω • G (-(ω • a))
  have hb := (integrable_conj_schwartz φ).smul_prod ha
  have hint : Integrable (fun z : ℝ × ℝ =>
      ((starRingEnd ℂ) (φ z.1) * Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)) • Φ z.2)
      (volume.prod volume) := by
    have hm := (by fun_prop : Continuous fun z : ℝ × ℝ =>
      Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)).aestronglyMeasurable.smul
        hb.aestronglyMeasurable
    refine hb.norm.mono' (hm.congr (Eventually.of_forall fun z => ?_))
      (Eventually.of_forall fun z => ?_)
    · change Complex.exp ((z.2 * z.1 : ℝ) * Complex.I) •
        ((starRingEnd ℂ) (φ z.1) • Φ z.2) = _
      simp only [smul_smul, mul_comm]
    · simp only [norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Φ]
      exact le_rfl
  have hL : ∀ c : ℝ, (starRingEnd ℂ) (φ c) • coefficientFormulaVec ρ G (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω,
        ((starRingEnd ℂ) (φ c) * Complex.exp ((ω * c : ℝ) * Complex.I)) • Φ ω := by
    intro c
    unfold coefficientFormulaVec
    rw [smul_comm, ← integral_smul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Φ, smul_smul]
    congr 1
    ring
  simp_rw [hL]
  rw [integral_smul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hconj : ∀ c : ℝ, (starRingEnd ℂ) (φ c) * Complex.exp ((ω * c : ℝ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (-Complex.I * ((inner ℝ c ω : ℝ) : ℂ)) * φ c) := by
    intro c
    rw [map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    simp only [RCLike.inner_apply, conj_trivial]
    have he : Complex.exp ((ω * c : ℝ) * Complex.I) =
        Complex.exp (-(-Complex.I) * ((c * ω : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [he, mul_comm]
    congr 2
    congr 1
    push_cast
    ring
  simp_rw [hconj]
  rw [integral_smul_const, integral_conj]
  rfl

variable (hν : IsHomogeneous α ν)
include hν

/-- `W_ρ G` depends only on the `ν`-class of `G`. -/
theorem spectralCoefficientVec_congr_ae (ρ : ℝ → ℝ) {G G' : H → Y} (hGG' : G =ᵐ[ν] G') :
    spectralCoefficientVec ν ρ G = spectralCoefficientVec ν ρ G' := by
  have hae := hν.ae_ae_eq_neg_smul' hGG'
  have hΦ : ∀ᵐ a ∂ν, (fun ω => filterFourier ρ ω • G (-(ω • a))) =ᵐ[volume]
      fun ω => filterFourier ρ ω • G' (-(ω • a)) := by
    filter_upwards [hae] with a ha
    filter_upwards [ha] with ω hω
    simp only [hω]
  have hΦ' : ∀ᵐ a ∂ν, (fun ω => filterFourier ρ ω • G' (-(ω • a))) =ᵐ[volume]
      fun ω => filterFourier ρ ω • G (-(ω • a)) := by
    filter_upwards [hΦ] with a ha
    exact ha.symm
  have key : ∀ γ : Lp Y 2 (parameterMeasure ν),
      HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G (-(ω • a))) ↔
        HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G' (-(ω • a))) :=
    fun γ => ⟨fun h => h.congr_right hΦ, fun h => h.congr_right hΦ'⟩
  unfold spectralCoefficientVec
  by_cases h : ∃ γ : Lp Y 2 (parameterMeasure ν),
      HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G (-(ω • a)))
  · have h' : ∃ γ : Lp Y 2 (parameterMeasure ν),
        HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G' (-(ω • a))) :=
      h.imp fun γ => (key γ).mp
    rw [dif_pos h, dif_pos h']
    exact Exists.choose_congr (funext fun γ => propext (key γ)) h h'
  · have h' : ¬ ∃ γ : Lp Y 2 (parameterMeasure ν),
        HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G' (-(ω • a))) :=
      fun h' => h (h'.imp fun γ => (key γ).mpr)
    rw [dif_neg h, dif_neg h']

variable (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hα hρ

/-- Existence and uniqueness of `W_ρ G` for measurable `G ∈ L²(ν)`. -/
theorem existsUnique_hasBiasFourierVec {G : H → Y} (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    ∃! γ : Lp Y 2 (parameterMeasure ν),
      HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G (-(ω • a))) := by
  have hB := (hasBiasFourierVec_coefficientFormulaVec hα hν hρ hG hG₂).congr_left
    (memLp_coefficientFormulaVec hα hν hρ hG hG₂).coeFn_toLp.symm
  exact ⟨_, hB, fun γ hγ => Lp.ext (HasBiasFourierVec.ae_eq (Lp.memLp γ) (Lp.memLp _) hγ hB)⟩

/-- For measurable `G ∈ L²(ν)`, `W_ρ G` is the class of the explicit coefficient `γ_G`. -/
theorem spectralCoefficientVec_eq_toLp {G : H → Y} (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    spectralCoefficientVec ν ρ G = (memLp_coefficientFormulaVec hα hν hρ hG hG₂).toLp _ := by
  have hB := (hasBiasFourierVec_coefficientFormulaVec hα hν hρ hG hG₂).congr_left
    (memLp_coefficientFormulaVec hα hν hρ hG hG₂).coeFn_toLp.symm
  have hex : ∃ γ : Lp Y 2 (parameterMeasure ν),
      HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G (-(ω • a))) := ⟨_, hB⟩
  unfold spectralCoefficientVec
  rw [dif_pos hex]
  exact Lp.ext (HasBiasFourierVec.ae_eq (Lp.memLp _) (Lp.memLp _) hex.choose_spec hB)

/-- The scaled isometry `‖W_ρ G‖² = C^{(α)}_ρ ‖G‖²` for measurable `G ∈ L²(ν)`. -/
theorem integral_spectralCoefficientVec_norm_sq {G : H → Y} (hG : StronglyMeasurable G)
    (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖(spectralCoefficientVec ν ρ G : H × ℝ → Y) p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν := by
  rw [spectralCoefficientVec_eq_toLp hν hα hρ hG hG₂,
    ← integral_coefficientFormulaVec_norm_sq hα hν hρ hG hG₂]
  apply integral_congr_ae
  filter_upwards [(memLp_coefficientFormulaVec hα hν hρ hG hG₂).coeFn_toLp] with p hp
  rw [hp]

/-- The explicit vector coefficient is additive almost everywhere on the parameter space. -/
theorem coefficientFormulaVec_sub_ae {G₁ G₂ : H → Y} (hG₁ : StronglyMeasurable G₁)
    (hG₁₂ : MemLp G₁ 2 ν) (hG₂ : StronglyMeasurable G₂) (hG₂₂ : MemLp G₂ 2 ν) :
    coefficientFormulaVec ρ (G₁ - G₂) =ᵐ[parameterMeasure ν]
      coefficientFormulaVec ρ G₁ - coefficientFormulaVec ρ G₂ := by
  have hray := (ae_integrable_ray_vec hα hν hρ hG₁ hG₁₂).and
    (ae_integrable_ray_vec hα hν hρ hG₂ hG₂₂)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hray] with p hp
  have hi : ∀ (F : ℝ → Y), Integrable F → Integrable fun ω =>
      Complex.exp ((ω * p.2 : ℝ) * Complex.I) • F ω := by
    intro F hF
    refine hF.norm.mono'
      ((by fun_prop : Continuous fun ω : ℝ =>
        Complex.exp ((ω * p.2 : ℝ) * Complex.I)).aestronglyMeasurable.smul
        hF.aestronglyMeasurable) ?_
    filter_upwards with ω
    simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact le_rfl
  have h₁ := hi _ hp.1
  have h₂ := hi _ hp.2
  simp only [coefficientFormulaVec, Pi.sub_apply]
  simp_rw [mul_comm (filterFourier ρ _) (Complex.exp _), ← smul_smul]
  rw [← smul_sub, ← integral_sub h₁ h₂]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  simp only [smul_sub]

/-- The vector coefficient operator respects subtraction of square-integrable classes. -/
theorem spectralCoefficientVec_coeFn_sub (u v : Lp Y 2 ν) :
    spectralCoefficientVec ν ρ ((u - v : Lp Y 2 ν) : H → Y) =
      spectralCoefficientVec ν ρ u - spectralCoefficientVec ν ρ v := by
  rw [spectralCoefficientVec_congr_ae hν ρ (Lp.coeFn_sub u v),
    spectralCoefficientVec_eq_toLp hν hα hρ ((Lp.stronglyMeasurable u).sub
      (Lp.stronglyMeasurable v)) ((Lp.memLp u).sub (Lp.memLp v)),
    spectralCoefficientVec_eq_toLp hν hα hρ (Lp.stronglyMeasurable u) (Lp.memLp u),
    spectralCoefficientVec_eq_toLp hν hα hρ (Lp.stronglyMeasurable v) (Lp.memLp v),
    ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _
    (coefficientFormulaVec_sub_ae hν hα hρ (Lp.stronglyMeasurable u) (Lp.memLp u)
      (Lp.stronglyMeasurable v) (Lp.memLp v))

/-- The vector coefficient operator is a scaled isometry on square-integrable classes. -/
theorem norm_spectralCoefficientVec_coeFn_sq (u : Lp Y 2 ν) :
    ‖spectralCoefficientVec ν ρ u‖ ^ 2 = admissibilityConst α ρ * ‖u‖ ^ 2 := by
  rw [spectralCoefficientVec_eq_toLp hν hα hρ (Lp.stronglyMeasurable u) (Lp.memLp u),
    MemLp.norm_toLp_two_sq,
    integral_coefficientFormulaVec_norm_sq hα hν hρ (Lp.stronglyMeasurable u) (Lp.memLp u),
    Lp.norm_sq_eq_integral_norm_sq]

/-- The vector coefficient operator is Lipschitz on square-integrable classes. -/
theorem lipschitzWith_spectralCoefficientVec :
    LipschitzWith (Real.sqrt (admissibilityConst α ρ)).toNNReal
      fun u : Lp Y 2 ν => spectralCoefficientVec ν ρ u := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [dist_eq_norm, dist_eq_norm, ← spectralCoefficientVec_coeFn_sub hν hα hρ,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_)
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_spectralCoefficientVec_coeFn_sq hν hα hρ]

/-- The vector-valued ridgelet extension is the coefficient operator on the spectral range. -/
theorem ridgeletExtensionVecCLM_eq_spectralCoefficientVec (μ : Measure H) [IsProbabilityMeasure μ]
    (G : spectralRangeVec Y μ ν) :
    ridgeletExtensionVecCLM hν hρ G = spectralCoefficientVec ν ρ ((G : Lp Y 2 ν) : H → Y) := by
  refine (denseRange_spectralEmbedVecₗ (Y := Y) μ ν).induction_on G ?_ fun f => ?_
  · exact isClosed_eq (ridgeletExtensionVecCLM hν hρ).continuous
      ((lipschitzWith_spectralCoefficientVec (Y := Y) hν hα hρ).continuous.comp
        continuous_subtype_val)
  · have hf : Integrable ((f : Lp Y 2 μ) : H → Y) μ := (Lp.memLp _).integrable one_le_two
    have hcoe : ((spectralEmbedVec μ ν f : Lp Y 2 ν) : H → Y) =ᵐ[ν] gaussFourierVec μ f :=
      MemLp.coeFn_toLp f.2
    rw [spectralEmbedVecₗ_apply, ridgeletExtensionVecCLM_embed,
      spectralCoefficientVec_congr_ae hν ρ hcoe,
      spectralCoefficientVec_eq_toLp hν hα hρ
        (continuous_gaussFourierVec μ hf).stronglyMeasurable f.2,
      ridgeletCoreVecₗ_apply]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
    exact congrFun (ridgeletVec_eq_coefficientFormulaVec' μ ρ
      (fun v => (by fun_prop : Continuous fun x : H => inner ℝ x v).measurable.aemeasurable) hf) p

end Coefficient

end OperatorRidgelet
