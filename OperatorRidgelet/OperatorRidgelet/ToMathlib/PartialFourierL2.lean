import LeanRidgelet.ToMathlib.FourierPlancherel
import OperatorRidgelet.ToMathlib.IndicatorTendstoL2

/-! # Jointly measurable partial Fourier transforms in L² -/

noncomputable section
open MeasureTheory Complex Filter Topology
open scoped FourierTransform ENNReal
namespace MeasureTheory
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]


variable {H : Type*} [MeasurableSpace H]
variable [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- The Fourier integral of the bias slices in Mathlib's convention,
`(a, ω) ↦ 𝓕 (γ(a,·)) ω`, as a function on `H × ℝ`. -/
def partialFourierIntegral (γ : H × ℝ → Y) (p : H × ℝ) : Y :=
  ∫ c : ℝ, Complex.exp (((-2 * Real.pi * c * p.2 : ℝ) : ℂ) * Complex.I) • γ (p.1, c)

omit [MeasurableSpace H] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- `partialFourierIntegral γ (a, ω)` is the Fourier transform of the ray `c ↦ γ(a, c)`. -/
theorem partialFourierIntegral_eq (γ : H × ℝ → Y) (a : H) (ω : ℝ) :
    partialFourierIntegral γ (a, ω) = 𝓕 (fun c => γ (a, c)) ω :=
  (Real.fourier_real_eq_integral_exp_smul _ _).symm

omit [MeasurableSpace H] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- The Fourier integrand of a bias slice is integrable when the slice is. -/
theorem integrable_exp_smul_section {γ : H × ℝ → Y} {a : H} (h : Integrable fun c => γ (a, c))
    (ω : ℝ) :
    Integrable fun c : ℝ => Complex.exp (((-2 * Real.pi * c * ω : ℝ) : ℂ) * Complex.I) • γ (a, c) :=
  by
  refine h.norm.mono'
    ((by fun_prop : Continuous fun c : ℝ =>
      Complex.exp (((-2 * Real.pi * c * ω : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable.smul
      h.aestronglyMeasurable) ?_
  filter_upwards with c
  simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact le_rfl

omit [CompleteSpace Y] in
/-- `partialFourierIntegral` is jointly measurable. -/
theorem measurable_partialFourierIntegral {γ : H × ℝ → Y} (hγ : Measurable γ) :
    Measurable (partialFourierIntegral γ) := by
  have hF : StronglyMeasurable fun q : (H × ℝ) × ℝ =>
      Complex.exp (((-2 * Real.pi * q.2 * q.1.2 : ℝ) : ℂ) * Complex.I) • γ (q.1.1, q.2) := by
    refine Measurable.stronglyMeasurable (Measurable.smul ?_ (hγ.comp
      (measurable_fst.fst.prodMk measurable_snd)))
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((measurable_const.mul measurable_snd).mul measurable_fst.snd)).mul measurable_const)
  exact hF.integral_prod_right'.measurable

omit [MeasurableSpace H] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- `partialFourierIntegral` is additive on coefficients with integrable slices. -/
theorem partialFourierIntegral_sub {γ γ' : H × ℝ → Y} {p : H × ℝ}
    (h : Integrable fun c => γ (p.1, c))
    (h' : Integrable fun c => γ' (p.1, c)) :
    partialFourierIntegral (γ - γ') p =
      partialFourierIntegral γ p - partialFourierIntegral γ' p := by
  unfold partialFourierIntegral
  simp only [Pi.sub_apply, smul_sub]
  exact integral_sub (integrable_exp_smul_section h p.2) (integrable_exp_smul_section h' p.2)

omit [MeasurableSpace H] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Plancherel along a bias line for a coefficient whose slice is in `L¹ ∩ L²`. -/
theorem lintegral_partialFourierIntegral_sq {γ : H × ℝ → Y} {a : H}
    (h₁ : Integrable fun c => γ (a, c))
    (h₂ : MemLp (fun c => γ (a, c)) 2 volume) :
    ∫⁻ ω, ‖partialFourierIntegral γ (a, ω)‖ₑ ^ 2 = ∫⁻ c, ‖γ (a, c)‖ₑ ^ 2 := by
  simp_rw [partialFourierIntegral_eq]
  exact h₁.lintegral_enorm_fourier_sq h₂

variable {ν : Measure H} [SFinite ν]

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- Almost every section of a square-integrable product function is square integrable. -/
private theorem ae_memLp_section {γ : H × ℝ → Y} (h : MemLp γ 2 (ν.prod volume)) :
    ∀ᵐ a ∂ν, MemLp (fun c : ℝ => γ (a, c)) 2 volume := by
  filter_upwards [h.integrable_norm_sq.prod_right_ae, h.aestronglyMeasurable.prodMk_left]
    with a ha hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ha

/-- Plancherel on `H × ℝ` for a coefficient in `L²(ν ⊗ dc)` with `ν`-almost every slice in
`L¹`. -/
theorem lintegral_partialFourierIntegral_prod_sq {γ : H × ℝ → Y} (hγ : Measurable γ)
    (h₁ : ∀ᵐ a ∂ν, Integrable fun c => γ (a, c)) (h₂ : MemLp γ 2 (ν.prod volume)) :
    ∫⁻ p, ‖partialFourierIntegral γ p‖ₑ ^ 2 ∂ν.prod volume = ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂ν.prod volume := by
  rw [lintegral_prod _ ((measurable_partialFourierIntegral hγ).enorm.pow_const 2).aemeasurable,
    lintegral_prod _ (hγ.enorm.pow_const 2).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, ae_memLp_section h₂] with a ha hm
  exact lintegral_partialFourierIntegral_sq ha hm

/-- Every square-integrable function on a product has a jointly measurable partial L²
Fourier transform. -/
theorem exists_measurable_partialFourierL2 {γ : H × ℝ → Y} (hγ : Measurable γ)
    (hγ₂ : MemLp γ 2 (ν.prod volume)) :
    ∃ Φ : H × ℝ → Y, Measurable Φ ∧ MemLp Φ 2 (ν.prod volume) ∧
      ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
        (fun ω => Φ (a, ω)) =ᵐ[volume]
          ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)) := by
  -- truncations in the bias
  set S : ℕ → Set (H × ℝ) := fun n => {p | |p.2| ≤ n} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  have hSmem : ∀ p : H × ℝ, ∀ᶠ n in atTop, p ∈ S n := fun p => by
    filter_upwards [eventually_ge_atTop ⌈|p.2|⌉₊] with n hn
    show |p.2| ≤ (n : ℝ)
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  set γn : ℕ → H × ℝ → Y := fun n => (S n).indicator γ with hγn
  have hγnm : ∀ n, Measurable (γn n) := fun n => hγ.indicator (hSm n)
  have hγn₂ : ∀ n, MemLp (γn n) 2 (ν.prod volume) := fun n => hγ₂.indicator (hSm n)
  have hS' : ∀ n : ℕ, MeasurableSet {c : ℝ | |c| ≤ n} := fun n =>
    measurableSet_le continuous_abs.measurable measurable_const
  have heq : ∀ n (a : H), (fun c => γn n (a, c)) = {c : ℝ | |c| ≤ n}.indicator fun c => γ (a, c) :=
    fun n a => rfl
  have hslice₂ : ∀ n (a : H), MemLp (fun c => γ (a, c)) 2 volume →
      MemLp (fun c => γn n (a, c)) 2 volume := fun n a ha => by
    rw [heq]
    exact ha.indicator (hS' n)
  have hslice₁ : ∀ n (a : H), MemLp (fun c => γ (a, c)) 2 volume →
      Integrable fun c => γn n (a, c) := fun n a ha => by
    rw [heq, integrable_indicator_iff (hS' n)]
    have hfin : volume {c : ℝ | |c| ≤ n} < ⊤ := by
      have : {c : ℝ | |c| ≤ n} = Set.Icc (-(n : ℝ)) n := by
        ext c
        simp [abs_le]
      rw [this]
      exact measure_Icc_lt_top
    haveI : IsFiniteMeasure (volume.restrict {c : ℝ | |c| ≤ n}) :=
      isFiniteMeasure_restrict.mpr hfin.ne
    exact (ha.restrict _).integrable one_le_two
  have hslice_ae : ∀ n, ∀ᵐ a ∂ν, Integrable fun c => γn n (a, c) := fun n => by
    filter_upwards [ae_memLp_section hγ₂] with a ha
    exact hslice₁ n a ha
  -- the transforms of the truncations
  set Φn : ℕ → H × ℝ → Y := fun n => partialFourierIntegral (γn n) with hΦn
  have hΦnm : ∀ n, Measurable (Φn n) := fun n => measurable_partialFourierIntegral (hγnm n)
  have hΦn₂ : ∀ n, MemLp (Φn n) 2 (ν.prod volume) := fun n =>
    memLp_two_of_lintegral_enorm_sq_lt_top (hΦnm n).aestronglyMeasurable (by
      rw [lintegral_partialFourierIntegral_prod_sq (hγnm n) (hslice_ae n) (hγn₂ n)]
      exact (hγn₂ n).lintegral_enorm_sq_lt_top)
  -- the transform is an isometry on the truncations
  have hdist : ∀ n m, dist ((hΦn₂ n).toLp _) ((hΦn₂ m).toLp _) =
      dist ((hγn₂ n).toLp _) ((hγn₂ m).toLp _) := by
    intro n m
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae ((hΦn₂ n).sub (hΦn₂ m)).coeFn_toLp,
      eLpNorm_congr_ae ((hγn₂ n).sub (hγn₂ m)).coeFn_toLp]
    have hsub : Φn n - Φn m =ᵐ[(ν.prod volume)] partialFourierIntegral (γn n - γn m) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((hslice_ae n).and (hslice_ae m))]
        with p hp
      rw [Pi.sub_apply, ← partialFourierIntegral_sub hp.1 hp.2]
    rw [eLpNorm_congr_ae hsub, eLpNorm_two_eq_lintegral_enorm_sq,
      eLpNorm_two_eq_lintegral_enorm_sq,
      lintegral_partialFourierIntegral_prod_sq ((hγnm n).sub (hγnm m))
      (by
        filter_upwards [hslice_ae n, hslice_ae m] with a h1 h2
        exact h1.sub h2) ((hγn₂ n).sub (hγn₂ m))]
  -- the truncations converge to `γ`, hence their transforms converge
  have hγlim : Tendsto (fun n => (hγn₂ n).toLp (γn n)) atTop (𝓝 (hγ₂.toLp γ)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hγn₂ γ hγ₂).mpr
      (tendsto_eLpNorm_indicator_sub hγ₂ hSm hSmem)
  have hcauchy : CauchySeq fun n => (hΦn₂ n).toLp (Φn n) := by
    have h := Metric.cauchySeq_iff.mp hγlim.cauchySeq
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => by
      rw [hdist]
      exact hN m hm n hn⟩
  obtain ⟨Φlim, hΦlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  set Φ : H × ℝ → Y := (Lp.aestronglyMeasurable Φlim).mk _ with hΦdef
  have hΦm : Measurable Φ := (Lp.aestronglyMeasurable Φlim).stronglyMeasurable_mk.measurable
  have hΦeq : ⇑Φlim =ᵐ[(ν.prod volume)] Φ := (Lp.aestronglyMeasurable Φlim).ae_eq_mk
  have hΦ₂ : MemLp Φ 2 (ν.prod volume) := (Lp.memLp Φlim).ae_eq hΦeq
  have hΦlim : Tendsto (fun n => eLpNorm (Φn n - Φ) 2 (ν.prod volume)) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hΦlim).congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hΦn₂ n).coeFn_toLp, hΦeq] with p h1 h2
    simp only [Pi.sub_apply, h1, h2]
  -- a subsequence with summable squared errors
  have hsub : ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      eLpNorm (Φn n - Φ) 2 (ν.prod volume) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    ENNReal.tendsto_atTop_zero.mp hΦlim _
      (ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) k)
  choose N hN using hsub
  set nk : ℕ → ℕ := fun k => max (N k) k with hnk
  have hnk_le : ∀ k, eLpNorm (Φn (nk k) - Φ) 2 (ν.prod volume) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    hN k _ (le_max_left _ _)
  have hnk_tendsto : Tendsto nk atTop atTop :=
    tendsto_atTop_mono (fun k => le_max_right _ _) tendsto_id
  -- the squared errors along rays are summable for almost every ray
  set e : ℕ → H → ℝ≥0∞ := fun k a => ∫⁻ ω, ‖Φn (nk k) (a, ω) - Φ (a, ω)‖ₑ ^ 2 with he
  have hem : ∀ k, Measurable (e k) := fun k =>
    (((hΦnm (nk k)).sub hΦm).enorm.pow_const 2).lintegral_prod_right'
  have hesum : ∫⁻ a, ∑' k, e k a ∂ν < ⊤ := by
    rw [lintegral_tsum fun k => (hem k).aemeasurable]
    calc ∑' k, ∫⁻ a, e k a ∂ν = ∑' k, ∫⁻ p, ‖Φn (nk k) p - Φ p‖ₑ ^ 2 ∂(ν.prod volume) := by
          congr 1
          funext k
          rw [lintegral_prod (fun p => ‖Φn (nk k) p - Φ p‖ₑ ^ 2)
            (((hΦnm (nk k)).sub hΦm).enorm.pow_const 2).aemeasurable]
      _ ≤ ∑' k, ((2⁻¹ : ℝ≥0∞) ^ 2) ^ k := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [← eLpNorm_two_sq_eq_lintegral_enorm_sq', ← pow_mul, mul_comm, pow_mul]
          exact ENNReal.pow_le_pow_left (hnk_le k)
      _ < ⊤ := by
          rw [ENNReal.tsum_geometric]
          refine ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr ?_)
          rw [← ENNReal.inv_pow]
          exact ENNReal.inv_lt_one.mpr (by norm_num)
  have hae : ∀ᵐ a ∂ν, Tendsto (fun k => e k a) atTop (𝓝 0) := by
    filter_upwards [ae_lt_top (Measurable.tsum hem) hesum.ne] with a ha
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne
  -- identification of the rays of the limit with the `L²` Fourier transforms of the rays of `γ`
  have hkey : ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      (fun ω => Φ (a, ω)) =ᵐ[volume] ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)) := by
    filter_upwards [hae, ae_memLp_section hΦ₂, ae_memLp_section hγ₂] with a ha hΦa hua hu
    -- the truncated rays converge in `L²(dc)`
    have hv : Tendsto (fun n => (hslice₂ n a hu).toLp _) atTop (𝓝 (hu.toLp _)) := by
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hslice₂ n a hu) _ hu).mpr ?_
      simp only [heq]
      exact tendsto_eLpNorm_indicator_sub hu hS' fun c => by
        filter_upwards [eventually_ge_atTop ⌈|c|⌉₊] with n hn
        show |c| ≤ (n : ℝ)
        exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    have hΦnv : ∀ n, (fun ω => Φn n (a, ω)) =ᵐ[volume]
        ⇑(𝓕 ((hslice₂ n a hu).toLp _) : Lp Y 2 (volume : Measure ℝ)) := fun n => by
      filter_upwards [(hslice₁ n a hu).fourier_toLp_ae_eq (hslice₂ n a hu)] with ω hω
      rw [hω]
      exact partialFourierIntegral_eq _ a ω
    -- the errors of the two approximations tend to zero
    have h1 : Tendsto (fun k => eLpNorm ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) 2 volume)
        atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp ha
      rw [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num)] at h
      refine h.congr fun k => ?_
      rw [eLpNorm_sub_comm, eLpNorm_two_eq_lintegral_enorm_sq]
      rfl
    have h2 : Tendsto (fun k => eLpNorm ((fun ω => Φn (nk k) (a, ω)) -
        ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ))) 2 volume) atTop (𝓝 0) := by
      have hF : Tendsto (fun k => (𝓕 ((hslice₂ (nk k) a hu).toLp _) : Lp Y 2 (volume : Measure ℝ)))
          atTop (𝓝 (𝓕 (hu.toLp _))) :=
        ((Lp.fourierTransformₗᵢ ℝ Y).continuous.tendsto _).comp (hv.comp hnk_tendsto)
      refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hF).congr fun k =>
        eLpNorm_congr_ae ?_
      filter_upwards [hΦnv (nk k)] with ω hω
      simp only [Pi.sub_apply, hω]
    have hmeas1 : ∀ k, AEStronglyMeasurable
        ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) volume := fun k =>
      hΦa.1.sub ((hΦnm (nk k)).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have h3 : ∀ k, eLpNorm ((fun ω => Φ (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)))
        2 volume ≤
        eLpNorm ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) 2 volume +
          eLpNorm ((fun ω => Φn (nk k) (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)))
            2 volume := by
      intro k
      rw [← sub_add_sub_cancel (fun ω => Φ (a, ω)) (fun ω => Φn (nk k) (a, ω))]
      exact eLpNorm_add_le (hmeas1 k)
        ((((hΦnm (nk k)).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).sub
          (Lp.aestronglyMeasurable _)) one_le_two
    have h5 : eLpNorm ((fun ω => Φ (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)))
        2 volume = 0 :=
      le_antisymm (ge_of_tendsto' (by simpa using h1.add h2) h3) zero_le
    have h6 := (eLpNorm_eq_zero_iff (hΦa.1.sub (Lp.aestronglyMeasurable _)) two_ne_zero).mp h5
    filter_upwards [h6] with ω hω
    exact sub_eq_zero.mp hω
  exact ⟨Φ, hΦm, hΦ₂, hkey⟩

end MeasureTheory
