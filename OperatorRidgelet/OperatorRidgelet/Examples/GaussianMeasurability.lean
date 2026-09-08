import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.GaussianLaw
import OperatorRidgelet.Examples.OperatorLayer

/-!
# Measurability of Gaussian coordinates under an arbitrary σ-algebra

The hypothesis `IsCenteredGaussian Q μ` (the characteristic functional of `μ` is
`ξ ↦ e^{-⟪Qξ,ξ⟫/2}`) is stated for an arbitrary σ-algebra on `H`.  Since the characteristic
functional never vanishes, every character `x ↦ e^{i⟪x,ξ⟫}` is a.e. strongly measurable
(`IsCenteredGaussian.aestronglyMeasurable_exp_inner_mul_I`), and letting `ξ → 0` along a ray
shows that every coordinate `x ↦ ⟪x, v⟫` is a.e.-measurable
(`IsCenteredGaussian.aemeasurable_inner`).  Together with the strong measurability of the
directions `y ↦ a_y`, the pairing `(x, y) ↦ ⟪a_y, x⟫` is a.e. strongly measurable on `μ ⊗ m`
(`aestronglyMeasurable_inner_prod_of_aemeasurable`).  This gives the transform formulas of the
neural-operator layer (`eq:operator-layer-transform`) without any compatibility assumption
between the σ-algebra and the topology of `H`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-! ### Coordinates are a.e.-measurable under a centred Gaussian -/

section Coordinates

variable {Q : H →L[ℝ] H} {μ : Measure H}

/-- Under `𝒩(0,Q)` the characters `x ↦ e^{i⟪x,ξ⟫}` are a.e. strongly measurable: their
integrals are nonzero. -/
theorem IsCenteredGaussian.aestronglyMeasurable_exp_inner_mul_I (hμ : IsCenteredGaussian Q μ)
    (ξ : H) : AEStronglyMeasurable (fun x => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)) μ := by
  by_contra h
  have h1 : ¬ Integrable (fun x => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)) μ := fun hi => h hi.1
  have h2 := hμ.charFun_eq ξ
  rw [charFun_apply, integral_undef h1] at h2
  exact Complex.exp_ne_zero _ h2.symm

/-- Under `𝒩(0,Q)` the characters `x ↦ e^{-i⟪x,ξ⟫}` are a.e. strongly measurable. -/
theorem IsCenteredGaussian.aestronglyMeasurable_character (hμ : IsCenteredGaussian Q μ) (ξ : H) :
    AEStronglyMeasurable (character ξ) μ := by
  have h := hμ.aestronglyMeasurable_exp_inner_mul_I (-ξ)
  refine h.congr (Eventually.of_forall fun x => ?_)
  show Complex.exp ((⟪x, -ξ⟫ : ℝ) * Complex.I) = Complex.exp (-((⟪x, ξ⟫ : ℝ) * Complex.I))
  rw [inner_neg_right]
  push_cast
  ring_nf

/-- The difference quotient of the exponential along a ray: for `|t s| ≤ 1`,
`‖(e^{i t s} - 1) / (i s) - t‖ ≤ t² |s|`. -/
theorem norm_exp_mul_I_sub_one_div_sub_le {t s : ℝ} (hs : s ≠ 0) (hts : |t * s| ≤ 1) :
    ‖(Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) - 1) / ((s : ℂ) * Complex.I) - t‖ ≤
      t ^ 2 * |s| := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have heq : (Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) - 1) / ((s : ℂ) * Complex.I) - t =
      (Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) - 1 - ((t * s : ℝ) : ℂ) * Complex.I) /
        ((s : ℂ) * Complex.I) := by
    field_simp
    push_cast
    ring
  have hz : ‖((t * s : ℝ) : ℂ) * Complex.I‖ = |t * s| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [heq, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.norm_exp_sub_one_sub_id_le (by rw [hz]; exact hts)
  rw [hz] at hb
  rw [div_le_iff₀ (abs_pos.mpr hs)]
  refine hb.trans (le_of_eq ?_)
  rw [abs_mul, mul_pow, sq_abs t]
  ring

/-- Under `𝒩(0,Q)` every coordinate `x ↦ ⟪x, v⟫` is a.e.-measurable. -/
theorem IsCenteredGaussian.aemeasurable_inner (hμ : IsCenteredGaussian Q μ) (v : H) :
    AEMeasurable (fun x => ⟪x, v⟫) μ := by
  set f : ℕ → H → ℂ := fun n x =>
    (Complex.exp ((⟪x, (1 / ((n : ℝ) + 1)) • v⟫ : ℝ) * Complex.I) - 1) *
      (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)⁻¹ with hf
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hμ.aestronglyMeasurable_exp_inner_mul_I _).sub aestronglyMeasurable_const).mul
      aestronglyMeasurable_const
  have hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 ((⟪x, v⟫ : ℝ) : ℂ)) := by
    intro x
    set t : ℝ := ⟪x, v⟫ with ht
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => t ^ 2 * |1 / ((n : ℝ) + 1)|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h1.abs.const_mul (t ^ 2))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop ⌈|t|⌉₊] with n hn
    have hs : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
    have hts : |t * (1 / ((n : ℝ) + 1))| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)), mul_one_div,
        div_le_one (by positivity)]
      have := Nat.le_ceil |t|
      have hn' : (⌈|t|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have := norm_exp_mul_I_sub_one_div_sub_le hs hts
    rw [div_eq_mul_inv] at this
    rw [norm_norm]
    refine le_trans (le_of_eq ?_) this
    simp only [hf, real_inner_smul_right, ht]
    ring_nf
  have hae := aestronglyMeasurable_of_tendsto_ae atTop hfm (Eventually.of_forall hlim)
  have hre : (fun x => ⟪x, v⟫) = fun x => ((fun x => ((⟪x, v⟫ : ℝ) : ℂ)) x).re := by
    funext x
    simp
  rw [hre]
  exact (Complex.continuous_re.comp_aestronglyMeasurable hae).aemeasurable

end Coordinates

/-! ### Joint measurability of the pairing with a strongly measurable family -/

section Joint

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If every coordinate `x ↦ ⟪x, c⟫` is a.e.-measurable under `μ` and `y ↦ a_y` is strongly
measurable, then `(x, y) ↦ ⟪a_y, x⟫` is a.e. strongly measurable on `μ ⊗ m`. -/
theorem aestronglyMeasurable_inner_prod_of_aemeasurable {μ : Measure H} {m : Measure Ω}
    [SFinite m] (hcoord : ∀ c : H, AEMeasurable (fun x => ⟪x, c⟫) μ) {a : Ω → H}
    (ha : StronglyMeasurable a) :
    AEStronglyMeasurable (fun z : H × Ω => ⟪a z.2, z.1⟫) (μ.prod m) := by
  have key : ∀ f : SimpleFunc Ω H,
      AEStronglyMeasurable (fun z : H × Ω => ⟪f z.2, z.1⟫) (μ.prod m) := by
    intro f
    induction f using SimpleFunc.induction with
    | @const c s hs =>
      have hfun : (fun z : H × Ω =>
          ⟪(SimpleFunc.piecewise s hs (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0)) z.2, z.1⟫) =
          fun z => s.indicator (fun _ => (1 : ℝ)) z.2 * ⟪z.1, c⟫ := by
        funext z
        rw [SimpleFunc.piecewise_apply]
        split_ifs with h
        · rw [SimpleFunc.const_apply, Set.indicator_of_mem h, one_mul, real_inner_comm]
        · rw [SimpleFunc.const_apply, Set.indicator_of_notMem h, zero_mul, inner_zero_left]
      rw [hfun]
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((measurable_const.indicator hs).comp measurable_snd).aestronglyMeasurable
      · exact ((hcoord c).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst).aestronglyMeasurable
    | @add f g _ hf hg =>
      have hfun : (fun z : H × Ω => ⟪(f + g) z.2, z.1⟫) =
          fun z => ⟪f z.2, z.1⟫ + ⟪g z.2, z.1⟫ := by
        funext z
        rw [SimpleFunc.coe_add, Pi.add_apply, inner_add_left]
      rw [hfun]
      exact hf.add hg
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => key (ha.approx n))
    (Eventually.of_forall fun z => ?_)
  exact ((continuous_id.inner continuous_const).tendsto (a z.2)).comp (ha.tendsto_approx z.2)

end Joint

/-! ### The transform of the neural-operator layer, without Borel assumptions -/

section Layer

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
variable {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H}
  {b : Ω → Y} [CompleteSpace H] {Q : H →L[ℝ] H} {μ : Measure H} [IsProbabilityMeasure μ]

omit [CompleteSpace Y] [CompleteSpace H] in
/-- The joint integrand of the transform of the layer is integrable on `μ ⊗ m`. -/
theorem IsLayerData.integrable_gaussianFun_mul_layerWeight_mul_character'
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y) (ξ : H) :
    Integrable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) (μ.prod m) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) (μ.prod m) := by
    have h1 : AEStronglyMeasurable (fun z : H × Ω => ⟪a z.2, z.1⟫) (μ.prod m) :=
      aestronglyMeasurable_inner_prod_of_aemeasurable hμ.aemeasurable_inner
        hL.stronglyMeasurable_a
    have h2 : AEStronglyMeasurable (fun z : H × Ω => ((gaussianFun ⟪a z.2, z.1⟫ : ℝ) : ℂ))
        (μ.prod m) :=
      (Complex.continuous_ofReal.comp continuous_gaussianFun).comp_aestronglyMeasurable h1
    have h3 : AEStronglyMeasurable (fun z : H × Ω => layerWeight b φ z.2) (μ.prod m) :=
      ((hL.stronglyMeasurable_layerWeight φ).comp_measurable measurable_snd).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun z : H × Ω => character ξ z.1) (μ.prod m) :=
      (hμ.aestronglyMeasurable_character ξ).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    exact (h2.mul h3).mul h4
  refine ((integrable_const (1 : ℝ)).mul_prod (hL.integrable_layerWeight φ).norm).mono' hmeas
    (Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, norm_character, mul_one,
    one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

omit [CompleteSpace H] [IsProbabilityMeasure μ] in
/-- The observable `F_φ` is a.e. strongly measurable under `𝒩(0,Q)`, for an arbitrary σ-algebra
on `H`. -/
theorem IsLayerData.aestronglyMeasurable_layerObservable_gaussianFun' (hμ : IsCenteredGaussian Q μ)
    (hL : IsLayerData m a b) (φ : Y) :
    AEStronglyMeasurable (layerObservable m a b gaussianFun φ) μ := by
  have hfun : layerObservable m a b gaussianFun φ =
      fun x => ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m :=
    funext (hL.layerObservable_gaussianFun_eq φ)
  rw [hfun]
  have h1 : AEStronglyMeasurable (fun z : H × Ω => ⟪a z.2, z.1⟫) (μ.prod m) :=
    aestronglyMeasurable_inner_prod_of_aemeasurable hμ.aemeasurable_inner hL.stronglyMeasurable_a
  have h2 : AEStronglyMeasurable (fun z : H × Ω => ((gaussianFun ⟪a z.2, z.1⟫ : ℝ) : ℂ) *
      layerWeight b φ z.2) (μ.prod m) :=
    ((Complex.continuous_ofReal.comp continuous_gaussianFun).comp_aestronglyMeasurable h1).mul
      ((hL.stronglyMeasurable_layerWeight φ).comp_measurable measurable_snd).aestronglyMeasurable
  exact h2.integral_prod_right'

omit [CompleteSpace H] in
/-- The observable `F_φ` is integrable under `𝒩(0,Q)`, for an arbitrary σ-algebra on `H`. -/
theorem IsLayerData.integrable_layerObservable_gaussianFun' (hμ : IsCenteredGaussian Q μ)
    (hL : IsLayerData m a b) (φ : Y) :
    Integrable (layerObservable m a b gaussianFun φ) μ :=
  Integrable.of_bound (hL.aestronglyMeasurable_layerObservable_gaussianFun' hμ φ) _
    (Eventually.of_forall (hL.norm_layerObservable_gaussianFun_le φ))

/-- **Example `ex:operator-layer`(ii)**, the transform of the scalar observable, for an
arbitrary σ-algebra on `H`:
`𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} m(dy)`. -/
theorem IsLayerData.gaussFourier_layerObservable_gaussianFun' (hQ : IsSelfAdjoint Q)
    (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y)
    (ξ : H) :
    gaussFourier μ (layerObservable m a b gaussianFun φ) ξ =
      ∫ y, layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) ∂m := by
  unfold gaussFourier
  simp_rw [hL.layerObservable_gaussianFun_eq φ]
  have h1 : ∀ x, (∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m) * character ξ x =
      ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x ∂m :=
    fun x => (integral_mul_const _ _).symm
  simp_rw [h1]
  rw [integral_integral_swap (hL.integrable_gaussianFun_mul_layerWeight_mul_character' hμ φ ξ)]
  congr 1
  funext y
  have h2 : (fun x => ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) =
      fun x => layerWeight b φ y * (((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * character ξ x) := by
    funext x
    ring
  rw [h2, integral_const_mul, hμ.integral_gaussianFun_mul_character' hQ hQ0 (a y) ξ
    (hμ.aemeasurable_inner _) (hμ.aemeasurable_inner _)]
  rfl

omit [CompleteSpace Y] [CompleteSpace H] in
/-- The joint integrand of the `Y`-valued transform of the layer is integrable on `μ ⊗ m`. -/
theorem IsLayerData.integrable_character_mul_gaussianFun_smul' (hμ : IsCenteredGaussian Q μ)
    (hL : IsLayerData m a b) (ξ : H) :
    Integrable (Function.uncurry fun (x : H) (y : Ω) =>
      (character ξ x * ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ)) • b y) (μ.prod m) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : H) (y : Ω) =>
      (character ξ x * ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ)) • b y) (μ.prod m) := by
    have h1 : AEStronglyMeasurable (fun z : H × Ω => ⟪a z.2, z.1⟫) (μ.prod m) :=
      aestronglyMeasurable_inner_prod_of_aemeasurable hμ.aemeasurable_inner
        hL.stronglyMeasurable_a
    have h2 : AEStronglyMeasurable (fun z : H × Ω => ((gaussianFun ⟪a z.2, z.1⟫ : ℝ) : ℂ))
        (μ.prod m) :=
      (Complex.continuous_ofReal.comp continuous_gaussianFun).comp_aestronglyMeasurable h1
    have h3 : AEStronglyMeasurable (fun z : H × Ω => b z.2) (μ.prod m) :=
      (hL.stronglyMeasurable_b.comp_measurable measurable_snd).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun z : H × Ω => character ξ z.1) (μ.prod m) :=
      (hμ.aestronglyMeasurable_character ξ).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    exact (h4.mul h2).smul h3
  refine ((integrable_const (1 : ℝ)).mul_prod hL.integrable_b.norm).mono' hmeas
    (Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  simp only [Function.uncurry_apply_pair, norm_smul, norm_mul, Complex.norm_real, norm_character,
    one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

/-- **Example `ex:operator-layer`(ii)**, the `Y`-valued transform of the layer, for an
arbitrary σ-algebra on `H`: `𝒢_Q ℱ(ξ) = ∫ (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} b_y m(dy)`. -/
theorem IsLayerData.gaussFourierVec_operatorLayer_gaussianFun' (hQ : IsSelfAdjoint Q)
    (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (ξ : H) :
    gaussFourierVec μ (operatorLayer m a b gaussianFun) ξ =
      ∫ y, (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) • b y ∂m := by
  unfold gaussFourierVec operatorLayer
  have h1 : ∀ x, character ξ x • ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) • b y ∂m =
      ∫ y, (character ξ x * ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ)) • b y ∂m := by
    intro x
    rw [← integral_smul]
    congr 1
    funext y
    rw [smul_smul]
  simp_rw [h1]
  rw [integral_integral_swap (hL.integrable_character_mul_gaussianFun_smul' hμ ξ)]
  congr 1
  funext y
  rw [integral_smul_const]
  congr 1
  unfold layerCovariance
  rw [← hμ.integral_gaussianFun_mul_character' hQ hQ0 (a y) ξ (hμ.aemeasurable_inner _)
    (hμ.aemeasurable_inner _)]
  congr 1
  funext x
  ring

end Layer

end OperatorRidgelet
