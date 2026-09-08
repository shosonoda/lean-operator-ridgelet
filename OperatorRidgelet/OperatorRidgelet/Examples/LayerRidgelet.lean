import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.GaussianLaw
import OperatorRidgelet.Examples.GaussianMeasurability
import OperatorRidgelet.ToMathlib.GaussianTilt

/-!
# The ridgelet coefficient of the Gaussian-activation layer

For a Gaussian pair `(⟪v,x⟫, ⟪a,x⟫)` under `𝒩(0,Q)` and a continuous filter `ρ`,
`∫ Φ(⟪v,x⟫) ρ(⟪a,x⟫ + c) 𝒩(0,Q)(dx) = (1+σ²)^{-1/2} (ρ * φ_{⟪S_v a,a⟫})(c)`
(`IsCenteredGaussian.integral_gaussianFun_mul_comp_inner_add'`): the Gaussian tilt turns the
`v`-coordinate into `𝒩(0, σ²/(1+σ²))`, the shear of Gaussian coordinates makes `⟪a,x⟫` a
Gaussian with variance `⟪S_v a, a⟫`, and the convolution with a centred Gaussian is symmetric.
Consequently the ridgelet coefficient of the layer observable is
`R_ρ F_φ(a,c) = ∫ w_φ(y) (1+σ_y²)^{-1/2} (ρ * φ_{⟪S_y a,a⟫})(c) m(dy)`
(`IsLayerData.ridgelet_layerObservable_gaussianFun'`, Example `ex:operator-layer`(ii)).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [CompleteSpace H] {Q : H →L[ℝ] H} {μ : Measure H} [IsProbabilityMeasure μ]

omit [CompleteSpace H] in
/-- The `μ.map (⟪·, a⟫)` law for a nonnegative variance, for a.e.-measurable coordinates. -/
theorem IsCenteredGaussian.map_inner_eq_gaussianReal' (hμ : IsCenteredGaussian Q μ) (a : H)
    (ha : AEMeasurable (fun x => ⟪x, a⟫) μ) (hτ : 0 ≤ ⟪Q a, a⟫) :
    μ.map (fun x => ⟪x, a⟫) = gaussianReal 0 ⟪Q a, a⟫.toNNReal :=
  MeasureTheory.map_inner_eq_gaussianReal' μ a ha hτ (hμ.charFun_smul a)

/-- The Gaussian-smoothed filter `ρ * φ_v` evaluated through the sheared Gaussian pair. -/
theorem IsCenteredGaussian.integral_gaussianFun_mul_comp_inner_add' (hQ : IsSelfAdjoint Q)
    (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (hμ : IsCenteredGaussian Q μ) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {C : ℝ} (hρC : ∀ t, |ρ t| ≤ C) (v a : H) (c : ℝ) :
    ∫ x, gaussianFun ⟪v, x⟫ * ρ (⟪a, x⟫ + c) ∂μ =
      (Real.sqrt (1 + ⟪Q v, v⟫))⁻¹ *
        gaussianSmooth ρ ⟪(Q - (1 + ⟪Q v, v⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q v) (Q v)) a, a⟫
          c := by
  have hv := hμ.aemeasurable_inner v
  have ha := hμ.aemeasurable_inner a
  have hch := fun s t => hμ.charFun_smul_add_smul hQ v a s t
  have hσ : 0 ≤ ⟪Q v, v⟫ := hQ0 v
  have hτ : 0 ≤ ⟪Q a, a⟫ := hQ0 a
  have hS := inner_sub_rankOne_smul_apply Q v a
  have hL : (fun x => gaussianFun ⟪v, x⟫ * ρ (⟪a, x⟫ + c)) =
      fun x => (fun z u => gaussianFun z * ρ (u + c)) ⟪x, v⟫ ⟪x, a⟫ := by
    funext x
    simp only [real_inner_comm x v, real_inner_comm x a]
  have hg : Continuous (Function.uncurry fun z u => gaussianFun z * ρ (u + c)) :=
    (continuous_gaussianFun.comp continuous_fst).mul (hρ.comp (continuous_snd.add continuous_const))
  rcases hσ.lt_or_eq with hσ | hσ0
  · -- nondegenerate case
    have hδ : 0 ≤ ⟪Q a, a⟫ - ⟪Q v, a⟫ ^ 2 / ⟪Q v, v⟫ := by
      have := MeasureTheory.sq_le_mul_of_charFun μ v a hch
      rw [sub_nonneg, div_le_iff₀ hσ]
      linarith
    have hvw : AEMeasurable (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, a⟫)) μ :=
      (WithLp.measurable_toLp 2 _).comp_aemeasurable (hv.prodMk ha)
    rw [hL, MeasureTheory.integral_inner_pair_eq_integral_prod_gaussianReal' μ v a hvw hσ hch _ hg]
    set k : ℝ := ⟪Q v, a⟫ / ⟪Q v, v⟫ with hk
    set δ : ℝ := ⟪Q a, a⟫ - ⟪Q v, a⟫ ^ 2 / ⟪Q v, v⟫ with hδdef
    -- Fubini on the product, then the tilt of the first coordinate
    have hint : Integrable (fun p : ℝ × ℝ => gaussianFun p.1 * ρ (k * p.1 + p.2 + c))
        ((gaussianReal 0 ⟪Q v, v⟫.toNNReal).prod (gaussianReal 0 δ.toNNReal)) := by
      refine Integrable.of_bound ((continuous_gaussianFun.comp continuous_fst).mul
        (hρ.comp (by fun_prop))).aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussianFun_pos _)]
      calc gaussianFun p.1 * |ρ (k * p.1 + p.2 + c)| ≤ 1 * C :=
            mul_le_mul (abs_gaussianFun_le_one p.1 |>.trans' (le_abs_self _)) (hρC _)
              (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    rw [integral_prod _ hint]
    have htilt := integral_exp_neg_sq_half_smul_gaussianReal hσ.le
      (fun z => ∫ u, ρ (k * z + u + c) ∂gaussianReal 0 δ.toNNReal)
    simp only [smul_eq_mul] at htilt
    have hfun : ∀ z, ∫ u, gaussianFun z * ρ (k * z + u + c) ∂gaussianReal 0 δ.toNNReal =
        Real.exp (-z ^ 2 / 2) * ∫ u, ρ (k * z + u + c) ∂gaussianReal 0 δ.toNNReal := by
      intro z
      rw [integral_const_mul]
      rfl
    simp_rw [hfun]
    rw [htilt]
    congr 1
    -- undo Fubini for the sheared variables and identify the law of `k z + u`
    have hint' : Integrable (fun p : ℝ × ℝ => ρ (k * p.1 + p.2 + c))
        ((gaussianReal 0 (⟪Q v, v⟫ / (1 + ⟪Q v, v⟫)).toNNReal).prod (gaussianReal 0 δ.toNNReal)) :=
      Integrable.of_bound (hρ.comp (by fun_prop)).aestronglyMeasurable C
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hρC _)
    rw [← integral_prod _ hint']
    have hmeas : Measurable fun p : ℝ × ℝ => k * p.1 + p.2 := by fun_prop
    have hchange : ∫ p : ℝ × ℝ, ρ (k * p.1 + p.2 + c)
        ∂((gaussianReal 0 (⟪Q v, v⟫ / (1 + ⟪Q v, v⟫)).toNNReal).prod (gaussianReal 0 δ.toNNReal)) =
        ∫ s, ρ (s + c) ∂(((gaussianReal 0 (⟪Q v, v⟫ / (1 + ⟪Q v, v⟫)).toNNReal).prod
          (gaussianReal 0 δ.toNNReal)).map fun p : ℝ × ℝ => k * p.1 + p.2) := by
      have hm : AEStronglyMeasurable (fun s => ρ (s + c))
          ((((gaussianReal 0 (⟪Q v, v⟫ / (1 + ⟪Q v, v⟫)).toNNReal).prod
            (gaussianReal 0 δ.toNNReal)).map fun p : ℝ × ℝ => k * p.1 + p.2)) :=
        (hρ.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      rw [integral_map hmeas.aemeasurable hm]
    rw [hchange, map_mul_add_prod_gaussianReal (by positivity) hδ k]
    have hV : k ^ 2 * (⟪Q v, v⟫ / (1 + ⟪Q v, v⟫)) + δ =
        ⟪(Q - (1 + ⟪Q v, v⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q v) (Q v)) a, a⟫ := by
      rw [hS, hk, hδdef]
      field_simp
      ring
    rw [hV]
    unfold gaussianSmooth
    have h1 : (fun s => ρ (s + c)) = fun s => ρ (c + s) := by
      funext s
      rw [add_comm]
    rw [h1, integral_comp_add_gaussianReal _ hρ c]
  · -- degenerate case: the `v`-coordinate vanishes almost everywhere
    have hr : ⟪Q v, a⟫ = 0 := by
      have := MeasureTheory.sq_le_mul_of_charFun μ v a hch
      rw [← hσ0, zero_mul] at this
      nlinarith [sq_nonneg ⟪Q v, a⟫]
    have hae := MeasureTheory.ae_inner_eq_zero_of_charFun' μ v hv fun s => by
      have := hch s 0
      rw [← hσ0] at this
      simpa using this
    rw [hS, hr, ← hσ0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
      add_zero, Real.sqrt_one, inv_one, one_mul]
    have hlaw := hμ.map_inner_eq_gaussianReal' a ha hτ |>.symm
    rw [integral_congr_ae (g := fun x => ρ (⟪a, x⟫ + c)) ?_]
    · unfold gaussianSmooth
      rw [← integral_comp_add_gaussianReal _ hρ c, hlaw]
      have hm : AEStronglyMeasurable (fun t => ρ (c + t)) (μ.map fun x => ⟪x, a⟫) :=
        (hρ.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      rw [integral_map ha hm]
      congr 1
      funext x
      rw [add_comm, real_inner_comm x a]
    · filter_upwards [hae] with x hx
      rw [real_inner_comm, hx]
      simp [gaussianFun]

/-! ### The ridgelet coefficient of the layer observable -/

section Layer

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
variable {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H}
  {b : Ω → Y}

/-- A Schwartz filter is bounded by its zeroth seminorm. -/
theorem abs_schwartz_le_seminorm (ρ : SchwartzMap ℝ ℝ) (t : ℝ) :
    |ρ t| ≤ SchwartzMap.seminorm ℝ 0 0 ρ := by
  rw [← Real.norm_eq_abs]
  exact SchwartzMap.norm_le_seminorm ℝ ρ t

omit [CompleteSpace H] [CompleteSpace Y] in
/-- The joint integrand of the ridgelet coefficient of the layer is integrable on `μ ⊗ m`. -/
theorem IsLayerData.integrable_gaussianFun_mul_layerWeight_mul_filter (hμ : IsCenteredGaussian Q μ)
    (hL : IsLayerData m a b) (ρ : SchwartzMap ℝ ℝ) (φ : Y) (p : H × ℝ) :
    Integrable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * (ρ (⟪p.1, x⟫ + p.2) : ℂ))
      (μ.prod m) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * (ρ (⟪p.1, x⟫ + p.2) : ℂ))
      (μ.prod m) := by
    have h1 : AEStronglyMeasurable (fun z : H × Ω => ⟪a z.2, z.1⟫) (μ.prod m) :=
      aestronglyMeasurable_inner_prod_of_aemeasurable hμ.aemeasurable_inner
        hL.stronglyMeasurable_a
    have h2 : AEStronglyMeasurable (fun z : H × Ω => ((gaussianFun ⟪a z.2, z.1⟫ : ℝ) : ℂ))
        (μ.prod m) :=
      (Complex.continuous_ofReal.comp continuous_gaussianFun).comp_aestronglyMeasurable h1
    have h3 : AEStronglyMeasurable (fun z : H × Ω => layerWeight b φ z.2) (μ.prod m) :=
      ((hL.stronglyMeasurable_layerWeight φ).comp_measurable measurable_snd).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun z : H × Ω => (ρ (⟪p.1, z.1⟫ + p.2) : ℂ)) (μ.prod m) := by
      have h5 : AEStronglyMeasurable (fun x : H => ⟪x, p.1⟫) μ :=
        (hμ.aemeasurable_inner p.1).aestronglyMeasurable
      have h7 : AEStronglyMeasurable (fun x : H => (ρ (⟪x, p.1⟫ + p.2) : ℂ)) μ :=
        (Complex.continuous_ofReal.comp (ρ.continuous.comp
          (continuous_id.add continuous_const))).comp_aestronglyMeasurable h5
      have h6 : AEStronglyMeasurable (fun x : H => (ρ (⟪p.1, x⟫ + p.2) : ℂ)) μ :=
        h7.congr (Eventually.of_forall fun x => by beta_reduce; rw [real_inner_comm x p.1])
      exact h6.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact (h2.mul h3).mul h4
  refine ((integrable_const (SchwartzMap.seminorm ℝ 0 0 ρ : ℝ)).mul_prod
    (hL.integrable_layerWeight φ).norm).mono' hmeas (Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real]
  calc ‖gaussianFun ⟪a y, x⟫‖ * ‖layerWeight b φ y‖ * ‖ρ (⟪p.1, x⟫ + p.2)‖
      ≤ 1 * ‖layerWeight b φ y‖ * SchwartzMap.seminorm ℝ 0 0 ρ := by
        gcongr
        · exact norm_gaussianFun_le_one _
        · exact SchwartzMap.norm_le_seminorm ℝ ρ _
    _ = _ := by ring

/-- **Example `ex:operator-layer`(ii)**, the ridgelet coefficient of the scalar observable:
`R_ρ F_φ(a,c) = ∫ w_φ(y) (1+σ_y²)^{-1/2} (ρ * φ_{⟪S_y a,a⟫})(c) m(dy)`. -/
theorem IsLayerData.ridgelet_layerObservable_gaussianFun' (hQ : IsSelfAdjoint Q)
    (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hL : IsLayerData m a b) (φ : Y) (p : H × ℝ) :
    ridgelet μ ρ (layerObservable m a b gaussianFun φ) p =
      ∫ y, layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        gaussianSmooth ρ ⟪layerCovariance Q a y p.1, p.1⟫ p.2 : ℝ) : ℂ) ∂m := by
  unfold ridgelet
  simp_rw [hL.layerObservable_gaussianFun_eq φ]
  have h1 : ∀ x, (∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m) *
      (ρ (⟪p.1, x⟫ + p.2) : ℂ) =
      ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * (ρ (⟪p.1, x⟫ + p.2) : ℂ) ∂m :=
    fun x => (integral_mul_const _ _).symm
  simp_rw [h1]
  rw [integral_integral_swap (hL.integrable_gaussianFun_mul_layerWeight_mul_filter hμ ρ φ p)]
  congr 1
  funext y
  have h2 : (fun x => ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y *
      (ρ (⟪p.1, x⟫ + p.2) : ℂ)) =
      fun x => layerWeight b φ y * ((gaussianFun ⟪a y, x⟫ * ρ (⟪p.1, x⟫ + p.2) : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  rw [h2, integral_const_mul, integral_complex_ofReal,
    hμ.integral_gaussianFun_mul_comp_inner_add' hQ hQ0 ρ.continuous (abs_schwartz_le_seminorm ρ)
      (a y) p.1 p.2]
  rfl

end Layer

end OperatorRidgelet
