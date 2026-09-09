import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.Basic
import OperatorRidgelet.Examples.GaussianLaw
import OperatorRidgelet.Examples.NotCylindrical
import OperatorRidgelet.Tempered.Basic

/-!
# The neural-operator layer: transforms, hinge form, and non-cylindricity

Auxiliary results for Example `ex:operator-layer` of the manuscript.

* `IsLayerData.norm_le_layerSupNorm`: `‖a_y‖ ≤ ‖A‖_∞`.
* `inner_layerCovariance`: `⟪S_y ξ, ξ⟫ = ⟪Qξ,ξ⟫ - ⟪Qa_y,ξ⟫²/(1+σ_y²)`.
* `IsLayerData.layerObservable_gaussianFun_eq`: `F_φ(x) = ∫ Φ(⟪a_y,x⟫) w_φ(y) m(dy)`.
* `IsLayerData.gaussFourier_layerObservable_gaussianFun`: the transform
  `𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} m(dy)` (`eq:operator-layer-transform`).
* `IsLayerData.gaussFourierVec_operatorLayer_gaussianFun`: the `Y`-valued transform.
* `IsLayerData.operatorLayer_gaussianFun_eq_integral_prod`: the ReLU form
  `ℱ(x) = ∫∫ b_y φ''(b) ReLU(⟪a_y,x⟫ - b) m(dy) db`.
* `IsLayerData.not_isCylindrical_layerObservable_gaussianFun`: non-cylindricity when `A` has
  infinite rank and `w_φ > 0` almost everywhere.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory LeanRidgelet Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Boundedness of the directions -/

section Bounded

variable {m : Measure Ω} {a : Ω → H} {b : Ω → Y}

omit [InnerProductSpace ℝ H] [MeasurableSpace Ω] in
/-- `‖A‖_∞ ≥ 0`. -/
theorem layerSupNorm_nonneg (a : Ω → H) : 0 ≤ layerSupNorm a :=
  Real.sSup_nonneg (by rintro _ ⟨y, rfl⟩; exact norm_nonneg _)

omit [InnerProductSpace ℝ H] [InnerProductSpace ℂ Y] [CompleteSpace Y] in
/-- The norms of the directions are bounded above. -/
theorem IsLayerData.bddAbove_range_norm (hL : IsLayerData m a b) :
    BddAbove (Set.range fun y => ‖a y‖) := by
  obtain ⟨C, hC⟩ := hL.bounded_a
  exact ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩

omit [InnerProductSpace ℝ H] [InnerProductSpace ℂ Y] [CompleteSpace Y] in
/-- `‖a_y‖ ≤ ‖A‖_∞`. -/
theorem IsLayerData.norm_le_layerSupNorm (hL : IsLayerData m a b) (y : Ω) :
    ‖a y‖ ≤ layerSupNorm a :=
  le_ciSup hL.bddAbove_range_norm y

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] in
/-- `y ↦ ⟪a_y, x⟫` is strongly measurable. -/
theorem IsLayerData.stronglyMeasurable_inner (hL : IsLayerData m a b) (x : H) :
    StronglyMeasurable fun y => ⟪a y, x⟫ :=
  hL.stronglyMeasurable_a.inner stronglyMeasurable_const

end Bounded

/-! ### The covariance `S_y` -/

section Covariance

omit [CompleteSpace Y] [MeasurableSpace Ω] in
/-- `⟪S_y ξ, ξ⟫ = ⟪Qξ,ξ⟫ - ⟪Qa_y,ξ⟫²/(1+σ_y²)`. -/
theorem inner_layerCovariance (Q : H →L[ℝ] H) (a : Ω → H) (y : Ω) (ξ : H) :
    ⟪layerCovariance Q a y ξ, ξ⟫ = ⟪Q ξ, ξ⟫ - ⟪Q (a y), ξ⟫ ^ 2 / (1 + ⟪Q (a y), a y⟫) :=
  inner_sub_rankOne_smul_apply Q (a y) ξ

variable [CompleteSpace H]

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] in
/-- The lower bound `S_y ≥ (1 + ‖Q‖ ‖A‖_∞²)⁻¹ Q` (Example `ex:operator-layer`(ii)). -/
theorem IsLayerData.inner_layerCovariance_ge {Q : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q)
    {m : Measure Ω} {a : Ω → H} {b : Ω → Y} (hL : IsLayerData m a b) (y : Ω) (ξ : H) :
    (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ ≤ ⟪layerCovariance Q a y ξ, ξ⟫ := by
  rw [inner_layerCovariance]
  have hτ : 0 ≤ ⟪Q ξ, ξ⟫ := hQ.inner_nonneg ξ
  have hσ : 0 ≤ ⟪Q (a y), a y⟫ := hQ.inner_nonneg (a y)
  have hcs := ContinuousLinearMap.inner_map_mul_le hQ.isSelfAdjoint.isSymmetric hQ.inner_nonneg
    (a y) ξ
  have hA := hL.norm_le_layerSupNorm y
  have hσle : ⟪Q (a y), a y⟫ ≤ ‖Q‖ * layerSupNorm a ^ 2 := by
    calc ⟪Q (a y), a y⟫ ≤ ‖Q (a y)‖ * ‖a y‖ := real_inner_le_norm _ _
      _ ≤ ‖Q‖ * ‖a y‖ * ‖a y‖ := by gcongr; exact Q.le_opNorm _
      _ = ‖Q‖ * ‖a y‖ ^ 2 := by ring
      _ ≤ ‖Q‖ * layerSupNorm a ^ 2 := by gcongr
  have h1σ : 0 < 1 + ⟪Q (a y), a y⟫ := by linarith
  calc (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫
      ≤ (1 + ⟪Q (a y), a y⟫)⁻¹ * ⟪Q ξ, ξ⟫ := by gcongr
    _ = ⟪Q ξ, ξ⟫ - ⟪Q (a y), a y⟫ * ⟪Q ξ, ξ⟫ / (1 + ⟪Q (a y), a y⟫) := by
        field_simp
        ring
    _ ≤ ⟪Q ξ, ξ⟫ - ⟪Q (a y), ξ⟫ ^ 2 / (1 + ⟪Q (a y), a y⟫) := by gcongr

end Covariance

/-! ### The scalar observable with Gaussian activation -/

section Observable

variable {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H} {b : Ω → Y}

/-- The Gaussian activation is bounded by one. -/
theorem norm_gaussianFun_le_one (u : ℝ) : ‖gaussianFun u‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact abs_gaussianFun_le_one u

omit [InnerProductSpace ℝ H] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The layer integrand `y ↦ c(y) • b_y` is integrable for bounded measurable `c`. -/
theorem IsLayerData.integrable_smul (hL : IsLayerData m a b) {c : Ω → ℂ}
    (hc : AEStronglyMeasurable c m) {C : ℝ} (hC : ∀ y, ‖c y‖ ≤ C) :
    Integrable (fun y => c y • b y) m :=
  hL.integrable_b.bdd_smul C hc (Eventually.of_forall hC)

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- A continuous activation is bounded along the pairings `y ↦ ⟪a_y, x⟫` of bounded
directions. -/
theorem IsLayerData.exists_bound_comp_inner (hL : IsLayerData m a b) {β : ℝ → ℝ}
    (hβ : Continuous β) (x : H) : ∃ C : ℝ, ∀ y, |β ⟪a y, x⟫| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(layerSupNorm a * ‖x‖)) (layerSupNorm a * ‖x‖)) hβ.continuousOn
  refine ⟨C, fun y => ?_⟩
  have h : |⟪a y, x⟫| ≤ layerSupNorm a * ‖x‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hL.norm_le_layerSupNorm y) (norm_nonneg _))
  simpa [Real.norm_eq_abs] using hC _ (abs_le.mp h)

omit [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The layer integrand `y ↦ β(⟪a_y, x⟫) b_y` is integrable for a continuous activation `β`. -/
theorem IsLayerData.integrable_ofReal_comp_inner_smul (hL : IsLayerData m a b) {β : ℝ → ℝ}
    (hβ : Continuous β) (x : H) :
    Integrable (fun y => ((β ⟪a y, x⟫ : ℝ) : ℂ) • b y) m := by
  obtain ⟨C, hC⟩ := hL.exists_bound_comp_inner hβ x
  refine hL.integrable_smul (Complex.continuous_ofReal.comp_stronglyMeasurable
    (hβ.comp_stronglyMeasurable (hL.stronglyMeasurable_inner x))).aestronglyMeasurable
    (C := C) fun y => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hC y

omit [IsFiniteMeasure m] in
/-- `F_φ(x) = ∫ β(⟪a_y, x⟫) ⟪φ, b_y⟫ m(dy)` for a continuous activation `β`. -/
theorem IsLayerData.layerObservable_eq_integral_inner (hL : IsLayerData m a b) {β : ℝ → ℝ}
    (hβ : Continuous β) (φ : Y) (x : H) :
    layerObservable m a b β φ x = ∫ y, ((β ⟪a y, x⟫ : ℝ) : ℂ) * inner ℂ φ (b y) ∂m := by
  unfold layerObservable operatorLayer
  rw [← integral_inner (hL.integrable_ofReal_comp_inner_smul hβ x) φ]
  congr 1
  funext y
  rw [inner_smul_right]

omit [IsFiniteMeasure m] [InnerProductSpace ℂ Y] [CompleteSpace Y] in
/-- `y ↦ Φ(⟪a_y, x⟫)` is strongly measurable. -/
theorem IsLayerData.stronglyMeasurable_gaussianFun_inner (hL : IsLayerData m a b) (x : H) :
    StronglyMeasurable fun y => ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) :=
  (Complex.continuous_ofReal.comp continuous_gaussianFun).comp_stronglyMeasurable
    (hL.stronglyMeasurable_inner x)

omit [InnerProductSpace ℝ H] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The weight `w_φ` is integrable. -/
theorem IsLayerData.integrable_layerWeight (hL : IsLayerData m a b) (φ : Y) :
    Integrable (layerWeight b φ) m :=
  ((innerSL ℂ φ).restrictScalars ℝ).integrable_comp hL.integrable_b

omit [InnerProductSpace ℝ H] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The weight `w_φ` is strongly measurable. -/
theorem IsLayerData.stronglyMeasurable_layerWeight (hL : IsLayerData m a b) (φ : Y) :
    StronglyMeasurable (layerWeight b φ) :=
  (innerSL ℂ φ).continuous.comp_stronglyMeasurable hL.stronglyMeasurable_b

omit [IsFiniteMeasure m] in
/-- `F_φ(x) = ∫ Φ(⟪a_y, x⟫) w_φ(y) m(dy)`. -/
theorem IsLayerData.layerObservable_gaussianFun_eq (hL : IsLayerData m a b) (φ : Y) (x : H) :
    layerObservable m a b gaussianFun φ x =
      ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m := by
  unfold layerObservable operatorLayer layerWeight
  rw [← integral_inner (hL.integrable_smul
    (hL.stronglyMeasurable_gaussianFun_inner x).aestronglyMeasurable (C := 1) fun y => by
      rw [Complex.norm_real]; exact norm_gaussianFun_le_one _) φ]
  congr 1
  funext y
  rw [inner_smul_right]

omit [IsFiniteMeasure m] in
/-- `|F_φ(x)| ≤ ∫ |w_φ| dm`. -/
theorem IsLayerData.norm_layerObservable_gaussianFun_le (hL : IsLayerData m a b) (φ : Y)
    (x : H) : ‖layerObservable m a b gaussianFun φ x‖ ≤ ∫ y, ‖layerWeight b φ y‖ ∂m := by
  rw [hL.layerObservable_gaussianFun_eq]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun y => norm_nonneg _) (hL.integrable_layerWeight φ).norm
    (Eventually.of_forall fun y => ?_))
  beta_reduce
  rw [norm_mul, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

omit [IsFiniteMeasure m] in
/-- `F_φ` is continuous. -/
theorem IsLayerData.continuous_layerObservable_gaussianFun (hL : IsLayerData m a b) (φ : Y) :
    Continuous (layerObservable m a b gaussianFun φ) := by
  have : layerObservable m a b gaussianFun φ =
      fun x => ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m :=
    funext (hL.layerObservable_gaussianFun_eq φ)
  rw [this]
  refine continuous_of_dominated (bound := fun y => ‖layerWeight b φ y‖) (fun x =>
    ((hL.stronglyMeasurable_gaussianFun_inner x).mul (hL.stronglyMeasurable_layerWeight φ))
      |>.aestronglyMeasurable) (fun x => Eventually.of_forall fun y => ?_)
    (hL.integrable_layerWeight φ).norm (Eventually.of_forall fun y =>
      (Complex.continuous_ofReal.comp (continuous_gaussianFun.comp
        (continuous_const.inner continuous_id))).mul continuous_const)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

omit [CompleteSpace Y] [IsFiniteMeasure m] in
/-- `‖ℱ(x)‖ ≤ ∫ ‖b_y‖ m(dy)` for the Gaussian activation. -/
theorem IsLayerData.norm_operatorLayer_gaussianFun_le (hL : IsLayerData m a b) (x : H) :
    ‖operatorLayer m a b gaussianFun x‖ ≤ ∫ y, ‖b y‖ ∂m := by
  unfold operatorLayer
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun y => norm_nonneg _) hL.integrable_b.norm
    (Eventually.of_forall fun y => ?_))
  beta_reduce
  rw [norm_smul, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

omit [IsFiniteMeasure m] [CompleteSpace Y] in
/-- `ℱ` is continuous for the Gaussian activation. -/
theorem IsLayerData.continuous_operatorLayer_gaussianFun (hL : IsLayerData m a b) :
    Continuous (operatorLayer m a b gaussianFun) := by
  unfold operatorLayer
  refine continuous_of_dominated (bound := fun y => ‖b y‖) (fun x =>
    ((hL.stronglyMeasurable_gaussianFun_inner x).smul hL.stronglyMeasurable_b)
      |>.aestronglyMeasurable) (fun x => Eventually.of_forall fun y => ?_)
    hL.integrable_b.norm (Eventually.of_forall fun y =>
      (Complex.continuous_ofReal.comp (continuous_gaussianFun.comp
        (continuous_const.inner continuous_id))).smul continuous_const)
  rw [norm_smul, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

variable [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
  [CompleteSpace H]

omit [CompleteSpace H] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The joint integrand of the transform of the layer is integrable on `μ ⊗ m`. -/
theorem IsLayerData.integrable_gaussianFun_mul_layerWeight_mul_character (hL : IsLayerData m a b)
    (φ : Y) (μ : Measure H) [IsProbabilityMeasure μ] (ξ : H) :
    Integrable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) (μ.prod m) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : H) (y : Ω) =>
      ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) (μ.prod m) := by
    have h1 : StronglyMeasurable fun z : H × Ω => ⟪a z.2, z.1⟫ :=
      (hL.stronglyMeasurable_a.comp_measurable measurable_snd).inner
        measurable_fst.stronglyMeasurable
    refine (((Complex.continuous_ofReal.comp continuous_gaussianFun).comp_stronglyMeasurable
      h1).mul ((hL.stronglyMeasurable_layerWeight φ).comp_measurable measurable_snd)).mul
      ((continuous_character ξ).comp_stronglyMeasurable measurable_fst.stronglyMeasurable)
      |>.aestronglyMeasurable
  refine ((integrable_const (1 : ℝ)).mul_prod (hL.integrable_layerWeight φ).norm).mono' hmeas
    (Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, norm_character, mul_one,
    one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

/-- **Example `ex:operator-layer`(ii)**, the transform of the scalar observable:
`𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} m(dy)`. -/
theorem IsLayerData.gaussFourier_layerObservable_gaussianFun {Q : H →L[ℝ] H}
    (hQ : IsSelfAdjoint Q) (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y) (ξ : H) :
    gaussFourier μ (layerObservable m a b gaussianFun φ) ξ =
      ∫ y, layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) ∂m := by
  unfold gaussFourier
  simp_rw [hL.layerObservable_gaussianFun_eq φ]
  have h1 : ∀ x, (∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y ∂m) * character ξ x =
      ∫ y, ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x ∂m :=
    fun x => (integral_mul_const _ _).symm
  simp_rw [h1]
  rw [integral_integral_swap (hL.integrable_gaussianFun_mul_layerWeight_mul_character φ μ ξ)]
  congr 1
  funext y
  have h2 : (fun x => ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * layerWeight b φ y * character ξ x) =
      fun x => layerWeight b φ y * (((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ) * character ξ x) := by
    funext x
    ring
  rw [h2, integral_const_mul, hμ.integral_gaussianFun_mul_character hQ hQ0 (a y) ξ]
  rfl

/-- The Gaussian decay of the transform of the scalar observable:
`|𝒢_Q F_φ(ξ)| ≤ (∫ |w_φ| dm) e^{-θ ⟪Qξ,ξ⟫/2}` with `θ = (1 + ‖Q‖ ‖A‖_∞²)⁻¹`. -/
theorem IsLayerData.norm_gaussFourier_layerObservable_gaussianFun_le {Q : H →L[ℝ] H}
    (hQ : IsPositiveTraceClass Q) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y) (ξ : H) :
    ‖gaussFourier μ (layerObservable m a b gaussianFun φ) ξ‖ ≤
      (∫ y, ‖layerWeight b φ y‖ ∂m) *
        Real.exp (-(1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ / 2) := by
  rw [hL.gaussFourier_layerObservable_gaussianFun hQ.isSelfAdjoint hQ.inner_nonneg hμ φ ξ,
    ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun y => norm_nonneg _)
    ((hL.integrable_layerWeight φ).norm.mul_const _) (Eventually.of_forall fun y => ?_))
  beta_reduce
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hσ : 0 ≤ ⟪Q (a y), a y⟫ := hQ.inner_nonneg (a y)
  have hbound := hL.inner_layerCovariance_ge hQ y ξ
  calc (Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ * Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2)
      ≤ 1 * Real.exp (-(1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ / 2) := by
        gcongr
        · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by linarith))
        · linarith
    _ = _ := one_mul _

omit [CompleteSpace Y] [IsFiniteMeasure m] [CompleteSpace H] in
/-- The joint integrand of the `Y`-valued transform of the layer is integrable on `μ ⊗ m`. -/
theorem IsLayerData.integrable_character_mul_gaussianFun_smul (hL : IsLayerData m a b)
    (μ : Measure H) [IsProbabilityMeasure μ] (ξ : H) :
    Integrable (Function.uncurry fun (x : H) (y : Ω) =>
      (character ξ x * ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ)) • b y) (μ.prod m) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : H) (y : Ω) =>
      (character ξ x * ((gaussianFun ⟪a y, x⟫ : ℝ) : ℂ)) • b y) (μ.prod m) := by
    have h1 : StronglyMeasurable fun z : H × Ω => ⟪a z.2, z.1⟫ :=
      (hL.stronglyMeasurable_a.comp_measurable measurable_snd).inner
        measurable_fst.stronglyMeasurable
    refine (((continuous_character ξ).comp_stronglyMeasurable measurable_fst.stronglyMeasurable).mul
      ((Complex.continuous_ofReal.comp continuous_gaussianFun).comp_stronglyMeasurable h1)).smul
      (hL.stronglyMeasurable_b.comp_measurable measurable_snd) |>.aestronglyMeasurable
  refine ((integrable_const (1 : ℝ)).mul_prod hL.integrable_b.norm).mono' hmeas
    (Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  simp only [Function.uncurry_apply_pair, norm_smul, norm_mul, Complex.norm_real, norm_character,
    one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)

/-- **Example `ex:operator-layer`(ii)**, the `Y`-valued transform of the layer:
`𝒢_Q ℱ(ξ) = ∫ (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} b_y m(dy)`. -/
theorem IsLayerData.gaussFourierVec_operatorLayer_gaussianFun {Q : H →L[ℝ] H}
    (hQ : IsSelfAdjoint Q) (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (ξ : H) :
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
  rw [integral_integral_swap (hL.integrable_character_mul_gaussianFun_smul μ ξ)]
  congr 1
  funext y
  rw [integral_smul_const]
  congr 1
  unfold layerCovariance
  rw [← hμ.integral_gaussianFun_mul_character hQ hQ0 (a y) ξ]
  congr 1
  funext x
  ring

/-- The Gaussian decay of the `Y`-valued transform of the layer. -/
theorem IsLayerData.norm_gaussFourierVec_operatorLayer_gaussianFun_le {Q : H →L[ℝ] H}
    (hQ : IsPositiveTraceClass Q) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (ξ : H) :
    ‖gaussFourierVec μ (operatorLayer m a b gaussianFun) ξ‖ ≤
      (∫ y, ‖b y‖ ∂m) * Real.exp (-(1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ / 2) := by
  rw [hL.gaussFourierVec_operatorLayer_gaussianFun hQ.isSelfAdjoint hQ.inner_nonneg hμ ξ,
    ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun y => norm_nonneg _) (hL.integrable_b.norm.mul_const _)
    (Eventually.of_forall fun y => ?_))
  beta_reduce
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hσ : 0 ≤ ⟪Q (a y), a y⟫ := hQ.inner_nonneg (a y)
  have hbound := hL.inner_layerCovariance_ge hQ y ξ
  calc (Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ * Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2)
      ≤ 1 * Real.exp (-(1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ / 2) := by
        gcongr
        · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by linarith))
        · linarith
    _ = _ := one_mul _

omit [CompleteSpace H] [IsFiniteMeasure m] [CompleteSpace Y] in
/-- The `Y`-valued transform of the layer is continuous. -/
theorem IsLayerData.continuous_gaussFourierVec_operatorLayer_gaussianFun (hL : IsLayerData m a b)
    (μ : Measure H) [IsProbabilityMeasure μ] :
    Continuous (gaussFourierVec μ (operatorLayer m a b gaussianFun)) := by
  unfold gaussFourierVec
  refine continuous_of_dominated (bound := fun _ => ∫ y, ‖b y‖ ∂m) (fun ξ =>
    ((continuous_character ξ).smul hL.continuous_operatorLayer_gaussianFun).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun x => ?_) (integrable_const _)
    (Eventually.of_forall fun x => ?_)
  · rw [norm_smul, norm_character, one_mul]
    exact hL.norm_operatorLayer_gaussianFun_le x
  · exact (by unfold character; fun_prop : Continuous fun ξ : H => character ξ x).smul
      continuous_const

end Observable

/-! ### Symmetries of the layer -/

section Symmetry

variable {m : Measure Ω}

/-- A bounded operator commutes with the layer: `T ℱ(x) = ∫ β(⟪a_y, x⟫) T b_y m(dy)`. -/
theorem IsLayerData.map_operatorLayer {a : Ω → H} {b : Ω → Y} (hL : IsLayerData m a b)
    {β : ℝ → ℝ} (hβ : Continuous β) {Y' : Type*} [NormedAddCommGroup Y']
    [InnerProductSpace ℂ Y'] [CompleteSpace Y'] (T : Y →L[ℂ] Y') (x : H) :
    T (operatorLayer m a b β x) = operatorLayer m a (fun y => T (b y)) β x := by
  unfold operatorLayer
  rw [← T.integral_comp_comm (hL.integrable_ofReal_comp_inner_smul hβ x)]
  simp_rw [map_smul]

omit [CompleteSpace Y] in
/-- The layer depends on the directions only through the pairings `⟪a_y, x⟫`. -/
theorem operatorLayer_congr_inner {a a' : Ω → H} {x x' : H} (h : ∀ y, ⟪a y, x⟫ = ⟪a' y, x'⟫)
    (b : Ω → Y) (β : ℝ → ℝ) : operatorLayer m a b β x = operatorLayer m a' b β x' := by
  unfold operatorLayer
  simp_rw [h]

omit [CompleteSpace Y] in
/-- Reparametrizing the layer by a measure-preserving equivalence of the parameter space. -/
theorem operatorLayer_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {m' : Measure Ω'}
    {e : Ω' ≃ᵐ Ω} (he : MeasurePreserving e m' m) (a : Ω → H) (b : Ω → Y) (β : ℝ → ℝ)
    (x : H) :
    operatorLayer m a b β x = operatorLayer m' (fun y => a (e y)) (fun y => b (e y)) β x := by
  unfold operatorLayer
  exact (he.integral_comp' _).symm

end Symmetry

/-! ### The ReLU form of the Gaussian-activation layer -/

section Hinge

variable {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H} {b : Ω → Y}

/-- The pointwise bound `|φ''(t) ReLU(u - t)| ≤ (|u| + |t|) (t² + 1) e^{-t²/2}`. -/
theorem norm_gaussianActDeriv2_mul_relu_sub_le (u t : ℝ) :
    ‖gaussianActDeriv2 t * relu (u - t)‖ ≤
      (|u| + |t|) * ((t ^ 2 + 1) * Real.exp (-t ^ 2 / 2)) := by
  rw [mul_comm]
  refine (norm_relu_sub_mul_gaussianActDeriv2_le u t).trans (le_of_eq ?_)
  ring

/-- `t ↦ (c + |t|) (t² + 1) e^{-t²/2}` is integrable. -/
theorem integrable_const_add_abs_mul_sq_add_one_mul_exp (c : ℝ) :
    Integrable fun t : ℝ => (c + |t|) * ((t ^ 2 + 1) * Real.exp (-t ^ 2 / 2)) := by
  refine ((integrable_sq_add_one_mul_exp.const_mul c).add
    integrable_abs_mul_sq_add_one_mul_exp).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

omit [IsFiniteMeasure m] [CompleteSpace Y] in
/-- The hinge integrand `(y, t) ↦ (φ''(t) ReLU(⟪a_y,x⟫ - t)) • b_y` is integrable on `m ⊗ dt`. -/
theorem IsLayerData.integrable_hinge_smul (hL : IsLayerData m a b) (x : H) :
    Integrable (fun p : Ω × ℝ =>
      ((gaussianActDeriv2 p.2 * relu (⟪a p.1, x⟫ - p.2) : ℝ) : ℂ) • b p.1) (m.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : Ω × ℝ =>
      ((gaussianActDeriv2 p.2 * relu (⟪a p.1, x⟫ - p.2) : ℝ) : ℂ) • b p.1) (m.prod volume) := by
    have h1 : StronglyMeasurable fun p : Ω × ℝ => ⟪a p.1, x⟫ :=
      (hL.stronglyMeasurable_inner x).comp_measurable measurable_fst
    refine (Complex.continuous_ofReal.comp_stronglyMeasurable
      ((continuous_gaussianActDeriv2.comp_stronglyMeasurable measurable_snd.stronglyMeasurable).mul
        (continuous_relu.comp_stronglyMeasurable
          (h1.sub measurable_snd.stronglyMeasurable)))).smul
      (hL.stronglyMeasurable_b.comp_measurable measurable_fst) |>.aestronglyMeasurable
  refine (hL.integrable_b.norm.mul_prod
    (integrable_const_add_abs_mul_sq_add_one_mul_exp (layerSupNorm a * ‖x‖))).mono' hmeas
    (Eventually.of_forall fun p => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  refine mul_le_mul_of_nonneg_left ((norm_gaussianActDeriv2_mul_relu_sub_le _ _).trans ?_)
    (norm_nonneg _)
  refine mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (by positivity)
  calc |⟪a p.1, x⟫| ≤ ‖a p.1‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ layerSupNorm a * ‖x‖ := by gcongr; exact hL.norm_le_layerSupNorm p.1

/-- **Example `ex:operator-layer`(iii)**, the ReLU form of the Gaussian-activation layer:
`ℱ(x) = ∫∫ b_y φ''(t) ReLU(⟪a_y,x⟫ - t) m(dy) dt`. -/
theorem IsLayerData.operatorLayer_gaussianFun_eq_integral_prod (hL : IsLayerData m a b)
    (x : H) :
    operatorLayer m a b gaussianFun x =
      ∫ p : Ω × ℝ, ((gaussianActDeriv2 p.2 * relu (⟪a p.1, x⟫ - p.2) : ℝ) : ℂ) • b p.1
        ∂(m.prod volume) := by
  rw [integral_prod _ (hL.integrable_hinge_smul x)]
  unfold operatorLayer
  congr 1
  funext y
  have h1 : ∀ t : ℝ, ((gaussianActDeriv2 t * relu (⟪a y, x⟫ - t) : ℝ) : ℂ) • b y =
      (relu (⟪a y, x⟫ - t) * gaussianActDeriv2 t) • b y := by
    intro t
    rw [mul_comm, Complex.coe_smul]
  simp_rw [h1]
  rw [integral_smul_const, integral_relu_sub_mul_gaussianActDeriv2, Complex.coe_smul]

end Hinge

/-! ### Non-cylindricity of the Gaussian-activation observable -/

section NotCylindrical

variable {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H} {b : Ω → Y}

omit [CompleteSpace Y] [InnerProductSpace ℂ Y] [IsFiniteMeasure m] in
/-- `A x = 0` in `L²(m)` if and only if `⟪a_y, x⟫ = 0` for `m`-almost every `y`. -/
theorem IsLayerData.layerA_eq_zero_iff (hL : IsLayerData m a b) (x : H) :
    layerA m a x = 0 ↔ ∀ᵐ y ∂m, ⟪a y, x⟫ = 0 := by
  have ha : AEStronglyMeasurable a m := hL.stronglyMeasurable_a.aestronglyMeasurable
  simp only [layerA, LinearMap.coe_mk, AddHom.coe_mk, dif_pos ha]
  constructor
  · intro h0
    have := AEEqFun.coeFn_mk (fun y => ⟪a y, x⟫) (ha.inner aestronglyMeasurable_const)
    rw [h0] at this
    filter_upwards [this, AEEqFun.coeFn_zero (β := ℝ) (μ := m)] with y hy hy0
    rw [← hy, hy0, Pi.zero_apply]
  · intro h0
    refine AEEqFun.ext ?_
    filter_upwards [AEEqFun.coeFn_mk (fun y => ⟪a y, x⟫) (ha.inner aestronglyMeasurable_const),
      AEEqFun.coeFn_zero (β := ℝ) (μ := m), h0] with y hy hy0 hxy
    rw [hy, hy0, hxy, Pi.zero_apply]

/-- Along the ray `t x`, `Φ(t⟪a_y,x⟫) → 𝟙{⟪a_y,x⟫ = 0}` as `t → ∞`. -/
theorem tendsto_gaussianFun_nat_mul (u : ℝ) :
    Tendsto (fun n : ℕ => gaussianFun (n * u)) atTop (𝓝 (if u = 0 then 1 else 0)) := by
  split_ifs with hu
  · simp [hu, gaussianFun]
  · unfold gaussianFun
    have h1 : Tendsto (fun n : ℕ => -(n : ℝ) ^ 2 * u ^ 2 / 2) atTop atBot := by
      have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (u ^ 2 / 2)) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop |>.atTop_mul_const
          (by positivity)
      refine (tendsto_neg_atTop_atBot.comp h2).congr fun n => ?_
      simp only [Function.comp_apply]
      ring
    refine (Real.tendsto_exp_atBot.comp h1).congr fun n => ?_
    simp only [Function.comp_apply]
    congr 1
    ring

omit [IsFiniteMeasure m] in
/-- The limit of the observable along the ray `n x`: `F_φ(n x) → ∫ 𝟙{⟪a_y,x⟫=0} w_φ dm`. -/
theorem IsLayerData.tendsto_layerObservable_gaussianFun_nat_smul (hL : IsLayerData m a b)
    (φ : Y) (x : H) :
    Tendsto (fun n : ℕ => layerObservable m a b gaussianFun φ ((n : ℝ) • x)) atTop
      (𝓝 (∫ y, (if ⟪a y, x⟫ = 0 then (1 : ℂ) else 0) * layerWeight b φ y ∂m)) := by
  simp_rw [hL.layerObservable_gaussianFun_eq φ]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖layerWeight b φ y‖) (fun n =>
    ((hL.stronglyMeasurable_gaussianFun_inner _).mul
      (hL.stronglyMeasurable_layerWeight φ)).aestronglyMeasurable)
    (hL.integrable_layerWeight φ).norm (fun n => Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ?_)
  · rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussianFun_le_one _)
  · refine Tendsto.mul_const _ ?_
    have h := (tendsto_gaussianFun_nat_mul ⟪a y, x⟫).comp
      (tendsto_id (x := atTop (α := ℕ)))
    have h2 := (Complex.continuous_ofReal.tendsto _).comp h
    refine h2.congr' (Eventually.of_forall fun n => ?_) |>.trans ?_
    · simp only [Function.comp_apply, id, inner_smul_right]
    · split_ifs <;> simp

omit [IsFiniteMeasure m] in
/-- **Example `ex:operator-layer`(iv)**: if `A` has infinite rank and `w_φ > 0` almost
everywhere, the Gaussian-activation observable `F_φ` is not cylindrical. -/
theorem IsLayerData.not_isCylindrical_layerObservable_gaussianFun (hL : IsLayerData m a b)
    (φ : Y) (hA : HasInfiniteRank (layerA m a))
    (hw : ∀ᵐ y ∂m, 0 < (layerWeight b φ y).re ∧ (layerWeight b φ y).im = 0) :
    ¬ IsCylindrical (layerObservable m a b gaussianFun φ) := by
  rintro ⟨k, L, G, hG⟩
  obtain ⟨x, hLx, hAx⟩ := hA.exists_mem_ker_not_mem_ker L
  -- along the ray the observable is constant
  have hconst : ∀ n : ℕ, layerObservable m a b gaussianFun φ ((n : ℝ) • x) =
      layerObservable m a b gaussianFun φ 0 := by
    intro n
    rw [hG, Function.comp_apply, Function.comp_apply, map_smul, hLx, smul_zero, map_zero]
  have hlim := hL.tendsto_layerObservable_gaussianFun_nat_smul φ x
  simp_rw [hconst] at hlim
  have heq := tendsto_nhds_unique hlim tendsto_const_nhds
  -- the value at the origin is `∫ w_φ`
  rw [hL.layerObservable_gaussianFun_eq φ 0] at heq
  simp only [inner_zero_right, gaussianFun, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul] at heq
  -- hence `∫ 𝟙{⟪a_y,x⟫ ≠ 0} w_φ dm = 0`, which forces `⟪a_y, x⟫ = 0` a.e.
  have hint := hL.integrable_layerWeight φ
  have hsub : ∫ y, (if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) * layerWeight b φ y ∂m = 0 := by
    have h1 : (fun y => (if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) * layerWeight b φ y) =
        fun y => layerWeight b φ y - (if ⟪a y, x⟫ = 0 then (1 : ℂ) else 0) * layerWeight b φ y := by
      funext y
      split_ifs <;> simp
    have hind : Integrable (fun y => (if ⟪a y, x⟫ = 0 then (1 : ℂ) else 0) * layerWeight b φ y)
        m := by
      refine hint.bdd_mul (c := 1) ?_ (Eventually.of_forall fun y => ?_)
      · exact (Measurable.ite ((hL.stronglyMeasurable_inner x).measurable
          (measurableSet_singleton 0)) measurable_const measurable_const).aestronglyMeasurable
      · split_ifs <;> simp
    rw [h1, integral_sub hint hind, ← heq, sub_self]
  -- the real part of the integrand is nonnegative and integrates to zero
  have hmeas' : AEStronglyMeasurable (fun y => if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) m :=
    (Measurable.ite ((hL.stronglyMeasurable_inner x).measurable (measurableSet_singleton 0))
      measurable_const measurable_const).aestronglyMeasurable
  have hind' : Integrable (fun y => (if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) * layerWeight b φ y)
      m :=
    hint.bdd_mul (c := 1) hmeas' (Eventually.of_forall fun y => by split_ifs <;> simp)
  have hre_nonneg : 0 ≤ᵐ[m] fun y =>
      ((if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) * layerWeight b φ y).re := by
    filter_upwards [hw] with y hy
    split_ifs <;> simp [hy.1.le]
  have hre_zero : ∫ y, ((if ⟪a y, x⟫ = 0 then (0 : ℂ) else 1) * layerWeight b φ y).re ∂m = 0 := by
    have h := integral_re hind'
    rw [hsub] at h
    simpa using h
  have hae := (integral_eq_zero_iff_of_nonneg_ae hre_nonneg hind'.re).mp hre_zero
  apply hAx
  rw [hL.layerA_eq_zero_iff]
  filter_upwards [hae, hw] with y hy hwy
  by_contra hne
  simp only [Pi.zero_apply, hne, if_false, one_mul] at hy
  linarith [hwy.1]

end NotCylindrical

end OperatorRidgelet
