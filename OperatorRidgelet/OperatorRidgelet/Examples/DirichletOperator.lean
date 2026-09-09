import OperatorRidgelet.Examples.Dirichlet
import OperatorRidgelet.Examples.OperatorLayer
import LeanRidgelet.ToMathlib.BochnerIntegralL2

/-!
# The Dirichlet solution operator as an integral operator

The Green kernel `g` of Example `ex:dirichlet` is bounded by `sinh 1` on `(0,1)²`, so
`x ↦ (y ↦ ∫₀¹ g(y,t) x(t) dt)` is a bounded linear operator on `L²(0,1)` of norm at most
`sinh 1` (`dirichletIntegralCLM`).  Hence the integral operator `integralOperator volume g` of
`OperatorRidgelet.Examples.Defs`, which is defined by choice among the bounded operators with
this action, exists, and `𝖦 x = ∫₀¹ g(·,t) x(t) dt` almost everywhere
(`dirichletOperator_apply_ae`).  Since the kernel is symmetric, the neural-operator layer with
`a_y = b_y = g(y,·)` is `ℱ(x) = 𝖦 β(𝖦 x)` (`operatorLayer_dirichlet_eq`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

/-- The `L¹` norm of an `L²` function on a probability space is at most its `L²` norm. -/
theorem integral_norm_le_norm_unitL2 (x : UnitL2) : ∫ t, ‖x t‖ ≤ ‖x‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable x), Lp.norm_def,
    ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top x)
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two (Lp.aestronglyMeasurable x))

/-- The integral `y ↦ ∫₀¹ g(y,t) x(t) dt` of an `L²` function against the Green kernel. -/
def dirichletIntegralFun (x : UnitL2) (y : UnitOpenInterval) : ℝ :=
  ∫ t : UnitOpenInterval, dirichletKernel y t * x t

/-- The kernel integrand `t ↦ g(y,t) x(t)` is integrable. -/
theorem integrable_dirichletKernel_mul (x : UnitL2) (y : UnitOpenInterval) :
    Integrable (fun t : UnitOpenInterval => dirichletKernel y t * x t) volume := by
  refine ((Lp.memLp x).integrable one_le_two).bdd_mul (c := Real.sinh 1) ?_
    (Eventually.of_forall fun t => ?_)
  · exact (continuous_dirichletKernel.comp (continuous_const.prodMk
      continuous_subtype_val)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_dirichletKernel_le y.2 t.2

/-- The pointwise bound `|∫₀¹ g(y,t) x(t) dt| ≤ sinh 1 ‖x‖₂`. -/
theorem abs_dirichletIntegralFun_le (x : UnitL2) (y : UnitOpenInterval) :
    |dirichletIntegralFun x y| ≤ Real.sinh 1 * ‖x‖ := by
  unfold dirichletIntegralFun
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t : UnitOpenInterval, ‖dirichletKernel y t * x t‖
      ≤ ∫ t : UnitOpenInterval, Real.sinh 1 * ‖x t‖ := by
        refine integral_mono (integrable_dirichletKernel_mul x y).norm
          (((Lp.memLp x).integrable one_le_two).norm.const_mul _) fun t => ?_
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_dirichletKernel_le y.2 t.2) (norm_nonneg _)
    _ = Real.sinh 1 * ∫ t : UnitOpenInterval, ‖x t‖ := integral_const_mul _ _
    _ ≤ Real.sinh 1 * ‖x‖ := by
        gcongr
        exact integral_norm_le_norm_unitL2 x

/-- `y ↦ ∫₀¹ g(y,t) x(t) dt` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_dirichletIntegralFun (x : UnitL2) :
    AEStronglyMeasurable (dirichletIntegralFun x) volume := by
  have h : AEStronglyMeasurable (fun p : UnitOpenInterval × UnitOpenInterval =>
      dirichletKernel p.1 p.2 * x p.2) (volume.prod volume) :=
    (continuous_dirichletKernel.comp (continuous_subtype_val.prodMap
      continuous_subtype_val)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable x).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  exact h.integral_prod_right'

/-- `y ↦ ∫₀¹ g(y,t) x(t) dt` belongs to `L²(0,1)`. -/
theorem memLp_dirichletIntegralFun (x : UnitL2) : MemLp (dirichletIntegralFun x) 2 volume :=
  MemLp.of_bound (aestronglyMeasurable_dirichletIntegralFun x) (Real.sinh 1 * ‖x‖)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact abs_dirichletIntegralFun_le x y)

/-- The integral operator with the Green kernel, as a linear map on `L²(0,1)`. -/
def dirichletIntegralLinear : UnitL2 →ₗ[ℝ] UnitL2 where
  toFun x := (memLp_dirichletIntegralFun x).toLp _
  map_add' x y := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, dirichletIntegralFun]
    rw [← integral_add (integrable_dirichletKernel_mul x z) (integrable_dirichletKernel_mul y z)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add x y] with t ht
    rw [ht, Pi.add_apply, mul_add]
  map_smul' c x := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply, dirichletIntegralFun, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c x] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring

/-- The integral operator with the Green kernel, as a bounded operator on `L²(0,1)`. -/
def dirichletIntegralCLM : UnitL2 →L[ℝ] UnitL2 :=
  dirichletIntegralLinear.mkContinuous (Real.sinh 1) fun x => by
    change ‖(memLp_dirichletIntegralFun x).toLp _‖ ≤ Real.sinh 1 * ‖x‖
    have h := Lp.norm_le_of_ae_bound (f := (memLp_dirichletIntegralFun x).toLp _)
      (by positivity : 0 ≤ Real.sinh 1 * ‖x‖) ?_
    · simpa [measureUnivNNReal_volume_unitOpenInterval] using h
    · filter_upwards [(memLp_dirichletIntegralFun x).coeFn_toLp] with y hy
      rw [hy, Real.norm_eq_abs]
      exact abs_dirichletIntegralFun_le x y

/-- `dirichletIntegralCLM x = ∫₀¹ g(·,t) x(t) dt` almost everywhere. -/
theorem dirichletIntegralCLM_apply_ae (x : UnitL2) :
    (dirichletIntegralCLM x : UnitOpenInterval → ℝ) =ᵐ[volume]
      fun y : UnitOpenInterval => ∫ t : UnitOpenInterval, dirichletKernel y t * x t :=
  (memLp_dirichletIntegralFun x).coeFn_toLp

/-- The bounded operators with the action of the Green kernel exist. -/
theorem exists_dirichlet_integralOperator :
    ∃ T : UnitL2 →L[ℝ] UnitL2, ∀ x : UnitL2, (T x : UnitOpenInterval → ℝ) =ᵐ[volume]
      fun y : UnitOpenInterval =>
        ∫ t : UnitOpenInterval, (fun y t : UnitOpenInterval => dirichletKernel y t) y t * x t :=
  ⟨dirichletIntegralCLM, dirichletIntegralCLM_apply_ae⟩

/-- **Example `ex:dirichlet`**: `𝖦 x = ∫₀¹ g(·,t) x(t) dt` almost everywhere. -/
theorem dirichletOperator_apply_ae (x : UnitL2) :
    (dirichletOperator x : UnitOpenInterval → ℝ) =ᵐ[volume]
      fun y : UnitOpenInterval => ∫ t : UnitOpenInterval, dirichletKernel y t * x t := by
  unfold dirichletOperator integralOperator
  rw [dif_pos exists_dirichlet_integralOperator]
  exact exists_dirichlet_integralOperator.choose_spec x


/-! ### The layer `ℱ(x) = 𝖦 β(𝖦 x)` -/

/-- The Green kernel is symmetric. -/
theorem dirichletKernel_symm (y t : ℝ) : dirichletKernel y t = dirichletKernel t y := by
  unfold dirichletKernel
  rw [min_comm, max_comm]

/-- `⟪a_y, x⟫ = ∫₀¹ g(y,t) x(t) dt`. -/
theorem inner_dirichletDirection (y : UnitOpenInterval) (x : UnitL2) :
    ⟪dirichletDirection y, x⟫ = dirichletIntegralFun x y := by
  rw [L2.inner_def, dirichletDirection_eq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_dirichletKernel y).coeFn_toLp] with t ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm]

/-- The output `b_y` is the class of `t ↦ g(y,t)`. -/
theorem dirichletOutput_coeFn_ae (y : UnitOpenInterval) :
    ⇑(dirichletOutput y) =ᵐ[volume]
      fun t : UnitOpenInterval => ((dirichletKernel y t : ℝ) : ℂ) := by
  unfold dirichletOutput
  have h : dirichletKernelFn y = (memLp_dirichletKernel y).toLp _ := dirichletDirection_eq y
  rw [h]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' ((memLp_dirichletKernel y).toLp _),
    (memLp_dirichletKernel y).coeFn_toLp] with t ht ht'
  rw [ht, Complex.ofRealCLM_apply, ht']

/-- The values `β(𝖦x)` of a continuous activation on `𝖦x` lie in `L²(0,1)`. -/
theorem memLp_comp_dirichletOperator {β : ℝ → ℝ} (hβ : Continuous β) (x : UnitL2) :
    MemLp (fun t => β (dirichletOperator x t)) 2 volume := by
  obtain ⟨C, hC⟩ := isLayerData_dirichlet.exists_bound_comp_inner hβ x
  refine MemLp.of_bound (hβ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)) C ?_
  filter_upwards [dirichletOperator_apply_ae x] with t ht
  rw [Real.norm_eq_abs, ht]
  have := hC t
  rwa [inner_dirichletDirection] at this

/-- `𝖦 β(𝖦x)` is `t ↦ ∫₀¹ g(t,y) β((𝖦x)(y)) dy` almost everywhere. -/
theorem dirichletOperator_comp_coeFn_ae {β : ℝ → ℝ} (hβ : Continuous β) (x : UnitL2) :
    ⇑(dirichletOperator (toLpOrZero 2 volume fun t => β (dirichletOperator x t))) =ᵐ[volume]
      fun t : UnitOpenInterval =>
        ∫ y : UnitOpenInterval, dirichletKernel t y * β (dirichletIntegralFun x y) := by
  have hmem := memLp_comp_dirichletOperator hβ x
  have hv : toLpOrZero 2 volume (fun t => β (dirichletOperator x t)) = hmem.toLp _ := by
    unfold toLpOrZero
    rw [dif_pos hmem]
  rw [hv]
  filter_upwards [dirichletOperator_apply_ae (hmem.toLp _)] with t ht
  rw [ht]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp, dirichletOperator_apply_ae x] with y hy hy'
  rw [hy, hy']
  rfl

/-- The two-variable integrand `(y,t) ↦ β(⟪a_y, x⟫) g(y,t)` of the Dirichlet layer is
integrable on `(0,1)²`. -/
theorem integrable_dirichlet_layer_integrand {β : ℝ → ℝ} (hβ : Continuous β) (x : UnitL2) :
    Integrable (fun p : UnitOpenInterval × UnitOpenInterval =>
      ((β ⟪dirichletDirection p.1, x⟫ : ℝ) : ℂ) * ((dirichletKernel p.1 p.2 : ℝ) : ℂ))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := isLayerData_dirichlet.exists_bound_comp_inner hβ x
  have hc : Continuous fun y : UnitOpenInterval => β ⟪dirichletDirection y, x⟫ :=
    hβ.comp (continuous_dirichletDirection.inner continuous_const)
  refine Integrable.of_bound ?_ (C * Real.sinh 1) (Eventually.of_forall fun p => ?_)
  · exact ((Complex.continuous_ofReal.comp (hc.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (continuous_dirichletKernel.comp
        (continuous_subtype_val.prodMap continuous_subtype_val)))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hC p.1) (abs_dirichletKernel_le p.1.2 p.2.2) (abs_nonneg _)
      ((abs_nonneg _).trans (hC p.1))

/-- **Example `ex:dirichlet`**: with `a_y = b_y = g(y,·)` the layer is `ℱ(x) = 𝖦 β(𝖦x)`. -/
theorem operatorLayer_dirichlet_eq {β : ℝ → ℝ} (hβ : Continuous β) (x : UnitL2) :
    operatorLayer volume dirichletDirection dirichletOutput β x =
      Complex.ofRealCLM.compLp
        (dirichletOperator (toLpOrZero 2 volume fun t => β (dirichletOperator x t))) := by
  refine Lp.ext ?_
  have h1 : ⇑(operatorLayer volume dirichletDirection dirichletOutput β x) =ᵐ[volume]
      fun t : UnitOpenInterval => ∫ y : UnitOpenInterval,
        ((β ⟪dirichletDirection y, x⟫ : ℝ) : ℂ) * ((dirichletKernel y t : ℝ) : ℂ) := by
    unfold operatorLayer
    refine integral_L2_coeFn_ae
      (F := fun y t : UnitOpenInterval =>
        ((β ⟪dirichletDirection y, x⟫ : ℝ) : ℂ) * ((dirichletKernel y t : ℝ) : ℂ))
      (isLayerData_dirichlet.integrable_ofReal_comp_inner_smul hβ x)
      (integrable_dirichlet_layer_integrand hβ x) (Eventually.of_forall fun y => ?_)
    filter_upwards [Lp.coeFn_smul ((β ⟪dirichletDirection y, x⟫ : ℝ) : ℂ) (dirichletOutput y),
      dirichletOutput_coeFn_ae y] with t ht ht'
    rw [ht, Pi.smul_apply, ht', smul_eq_mul]
  refine h1.trans ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' _, dirichletOperator_comp_coeFn_ae hβ x]
    with t ht ht'
  rw [ht, Complex.ofRealCLM_apply, ht', ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_dirichletDirection, Complex.ofReal_mul]
  rw [dirichletKernel_symm, mul_comm]

end OperatorRidgelet
