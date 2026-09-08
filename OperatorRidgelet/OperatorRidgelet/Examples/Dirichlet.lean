import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.ToMathlib.LpOfReal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Dirichlet solution operator: bounds on the Green kernel

The Green kernel `g(y,t) = sinh(min(y,t)) sinh(1 - max(y,t)) / sinh 1` of Example
`ex:dirichlet` is nonnegative and bounded by `sinh 1` on `(0,1)²` (`abs_dirichletKernel_le`),
and Lipschitz in `y` uniformly in `t` (`abs_dirichletKernel_sub_le`).  Hence the directions
`a_y = g(y,·)` are bounded in `L²(0,1)` (`norm_dirichletDirection_le`) and depend continuously
on `y` (`continuous_dirichletDirection`), so the standing hypotheses of the neural-operator
layer hold (`isLayerData_dirichlet`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Set Filter
open scoped ENNReal NNReal

/-! ### Pointwise bounds on the kernel -/

/-- `sinh` is `cosh 1`-Lipschitz on `[0,1]`. -/
theorem lipschitzOnWith_sinh_Icc :
    LipschitzOnWith (Real.toNNReal (Real.cosh 1)) Real.sinh (Icc (0 : ℝ) 1) := by
  refine (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => Real.differentiable_sinh x) fun x hx => ?_
  rw [Real.deriv_sinh, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos x), Real.coe_toNNReal _ (Real.cosh_pos 1).le]
  exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hx.1, abs_one]; exact hx.2)

/-- `g(y,t) ≥ 0` on `(0,1)²`. -/
theorem dirichletKernel_nonneg {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ dirichletKernel y t := by
  unfold dirichletKernel
  have h1 : 0 ≤ Real.sinh (min y t) := Real.sinh_nonneg_iff.mpr (le_min hy.1.le ht.1.le)
  have h2 : 0 ≤ Real.sinh (1 - max y t) :=
    Real.sinh_nonneg_iff.mpr (by linarith [max_le hy.2.le ht.2.le])
  have h3 : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  positivity

/-- `g(y,t) ≤ sinh 1` on `(0,1)²`. -/
theorem dirichletKernel_le_sinh_one {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : dirichletKernel y t ≤ Real.sinh 1 := by
  unfold dirichletKernel
  have h3 : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  rw [div_le_iff₀ h3]
  have h0 : 0 ≤ Real.sinh (min y t) := Real.sinh_nonneg_iff.mpr (le_min hy.1.le ht.1.le)
  have h1 : Real.sinh (min y t) ≤ Real.sinh 1 :=
    Real.sinh_le_sinh.mpr ((min_le_left _ _).trans hy.2.le)
  have h2 : Real.sinh (1 - max y t) ≤ Real.sinh 1 :=
    Real.sinh_le_sinh.mpr (by linarith [le_max_left y t, hy.1])
  exact mul_le_mul h1 h2 (Real.sinh_nonneg_iff.mpr (by linarith [max_le hy.2.le ht.2.le])) h3.le

/-- `|g(y,t)| ≤ sinh 1` on `(0,1)²`. -/
theorem abs_dirichletKernel_le {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    |dirichletKernel y t| ≤ Real.sinh 1 :=
  abs_le.mpr ⟨by linarith [dirichletKernel_nonneg hy ht, Real.sinh_pos_iff.mpr (one_pos : (0:ℝ) < 1)],
    dirichletKernel_le_sinh_one hy ht⟩

/-- The kernel is `2 cosh 1`-Lipschitz in `y`, uniformly in `t ∈ (0,1)`. -/
theorem abs_dirichletKernel_sub_le {y y' t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (hy' : y' ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    |dirichletKernel y t - dirichletKernel y' t| ≤ 2 * Real.cosh 1 * |y - y'| := by
  unfold dirichletKernel
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  have hc : 0 ≤ Real.cosh 1 := (Real.cosh_pos 1).le
  have hL := lipschitzOnWith_sinh_Icc
  have hmin : ∀ {u}, u ∈ Ioo (0 : ℝ) 1 → min u t ∈ Icc (0 : ℝ) 1 := fun {u} hu =>
    ⟨le_min hu.1.le ht.1.le, (min_le_left _ _).trans hu.2.le⟩
  have hmax : ∀ {u}, u ∈ Ioo (0 : ℝ) 1 → 1 - max u t ∈ Icc (0 : ℝ) 1 := fun {u} hu =>
    ⟨by linarith [max_le hu.2.le ht.2.le], by linarith [le_max_left u t, hu.1]⟩
  have hf : |Real.sinh (min y t) - Real.sinh (min y' t)| ≤ Real.cosh 1 * |y - y'| := by
    have h := hL.dist_le_mul (min y t) (hmin hy) (min y' t) (hmin hy')
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hc] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
    have := abs_min_sub_min_le_max y t y' t
    simpa using this
  have hg : |Real.sinh (1 - max y t) - Real.sinh (1 - max y' t)| ≤ Real.cosh 1 * |y - y'| := by
    have h := hL.dist_le_mul (1 - max y t) (hmax hy) (1 - max y' t) (hmax hy')
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hc] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
    have := abs_max_sub_max_le_abs y y' t
    rw [show (1 - max y t) - (1 - max y' t) = -(max y t - max y' t) by ring, abs_neg]
    exact this
  have hgb : |Real.sinh (1 - max y t)| ≤ Real.sinh 1 := by
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (hmax hy).1)]
    exact Real.sinh_le_sinh.mpr (hmax hy).2
  have hfb : |Real.sinh (min y' t)| ≤ Real.sinh 1 := by
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (hmin hy').1)]
    exact Real.sinh_le_sinh.mpr (hmin hy').2
  rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc |Real.sinh (min y t) * Real.sinh (1 - max y t) -
          Real.sinh (min y' t) * Real.sinh (1 - max y' t)|
      = |(Real.sinh (min y t) - Real.sinh (min y' t)) * Real.sinh (1 - max y t) +
          Real.sinh (min y' t) * (Real.sinh (1 - max y t) - Real.sinh (1 - max y' t))| := by
        ring_nf
    _ ≤ |Real.sinh (min y t) - Real.sinh (min y' t)| * |Real.sinh (1 - max y t)| +
          |Real.sinh (min y' t)| * |Real.sinh (1 - max y t) - Real.sinh (1 - max y' t)| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ Real.cosh 1 * |y - y'| * Real.sinh 1 + Real.sinh 1 * (Real.cosh 1 * |y - y'|) := by
        gcongr
    _ = 2 * Real.cosh 1 * |y - y'| * Real.sinh 1 := by ring

/-- The kernel is jointly continuous. -/
theorem continuous_dirichletKernel : Continuous fun p : ℝ × ℝ => dirichletKernel p.1 p.2 := by
  unfold dirichletKernel
  fun_prop

/-! ### The directions in `L²(0,1)` -/

/-- `g(y,·) ∈ L²(0,1)` for `y ∈ (0,1)`. -/
theorem memLp_dirichletKernel (y : UnitOpenInterval) :
    MemLp (fun t : UnitOpenInterval => dirichletKernel y t) 2 volume := by
  refine MemLp.of_bound ?_ (Real.sinh 1) (Eventually.of_forall fun t => ?_)
  · exact (continuous_dirichletKernel.comp (continuous_const.prodMk
      continuous_subtype_val)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_dirichletKernel_le y.2 t.2

/-- The direction `a_y` is the `L²` class of `g(y,·)`. -/
theorem dirichletDirection_eq (y : UnitOpenInterval) :
    dirichletDirection y = (memLp_dirichletKernel y).toLp _ := by
  unfold dirichletDirection dirichletKernelFn toLpOrZero
  rw [dif_pos (memLp_dirichletKernel y)]

/-- Lebesgue measure on `(0,1)` has total mass one, as an `ℝ≥0`. -/
theorem measureUnivNNReal_volume_unitOpenInterval :
    measureUnivNNReal (volume : Measure UnitOpenInterval) = 1 := by
  rw [← ENNReal.coe_inj, coe_measureUnivNNReal, measure_univ, ENNReal.coe_one]

/-- **Example `ex:dirichlet`**: `‖a_y‖₂ ≤ sinh 1`. -/
theorem norm_dirichletDirection_le (y : UnitOpenInterval) :
    ‖dirichletDirection y‖ ≤ Real.sinh 1 := by
  rw [dirichletDirection_eq]
  have h := Lp.norm_le_of_ae_bound (f := (memLp_dirichletKernel y).toLp _)
    (Real.sinh_pos_iff.mpr (one_pos : (0 : ℝ) < 1)).le ?_
  · simpa [measureUnivNNReal_volume_unitOpenInterval] using h
  · filter_upwards [(memLp_dirichletKernel y).coeFn_toLp] with t ht
    rw [ht, Real.norm_eq_abs]
    exact abs_dirichletKernel_le y.2 t.2

/-- `y ↦ a_y` is `2 cosh 1`-Lipschitz into `L²(0,1)`. -/
theorem norm_dirichletDirection_sub_le (y y' : UnitOpenInterval) :
    ‖dirichletDirection y - dirichletDirection y'‖ ≤ 2 * Real.cosh 1 * |(y : ℝ) - y'| := by
  rw [dirichletDirection_eq, dirichletDirection_eq, ← MemLp.toLp_sub]
  have h := Lp.norm_le_of_ae_bound (f := ((memLp_dirichletKernel y).sub
    (memLp_dirichletKernel y')).toLp _) (by positivity : 0 ≤ 2 * Real.cosh 1 * |(y : ℝ) - y'|) ?_
  · simpa [measureUnivNNReal_volume_unitOpenInterval] using h
  · filter_upwards [((memLp_dirichletKernel y).sub (memLp_dirichletKernel y')).coeFn_toLp] with t ht
    rw [ht, Pi.sub_apply, Real.norm_eq_abs]
    exact abs_dirichletKernel_sub_le y.2 y'.2 t.2

/-- `y ↦ a_y` is Lipschitz. -/
theorem lipschitzWith_dirichletDirection :
    LipschitzWith (Real.toNNReal (2 * Real.cosh 1)) dirichletDirection :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact norm_dirichletDirection_sub_le y y'

/-- `y ↦ a_y` is continuous. -/
theorem continuous_dirichletDirection : Continuous dirichletDirection :=
  lipschitzWith_dirichletDirection.continuous

/-- `y ↦ b_y` is continuous. -/
theorem continuous_dirichletOutput : Continuous dirichletOutput :=
  (Complex.ofRealCLM.compLpL 2 volume).continuous.comp continuous_dirichletDirection

/-- `‖b_y‖ ≤ sinh 1`. -/
theorem norm_dirichletOutput_le (y : UnitOpenInterval) : ‖dirichletOutput y‖ ≤ Real.sinh 1 := by
  unfold dirichletOutput
  rw [norm_ofRealCLM_compLp]
  exact norm_dirichletDirection_le y

/-- **Example `ex:dirichlet`**: the standing hypotheses of the neural-operator layer hold. -/
theorem isLayerData_dirichlet : IsLayerData volume dirichletDirection dirichletOutput where
  stronglyMeasurable_a := continuous_dirichletDirection.stronglyMeasurable
  bounded_a := ⟨Real.sinh 1, norm_dirichletDirection_le⟩
  stronglyMeasurable_b := continuous_dirichletOutput.stronglyMeasurable
  integrable_b := Integrable.of_bound continuous_dirichletOutput.aestronglyMeasurable
    (Real.sinh 1) (Eventually.of_forall norm_dirichletOutput_le)

end OperatorRidgelet
