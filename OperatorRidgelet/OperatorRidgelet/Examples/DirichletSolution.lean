import OperatorRidgelet.Examples.Dirichlet
import OperatorRidgelet.Examples.DirichletOperator
import OperatorRidgelet.ToMathlib.HyperbolicSineIntegral
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The classical boundary-value equation for the Green operator -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Set Filter Topology

/-- The split Green formula, in terms of two primitives of the continuous source. -/
def dirichletSplit (x : ℝ → ℝ) (y : ℝ) : ℝ :=
  (Real.sinh (1 - y) * (∫ t in (0 : ℝ)..y, Real.sinh t * x t) +
    Real.sinh y * (∫ t in y..(1 : ℝ), Real.sinh (1 - t) * x t)) / Real.sinh 1

/-- The first derivative of the split Green formula. -/
def dirichletSplitDeriv (x : ℝ → ℝ) (y : ℝ) : ℝ :=
  (-Real.cosh (1 - y) * (∫ t in (0 : ℝ)..y, Real.sinh t * x t) +
    Real.cosh y * (∫ t in y..(1 : ℝ), Real.sinh (1 - t) * x t)) / Real.sinh 1

/-- Splitting the Green integral at its corner gives the primitive formula. -/
theorem dirichletSolution_eq_split {x : ℝ → ℝ} (hx : Continuous x) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : dirichletSolution x y = dirichletSplit x y := by
  have hc : Continuous fun t : ℝ => dirichletKernel y t * x t :=
    (continuous_dirichletKernel.comp (continuous_const.prodMk continuous_id)).mul hx
  have hL : (∫ t in (0 : ℝ)..y, dirichletKernel y t * x t) =
      Real.sinh (1 - y) / Real.sinh 1 * (∫ t in (0 : ℝ)..y, Real.sinh t * x t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hy.1] at ht
    simp only [dirichletKernel, min_eq_right ht.2, max_eq_left ht.2]
    ring
  have hR : (∫ t in y..(1 : ℝ), dirichletKernel y t * x t) =
      Real.sinh y / Real.sinh 1 * (∫ t in y..(1 : ℝ), Real.sinh (1 - t) * x t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hy.2] at ht
    simp only [dirichletKernel, min_eq_left ht.1, max_eq_right ht.1]
    ring
  unfold dirichletSolution
  change (∫ t : Ioo (0 : ℝ) 1, dirichletKernel y t * x t
    ∂(volume.comap Subtype.val)) = _
  rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioo
      (fun t : ℝ => dirichletKernel y t * x t), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 y)
      (hc.intervalIntegrable y 1), hL, hR]
  unfold dirichletSplit
  ring

/-- Differentiate the split Green formula once; the two endpoint terms cancel. -/
theorem hasDerivAt_dirichletSplit {x : ℝ → ℝ} (hx : Continuous x) (y : ℝ) :
    HasDerivAt (dirichletSplit x) (dirichletSplitDeriv x y) y := by
  have hA : Continuous fun t : ℝ => Real.sinh t * x t := Real.continuous_sinh.mul hx
  have hB : Continuous fun t : ℝ => Real.sinh (1 - t) * x t :=
    (Real.continuous_sinh.comp (continuous_const.sub continuous_id)).mul hx
  have hdA := intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable 0 y)
    hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt
  have hdB := intervalIntegral.integral_hasDerivAt_left (hB.intervalIntegrable y 1)
    hB.aestronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt
  have hs := ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).sinh
  convert! ((hs.mul hdA).add ((Real.hasDerivAt_sinh y).mul hdB)).div_const (Real.sinh 1) using 1
  simp only [dirichletSplitDeriv, Pi.sub_apply, id_eq]
  ring

/-- Differentiate the first derivative; the hyperbolic addition formula supplies the source. -/
theorem hasDerivAt_dirichletSplitDeriv {x : ℝ → ℝ} (hx : Continuous x) (y : ℝ) :
    HasDerivAt (dirichletSplitDeriv x) (dirichletSplit x y - x y) y := by
  have hA : Continuous fun t : ℝ => Real.sinh t * x t := Real.continuous_sinh.mul hx
  have hB : Continuous fun t : ℝ => Real.sinh (1 - t) * x t :=
    (Real.continuous_sinh.comp (continuous_const.sub continuous_id)).mul hx
  have hdA := intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable 0 y)
    hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt
  have hdB := intervalIntegral.integral_hasDerivAt_left (hB.intervalIntegrable y 1)
    hB.aestronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt
  have hc := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).cosh).neg
  convert! ((hc.mul hdA).add ((Real.hasDerivAt_cosh y).mul hdB)).div_const (Real.sinh 1) using 1
  · simp only [dirichletSplit, Pi.sub_apply, Pi.neg_apply, id_eq]
    have hs : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr one_pos)
    have hadd : Real.sinh (1 - y) * Real.cosh y + Real.cosh (1 - y) * Real.sinh y = Real.sinh 1
        := by
      rw [← Real.sinh_add]
      congr 1
      ring
    field_simp
    nlinarith [congrArg (fun r : ℝ => r * x y) hadd]

/-- The Green integral solves the Dirichlet problem for every continuous source. -/
theorem dirichletSolution_boundary_equation {x : ℝ → ℝ} (hx : Continuous x) :
    dirichletSolution x 0 = 0 ∧ dirichletSolution x 1 = 0 ∧
      (∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (dirichletSolution x) y) ∧
      ∀ y ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (deriv (dirichletSolution x)) (dirichletSolution x y - x y) y := by
  have heq (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      dirichletSolution x =ᶠ[𝓝 y] dirichletSplit x := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact dirichletSolution_eq_split hx ⟨hz.1.le, hz.2.le⟩
  have hd (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (dirichletSolution x) (dirichletSplitDeriv x y) y :=
    (hasDerivAt_dirichletSplit hx y).congr_of_eventuallyEq (heq y hy)
  refine ⟨?_, ?_, fun y hy => (hd y hy).differentiableAt, fun y hy => ?_⟩
  · rw [dirichletSolution_eq_split hx (by norm_num)]
    simp [dirichletSplit]
  · rw [dirichletSolution_eq_split hx (by norm_num)]
    simp [dirichletSplit]
  · have hderiv : deriv (dirichletSolution x) =ᶠ[𝓝 y] dirichletSplitDeriv x := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact (hd z hz).deriv
    rw [dirichletSolution_eq_split hx ⟨hy.1.le, hy.2.le⟩]
    exact (hasDerivAt_dirichletSplitDeriv hx y).congr_of_eventuallyEq hderiv

/-- The Green formula acts diagonally on a sine with integral frequency. -/
theorem dirichletSolution_sin (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    dirichletSolution (fun t => Real.sin (n * Real.pi * t)) y =
      dirichletEigenvalue n * Real.sin (n * Real.pi * y) := by
  rw [dirichletSolution_eq_split (by fun_prop) hy]
  unfold dirichletSplit
  rw [Real.integral_sinh_mul_sin, Real.integral_sinh_sub_mul_sin]
  simp only [mul_zero, Real.sin_zero, Real.sinh_zero, Real.cosh_zero, Real.cos_zero,
    mul_one, one_mul, sub_self, zero_mul, sub_zero, Real.sin_nat_mul_pi, zero_div,
    neg_zero, zero_sub]
  have hs : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr one_pos)
  have hadd : Real.sinh (1 - y) * Real.cosh y + Real.cosh (1 - y) * Real.sinh y = Real.sinh 1 := by
    rw [← Real.sinh_add]
    congr 1
    ring
  unfold dirichletEigenvalue
  have he : (1 + (n * Real.pi) ^ 2 : ℝ) = 1 + Real.pi ^ 2 * (n : ℝ) ^ 2 := by ring
  rw [he]
  field_simp
  nlinarith [congrArg (fun r : ℝ => r * Real.sin (y * n * Real.pi)) hadd]

/-- The normalized sine lies in the real `L²` space of the interval. -/
theorem memLp_dirichletEigenfunction (n : ℕ) :
    MemLp (fun t : UnitOpenInterval => Real.sqrt 2 * Real.sin (n * Real.pi * t)) 2 volume := by
  refine MemLp.of_bound (by fun_prop) (Real.sqrt 2) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)

/-- The representative of a Dirichlet sine eigenfunction agrees almost everywhere with its formula.
-/
theorem dirichletEigenfunction_coeFn_ae (n : ℕ) :
    (dirichletEigenfunction n : UnitOpenInterval → ℝ) =ᵐ[volume]
      fun t => Real.sqrt 2 * Real.sin (n * Real.pi * t) := by
  unfold dirichletEigenfunction toLpOrZero
  rw [dif_pos (memLp_dirichletEigenfunction n)]
  exact (memLp_dirichletEigenfunction n).coeFn_toLp

/-- The exact sine eigenpairs of the Dirichlet Green operator (also valid for the zero sine). -/
theorem dirichletOperator_eigenfunction (n : ℕ) :
    dirichletOperator (dirichletEigenfunction n) =
      dirichletEigenvalue n • dirichletEigenfunction n := by
  apply Lp.ext
  filter_upwards [dirichletOperator_apply_ae (dirichletEigenfunction n),
    Lp.coeFn_smul (dirichletEigenvalue n) (dirichletEigenfunction n),
    dirichletEigenfunction_coeFn_ae n] with y hy hsm he
  rw [hy, hsm]
  simp only [Pi.smul_apply, he]
  have hi : (∫ t : UnitOpenInterval, dirichletKernel y t * dirichletEigenfunction n t) =
      Real.sqrt 2 * dirichletSolution (fun t => Real.sin (n * Real.pi * t)) y := by
    unfold dirichletSolution
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [dirichletEigenfunction_coeFn_ae n] with t ht
    rw [ht]
    ring
  rw [hi, dirichletSolution_sin n ⟨y.2.1.le, y.2.2.le⟩]
  simp only [smul_eq_mul]
  ring

/-- Every nonzero-frequency sine is a nonzero vector of `L²(0,1)`. -/
theorem dirichletEigenfunction_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    dirichletEigenfunction n ≠ 0 := by
  haveI : (volume : Measure UnitOpenInterval).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  intro hzero
  have he : (fun t : UnitOpenInterval => Real.sqrt 2 * Real.sin (n * Real.pi * t)) =ᵐ[volume]
      fun _ => (0 : ℝ) := by
    filter_upwards [dirichletEigenfunction_coeFn_ae n, Lp.coeFn_zero ℝ 2 volume] with t ht hz
    rw [hzero, hz] at ht
    exact ht.symm
  have heq := MeasureTheory.Measure.eq_of_ae_eq he (by fun_prop) continuous_const
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let t : UnitOpenInterval := ⟨(2 * n : ℝ)⁻¹, by
    constructor
    · positivity
    · exact (inv_lt_one₀ (by positivity)).2 (by linarith)⟩
  have ht : n * Real.pi * (t : ℝ) = Real.pi / 2 := by
    dsimp [t]
    field_simp
  have h := congrFun heq t
  rw [ht, Real.sin_pi_div_two, mul_one] at h
  exact (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) h

/-- Distinct positive integer frequencies have distinct Dirichlet eigenvalues. -/
theorem dirichletEigenvalue_succ_injective : Function.Injective
    (fun n : ℕ => dirichletEigenvalue (n + 1)) := by
  intro m n h
  unfold dirichletEigenvalue at h
  have he := inv_injective h
  have hp : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := Nat.cast_nonneg _
  have he' : ((m + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have he'' := (sq_eq_sq₀ hm hn).mp he'
  exact Nat.succ.inj (Nat.cast_injective he'')

/-- The Dirichlet Green operator has infinitely many independent eigenvectors in its range. -/
theorem hasInfiniteRank_dirichletOperator : HasInfiniteRank
    (dirichletOperator : UnitL2 →ₗ[ℝ] UnitL2) := by
  let T : UnitL2 →ₗ[ℝ] UnitL2 := dirichletOperator
  have hEigNonzero (n : ℕ) : dirichletEigenvalue (n + 1) ≠ 0 := by
    unfold dirichletEigenvalue
    positivity
  have hLI : LinearIndependent ℝ (fun n : ℕ => dirichletEigenfunction (n + 1)) :=
    Module.End.eigenvectors_linearIndependent' T _ dirichletEigenvalue_succ_injective _ fun n =>
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr
          (dirichletOperator_eigenfunction (n + 1)),
        dirichletEigenfunction_ne_zero (by omega)⟩
  let v : ℕ → LinearMap.range T := fun n => ⟨dirichletEigenfunction (n + 1), by
    refine ⟨(dirichletEigenvalue (n + 1))⁻¹ • dirichletEigenfunction (n + 1), ?_⟩
    change dirichletOperator _ = _
    rw [map_smul, dirichletOperator_eigenfunction, smul_smul, inv_mul_cancel₀ (hEigNonzero n),
        one_smul]⟩
  have hLI' : LinearIndependent ℝ v := LinearIndependent.of_comp (LinearMap.range T).subtype hLI
  intro hfinite
  haveI : FiniteDimensional ℝ (LinearMap.range T) := hfinite
  simpa using hLI'.lt_aleph0_of_finiteDimensional

end OperatorRidgelet
