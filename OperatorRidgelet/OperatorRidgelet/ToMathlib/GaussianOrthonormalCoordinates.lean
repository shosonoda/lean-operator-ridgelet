import OperatorRidgelet.ToMathlib.GaussianRealIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Orthonormal Gaussian coordinates

Let `μ` be a centred Gaussian measure on a real inner product space with covariance `Cov`
(characteristic functional `exp(-⟪Cov ξ, ξ⟫/2)`) and let `v : ι → H` be finitely many vectors
whose covariance matrix `⟪Cov (v i), v j⟫` is diagonal with entries `σ i ≥ 0`.  Then the joint
law of the coordinates `⟪v i, ·⟫` is the product `⊗ 𝒩(0, σ i)`
(`MeasureTheory.map_inner_pi_eq_pi_gaussianReal`), so integrals of products factor
(`MeasureTheory.integral_prod_comp_inner`).

The one-dimensional integral entering the Gaussian integral of a quadratic exponential,
`∫ e^{iat - mt²/2} 𝒩(0,1)(dt) = (1+m)^{-1/2} e^{-a²/(2(1+m))}`, is
`ProbabilityTheory.integral_exp_mul_I_sub_sq_gaussianReal_one`.
-/

open MeasureTheory ProbabilityTheory Complex Real
open scoped RealInnerProductSpace NNReal ENNReal

namespace ProbabilityTheory

/-- `∫ e^{i a t - m t²/2} 𝒩(0,1)(dt) = (1+m)^{-1/2} e^{-a²/(2(1+m))}` for `m ≥ 0`. -/
theorem integral_exp_mul_I_sub_sq_gaussianReal_one {m : ℝ} (hm : 0 ≤ m) (a : ℝ) :
    ∫ t : ℝ, Complex.exp (((a * t : ℝ) : ℂ) * Complex.I - ((m * t ^ 2 / 2 : ℝ) : ℂ))
        ∂gaussianReal 0 1 =
      (((Real.sqrt (1 + m))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((a ^ 2 / (2 * (1 + m)) : ℝ) : ℂ)) := by
  have hone : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [integral_gaussianReal_eq_integral_smul hone]
  set b : ℂ := -(((1 + m) / 2 : ℝ) : ℂ) with hb
  have hbre : b.re < 0 := by
    rw [hb, Complex.neg_re, Complex.ofReal_re]
    linarith
  have hfun : ∀ t : ℝ, gaussianPDFReal 0 1 t •
      Complex.exp (((a * t : ℝ) : ℂ) * Complex.I - ((m * t ^ 2 / 2 : ℝ) : ℂ)) =
      (((√(2 * π))⁻¹ : ℝ) : ℂ) *
        Complex.exp (b * (t : ℂ) ^ 2 + ((a : ℂ) * Complex.I) * t + 0) := by
    intro t
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv, hb]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_cexp_quadratic hbre]
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  have h1 : (π : ℂ) / -b = ((2 * π / (1 + m) : ℝ) : ℂ) := by
    rw [hb, neg_neg]
    have : ((1 + m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm1.ne'
    push_cast
    field_simp
  have h2 : ((2 * π / (1 + m) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * π / (1 + m)) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have h3 : (0 : ℂ) - ((a : ℂ) * Complex.I) ^ 2 / (4 * b) =
      -((a ^ 2 / (2 * (1 + m)) : ℝ) : ℂ) := by
    have hI : ((a : ℂ) * Complex.I) ^ 2 = -((a : ℂ) ^ 2) := by
      rw [mul_pow, Complex.I_sq]
      ring
    have hne : ((1 + m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm1.ne'
    rw [hI, hb]
    push_cast
    field_simp
    ring
  rw [h1, h2, h3]
  have h4 : ((√(2 * π))⁻¹ : ℝ) * Real.sqrt (2 * π / (1 + m)) = (Real.sqrt (1 + m))⁻¹ := by
    rw [Real.sqrt_div (by positivity)]
    have hs : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [← mul_assoc, ← Complex.ofReal_mul, h4]

end ProbabilityTheory

namespace MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- The joint law of finitely many Gaussian coordinates whose covariance matrix is diagonal is
the product of the one-dimensional laws. -/
theorem map_inner_pi_eq_pi_gaussianReal {Cov : H →L[ℝ] H} {μ : Measure H}
    [IsProbabilityMeasure μ]
    (hμ : ∀ ξ, charFun μ ξ = Complex.exp (-((⟪Cov ξ, ξ⟫ / 2 : ℝ) : ℂ)))
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → H) (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hvv : ∀ i j, ⟪Cov (v i), v j⟫ = if i = j then σ i else 0) :
    μ.map (fun ξ (i : ι) => ⟪v i, ξ⟫) = Measure.pi fun i => gaussianReal 0 (σ i).toNNReal := by
  have hmeas : Measurable fun (ξ : H) (i : ι) => ⟪v i, ξ⟫ :=
    measurable_pi_lambda _ fun i => (continuous_const.inner continuous_id).measurable
  haveI : IsProbabilityMeasure (μ.map fun (ξ : H) (i : ι) => ⟪v i, ξ⟫) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine (charFun_eq_pi_iff (E := fun _ : ι => ℝ)).1 fun t => ?_
  have hmap : (μ.map fun (ξ : H) (i : ι) => ⟪v i, ξ⟫).map (WithLp.toLp 2) =
      μ.map (fun ξ : H => (WithLp.toLp 2 fun i : ι => ⟪v i, ξ⟫)) := by
    rw [Measure.map_map (by fun_prop) hmeas]
    rfl
  rw [hmap, charFun,
    integral_map (by fun_prop) ((by fun_prop : Continuous fun z : PiLp 2 fun _ : ι => ℝ =>
      Complex.exp (⟪z, t⟫ * Complex.I)).aestronglyMeasurable)]
  have hinner : ∀ ξ : H,
      (⟪(WithLp.toLp 2 fun i : ι => ⟪v i, ξ⟫), t⟫ : ℝ) = ⟪ξ, ∑ i, t i • v i⟫ := by
    intro ξ
    rw [PiLp.inner_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, show ⟪ξ, v i⟫ = ⟪v i, ξ⟫ from real_inner_comm _ _]
    simp [RCLike.inner_apply, mul_comm]
  simp_rw [hinner]
  have := hμ (∑ i, t i • v i)
  rw [charFun] at this
  rw [this]
  have hquad : ⟪Cov (∑ i, t i • v i), ∑ i, t i • v i⟫ = ∑ i, σ i * t i ^ 2 := by
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, real_inner_smul_left, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_right, hvv i i, if_pos rfl]
      ring
    · intro j _ hj
      rw [real_inner_smul_right, hvv i j, if_neg (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hquad]
  have hpi : ∀ i : ι, charFun (gaussianReal 0 (σ i).toNNReal) (t i) =
      Complex.exp (-(((σ i * t i ^ 2 / 2 : ℝ)) : ℂ)) := by
    intro i
    rw [charFun_gaussianReal, Real.coe_toNNReal _ (hσ i)]
    push_cast
    ring_nf
  simp_rw [hpi]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- Integrals of products of functions of orthonormal Gaussian coordinates factor. -/
theorem integral_prod_comp_inner {Cov : H →L[ℝ] H} {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : ∀ ξ, charFun μ ξ = Complex.exp (-((⟪Cov ξ, ξ⟫ / 2 : ℝ) : ℂ)))
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → H) (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hvv : ∀ i j, ⟪Cov (v i), v j⟫ = if i = j then σ i else 0) (g : ι → ℝ → ℂ)
    (hg : ∀ i, Continuous (g i)) :
    ∫ ξ, ∏ i, g i ⟪v i, ξ⟫ ∂μ = ∏ i, ∫ t, g i t ∂gaussianReal 0 (σ i).toNNReal := by
  have hmeas : Measurable fun (ξ : H) (i : ι) => ⟪v i, ξ⟫ :=
    measurable_pi_lambda _ fun i => (continuous_const.inner continuous_id).measurable
  have hcont : Continuous fun z : ι → ℝ => ∏ i, g i (z i) :=
    continuous_finsetProd _ fun i _ => (hg i).comp (continuous_apply i)
  rw [← integral_fintype_prod_eq_prod (fun i => g i)
    (μ := fun i => gaussianReal 0 (σ i).toNNReal),
    ← map_inner_pi_eq_pi_gaussianReal hμ v σ hσ hvv,
    integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]

end MeasureTheory
