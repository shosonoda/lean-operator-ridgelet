import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.CharFun
import OperatorRidgelet.ToMathlib.GaussianRealIntegral

/-!
# Tilting and shearing one-dimensional Gaussians

* `ProbabilityTheory.integral_exp_neg_sq_half_smul_gaussianReal`: the Gaussian tilt
  `e^{-z²/2} 𝒩(0,v)(dz) = (1+v)^{-1/2} 𝒩(0, v/(1+v))(dz)`, as an identity of Bochner integrals;
* `ProbabilityTheory.map_mul_add_prod_gaussianReal`: the law of `k z + u` under
  `𝒩(0,v₁) ⊗ 𝒩(0,v₂)` is `𝒩(0, k² v₁ + v₂)`;
* `ProbabilityTheory.integral_comp_add_gaussianReal`: `∫ h(c + t) 𝒩(0,v)(dt) = ∫ h(c - t) 𝒩(0,v)(dt)`.
-/

open MeasureTheory Real
open scoped NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Gaussian tilt: `∫ e^{-z²/2} h(z) 𝒩(0,v)(dz) = (1+v)^{-1/2} ∫ h 𝒩(0, v/(1+v))`. -/
theorem integral_exp_neg_sq_half_smul_gaussianReal {v : ℝ} (hv : 0 ≤ v) (h : ℝ → E) :
    ∫ z, Real.exp (-z ^ 2 / 2) • h z ∂gaussianReal 0 v.toNNReal =
      (Real.sqrt (1 + v))⁻¹ • ∫ z, h z ∂gaussianReal 0 (v / (1 + v)).toNNReal := by
  rcases hv.lt_or_eq with hv | hv0
  · have hv' : v.toNNReal ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact hv
    have hw : 0 < v / (1 + v) := by positivity
    have hw' : (v / (1 + v)).toNNReal ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact hw
    rw [integral_gaussianReal_eq_integral_smul hv', integral_gaussianReal_eq_integral_smul hw',
      ← integral_smul]
    congr 1
    funext z
    rw [smul_smul, smul_smul]
    congr 1
    have h1v : 0 < 1 + v := by linarith
    have hsq : Real.sqrt (2 * π * v) = Real.sqrt (1 + v) * Real.sqrt (2 * π * (v / (1 + v))) := by
      rw [← Real.sqrt_mul h1v.le]
      congr 1
      field_simp
    have hexp : Real.exp (-z ^ 2 / (2 * v)) * Real.exp (-z ^ 2 / 2) =
        Real.exp (-z ^ 2 / (2 * (v / (1 + v)))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    unfold gaussianPDFReal
    rw [Real.coe_toNNReal _ hv.le, Real.coe_toNNReal _ hw.le, sub_zero, hsq, mul_inv]
    calc (Real.sqrt (1 + v))⁻¹ * (Real.sqrt (2 * π * (v / (1 + v))))⁻¹ *
          Real.exp (-z ^ 2 / (2 * v)) * Real.exp (-z ^ 2 / 2)
        = (Real.sqrt (1 + v))⁻¹ * ((Real.sqrt (2 * π * (v / (1 + v))))⁻¹ *
            (Real.exp (-z ^ 2 / (2 * v)) * Real.exp (-z ^ 2 / 2))) := by ring
      _ = _ := by rw [hexp]
  · subst hv0
    simp only [Real.toNNReal_zero, gaussianReal_zero_var, zero_div, add_zero, Real.sqrt_one,
      inv_one, one_smul]
    rw [integral_dirac, integral_dirac]
    simp

/-- The law of `k z + u` under `𝒩(0,v₁) ⊗ 𝒩(0,v₂)` is `𝒩(0, k² v₁ + v₂)`. -/
theorem map_mul_add_prod_gaussianReal {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (k : ℝ) :
    ((gaussianReal 0 v₁.toNNReal).prod (gaussianReal 0 v₂.toNNReal)).map
        (fun p : ℝ × ℝ => k * p.1 + p.2) =
      gaussianReal 0 (k ^ 2 * v₁ + v₂).toNNReal := by
  have hmeas : Measurable fun p : ℝ × ℝ => k * p.1 + p.2 := by fun_prop
  haveI : IsProbabilityMeasure (((gaussianReal 0 v₁.toNNReal).prod
      (gaussianReal 0 v₂.toNNReal)).map (fun p : ℝ × ℝ => k * p.1 + p.2)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_charFun (funext fun s => ?_)
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop)]
  have hfun : ∀ p : ℝ × ℝ, Complex.exp ((s : ℂ) * ((k * p.1 + p.2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((s * k : ℝ) : ℂ) * (p.1 : ℂ) * Complex.I) *
        Complex.exp ((s : ℂ) * (p.2 : ℂ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hfun]
  have hprod : ∫ p : ℝ × ℝ, Complex.exp (((s * k : ℝ) : ℂ) * (p.1 : ℂ) * Complex.I) *
        Complex.exp ((s : ℂ) * (p.2 : ℂ) * Complex.I)
        ∂((gaussianReal 0 v₁.toNNReal).prod (gaussianReal 0 v₂.toNNReal)) =
      (∫ a : ℝ, Complex.exp (((s * k : ℝ) : ℂ) * (a : ℂ) * Complex.I)
          ∂gaussianReal 0 v₁.toNNReal) *
        ∫ b : ℝ, Complex.exp ((s : ℂ) * (b : ℂ) * Complex.I) ∂gaussianReal 0 v₂.toNNReal :=
    integral_prod_mul (fun a : ℝ => Complex.exp (((s * k : ℝ) : ℂ) * (a : ℂ) * Complex.I))
      (fun b : ℝ => Complex.exp ((s : ℂ) * (b : ℂ) * Complex.I))
  rw [hprod, ← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal,
    charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add, Real.coe_toNNReal _ hv₁,
    Real.coe_toNNReal _ hv₂, Real.coe_toNNReal _ (by positivity)]
  congr 1
  push_cast
  ring

omit [CompleteSpace E] in
/-- `∫ h(c + t) 𝒩(0,v)(dt) = ∫ h(c - t) 𝒩(0,v)(dt)` for continuous `h`. -/
theorem integral_comp_add_gaussianReal (v : ℝ≥0) {h : ℝ → E} (hh : Continuous h) (c : ℝ) :
    ∫ t, h (c + t) ∂gaussianReal 0 v = ∫ t, h (c - t) ∂gaussianReal 0 v := by
  have hmap : (gaussianReal 0 v).map (fun t => -t) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have hm : AEStronglyMeasurable (fun t => h (c + t)) ((gaussianReal 0 v).map fun t => -t) :=
    (hh.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  conv_lhs => rw [← hmap]
  rw [integral_map measurable_neg.aemeasurable hm]
  simp_rw [sub_eq_add_neg]

end ProbabilityTheory
