import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integrals on the line

Closed forms of a few integrals against the centred one-dimensional Gaussian `gaussianReal 0 v`
and against Lebesgue measure.

* `integral_Ioi_mul_exp_neg_mul_sq`: `∫_0^∞ t e^{-b t²} dt = 1/(2b)`.
* `tendsto_pow_mul_exp_neg_sq_half_atTop`, `tendsto_pow_mul_exp_neg_sq_half_atBot`:
  `tⁿ e^{-t²/2} → 0` at `±∞`.
* `integral_max_sub_mul_gaussian_deriv2`: the absolute hinge representation
  `∫ (u - b)_+ (b² - 1) e^{-b²/2} db = e^{-u²/2}` of the Gaussian, by integration by parts on
  `(-∞, u]`.
* `ProbabilityTheory.integral_max_zero_gaussianReal`: `∫ max(t, 0) 𝒩(0,v)(dt) = √(v/(2π))`.
* `ProbabilityTheory.integral_exp_neg_sq_half_gaussianReal`:
  `∫ e^{-t²/2} 𝒩(0,v)(dt) = (1 + v)^{-1/2}`.
* `ProbabilityTheory.integral_exp_neg_sq_half_mul_exp_neg_mul_I_gaussianReal`:
  `∫ e^{-t²/2} e^{-ikt} 𝒩(0,v)(dt) = (1 + v)^{-1/2} exp(-k² v / (2 (1 + v)))`.
-/

open MeasureTheory Filter Topology Real
open scoped NNReal

/-- `∫_0^∞ t e^{-b t²} dt = 1/(2b)` for `b > 0`. -/
theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-b * t ^ 2) = (2 * b)⁻¹ := by
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2))
        (t * Real.exp (-b * t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -b * t ^ 2) (-b * (2 * t)) t := by
      refine ((hasDerivAt_pow 2 t).const_mul (-b)).congr_deriv ?_
      norm_num
    refine ((Real.hasDerivAt_exp _).comp t h1).const_mul (-(2 * b)⁻¹) |>.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun t : ℝ => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -b * t ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop hb
      have h' := tendsto_neg_atTop_atBot.comp this
      refine h'.congr fun t => ?_
      simp only [Function.comp_apply]
      ring
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (-(2 * b)⁻¹)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_mul_exp_neg_mul_sq hb).integrableOn hlim]
  simp

/-- `tⁿ e^{-t²/2} → 0` as `t → +∞`. -/
theorem tendsto_pow_mul_exp_neg_sq_half_atTop (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -(1 / 2 * x)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num))
    refine (Real.tendsto_exp_atBot.comp h1).congr fun x => ?_
    simp only [Function.comp_apply, neg_mul]
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (b := 1 / 2) (by norm_num)
    (n : ℝ)).tendsto_zero_of_tendsto hexp
  refine h.congr fun t => ?_
  rw [Real.rpow_natCast]
  congr 2
  ring

/-- `tⁿ e^{-t²/2} → 0` as `t → -∞`. -/
theorem tendsto_pow_mul_exp_neg_sq_half_atBot (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-t ^ 2 / 2)) atBot (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_sq_half_atTop n).comp tendsto_neg_atBot_atTop).const_mul
    ((-1 : ℝ) ^ n)
  rw [mul_zero] at h
  refine h.congr fun t => ?_
  show (-1 : ℝ) ^ n * ((-t) ^ n * Real.exp (-(-t) ^ 2 / 2)) = t ^ n * Real.exp (-t ^ 2 / 2)
  rw [neg_sq, ← mul_assoc, ← mul_pow]
  simp

/-- The absolute hinge representation of the Gaussian:
`∫ (u - b)_+ (b² - 1) e^{-b²/2} db = e^{-u²/2}`. -/
theorem integral_max_sub_mul_gaussian_deriv2 (u : ℝ) :
    ∫ b : ℝ, max (u - b) 0 * ((b ^ 2 - 1) * Real.exp (-b ^ 2 / 2)) = Real.exp (-u ^ 2 / 2) := by
  set F : ℝ → ℝ := fun b => (u - b) * (-b * Real.exp (-b ^ 2 / 2)) + Real.exp (-b ^ 2 / 2)
    with hF
  have hgauss : ∀ b : ℝ, HasDerivAt (fun b : ℝ => Real.exp (-b ^ 2 / 2))
      (-b * Real.exp (-b ^ 2 / 2)) b := by
    intro b
    have h1 : HasDerivAt (fun b : ℝ => -b ^ 2 / 2) (-b) b := by
      refine ((hasDerivAt_pow 2 b).neg.div_const 2).congr_deriv ?_
      norm_num
      ring
    exact ((Real.hasDerivAt_exp _).comp b h1).congr_deriv (by ring)
  have hderiv : ∀ b : ℝ, HasDerivAt F ((u - b) * ((b ^ 2 - 1) * Real.exp (-b ^ 2 / 2))) b := by
    intro b
    have h1 := (hasDerivAt_id' b).neg.mul (hgauss b)
    have h2 := ((hasDerivAt_id' b).const_sub u).mul h1
    refine (h2.add (hgauss b)).congr_deriv ?_
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring
  have hrestrict : ∫ b : ℝ, max (u - b) 0 * ((b ^ 2 - 1) * Real.exp (-b ^ 2 / 2)) =
      ∫ b in Set.Iic u, (u - b) * ((b ^ 2 - 1) * Real.exp (-b ^ 2 / 2)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Iic u)]
    · exact setIntegral_congr_fun measurableSet_Iic fun b hb => by
        rw [max_eq_left (sub_nonneg.mpr hb)]
    · intro b hb
      rw [max_eq_right (sub_nonpos.mpr (le_of_lt (not_le.mp hb))), zero_mul]
  have hn : ∀ n : ℕ, Integrable fun b : ℝ => b ^ n * Real.exp (-b ^ 2 / 2) := by
    intro n
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (n : ℝ))
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    refine h.congr (Eventually.of_forall fun b => ?_)
    simp only [Real.rpow_natCast]
    congr 2
    ring
  have hint : Integrable fun b : ℝ => (u - b) * ((b ^ 2 - 1) * Real.exp (-b ^ 2 / 2)) := by
    have h := ((((hn 2).const_mul u).sub (hn 3)).sub ((hn 0).const_mul u)).add (hn 1)
    refine h.congr (Eventually.of_forall fun b => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, pow_zero, pow_one]
    ring
  have hlim : Tendsto F atBot (𝓝 0) := by
    have h := (((tendsto_pow_mul_exp_neg_sq_half_atBot 1).const_mul (-u)).add
      (tendsto_pow_mul_exp_neg_sq_half_atBot 2)).add (tendsto_pow_mul_exp_neg_sq_half_atBot 0)
    simp only [mul_zero, add_zero] at h
    refine h.congr fun b => ?_
    simp only [hF, pow_zero, pow_one]
    ring
  rw [hrestrict, integral_Iic_of_hasDerivAt_of_tendsto' (fun b _ => hderiv b)
    hint.integrableOn hlim]
  simp [hF]

namespace ProbabilityTheory

/-- The Gaussian expectation of the positive part: `∫ max(t, 0) 𝒩(0,v)(dt) = √(v / (2π))`. -/
theorem integral_max_zero_gaussianReal (v : ℝ≥0) :
    ∫ t, max t 0 ∂gaussianReal 0 v = Real.sqrt (v / (2 * π)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [gaussianPDFReal, sub_zero, smul_eq_mul]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne (NNReal.coe_nonneg v) (by exact_mod_cast hv.symm)
  have hb : 0 < (2 * (v : ℝ))⁻¹ := by positivity
  have hrestrict : ∫ t, (√(2 * π * v))⁻¹ * rexp (-t ^ 2 / (2 * v)) * max t 0 =
      ∫ t in Set.Ioi (0 : ℝ), (√(2 * π * v))⁻¹ * (t * rexp (-(2 * (v : ℝ))⁻¹ * t ^ 2)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi 0)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [max_eq_left (le_of_lt ht)]
      have : -t ^ 2 / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * t ^ 2 := by ring
      rw [this]
      ring
    · intro t ht
      rw [max_eq_right (not_lt.mp ht), mul_zero]
  rw [hrestrict, integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb]
  have h1 : (2 * (2 * (v : ℝ))⁻¹)⁻¹ = v := by field_simp
  rw [h1, Real.sqrt_div (NNReal.coe_nonneg v), Real.sqrt_mul (by positivity)]
  have hsv : 0 < √(v : ℝ) := Real.sqrt_pos.mpr hv'
  have h2 : (v : ℝ) = √(v : ℝ) * √(v : ℝ) := (Real.mul_self_sqrt hv'.le).symm
  set sv := √(v : ℝ) with hsv_def
  rw [h2]
  have hs2 : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `∫ e^{-t²/2} 𝒩(0,v)(dt) = (1 + v)^{-1/2}`. -/
theorem integral_exp_neg_sq_half_gaussianReal (v : ℝ≥0) :
    ∫ t, Real.exp (-t ^ 2 / 2) ∂gaussianReal 0 v = (Real.sqrt (1 + v))⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [gaussianPDFReal, sub_zero, smul_eq_mul]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne (NNReal.coe_nonneg v) (by exact_mod_cast hv.symm)
  have hfun : ∀ t : ℝ, (√(2 * π * v))⁻¹ * rexp (-t ^ 2 / (2 * v)) * rexp (-t ^ 2 / 2) =
      (√(2 * π * v))⁻¹ * rexp (-((1 + v) / (2 * v)) * t ^ 2) := by
    intro t
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_gaussian]
  have h1 : π / ((1 + (v : ℝ)) / (2 * v)) = 2 * π * v / (1 + v) := by
    field_simp
  rw [h1, Real.sqrt_div (by positivity)]
  have hs : 0 < √(2 * π * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The tilted Gaussian Fourier integral:
`∫ e^{-t²/2} e^{-ikt} 𝒩(0,v)(dt) = (1 + v)^{-1/2} exp(-k² v / (2 (1 + v)))`. -/
theorem integral_exp_neg_sq_half_mul_exp_neg_mul_I_gaussianReal (v : ℝ≥0) (k : ℝ) :
    ∫ t, Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-((k * t : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 v =
      (((Real.sqrt (1 + v))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((k ^ 2 * v / (2 * (1 + v)) : ℝ) : ℂ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne (NNReal.coe_nonneg v) (by exact_mod_cast hv.symm)
  have hvc : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv'.ne'
  have h1v : (1 + ((v : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + v := by positivity
    exact_mod_cast this.ne'
  set b : ℂ := -(((1 + v) / (2 * v) : ℝ) : ℂ) with hb
  have hbre : b.re < 0 := by
    rw [hb, Complex.neg_re, Complex.ofReal_re]
    have : 0 < (1 + (v : ℝ)) / (2 * v) := by positivity
    linarith
  have hfun : ∀ t : ℝ, gaussianPDFReal 0 v t •
      (Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-((k * t : ℝ) : ℂ) * Complex.I)) =
      (((√(2 * π * v))⁻¹ : ℝ) : ℂ) *
        Complex.exp (b * (t : ℂ) ^ 2 + (-(k : ℂ) * Complex.I) * t + 0) := by
    intro t
    simp only [gaussianPDFReal, sub_zero, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_exp, hb]
    rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_cexp_quadratic hbre]
  have h1 : (π : ℂ) / -b = ((2 * π * v / (1 + v) : ℝ) : ℂ) := by
    rw [hb, neg_neg]
    push_cast
    field_simp
  have h2 : ((2 * π * v / (1 + v) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * π * v / (1 + v)) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have h3 : (0 : ℂ) - (-(k : ℂ) * Complex.I) ^ 2 / (4 * b) =
      -((k ^ 2 * v / (2 * (1 + v)) : ℝ) : ℂ) := by
    have hI : (-(k : ℂ) * Complex.I) ^ 2 = -((k : ℂ) ^ 2) := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hI, hb]
    push_cast
    field_simp
    ring
  rw [h1, h2, h3]
  have h4 : ((√(2 * π * v))⁻¹ : ℝ) * Real.sqrt (2 * π * v / (1 + v)) =
      (Real.sqrt (1 + v))⁻¹ := by
    rw [Real.sqrt_div (by positivity)]
    have hs : 0 < √(2 * π * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [← mul_assoc, ← Complex.ofReal_mul, h4]

end ProbabilityTheory
