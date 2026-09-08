import OperatorRidgelet.ToMathlib.PolynomialGaussianSchwartz
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The Fourier transform of the Mexican hat, and Gaussian moments

* `ContinuousLinearMap.iteratedDeriv_comp_left`: iterated derivatives commute with a continuous
  linear map.
* `Real.iteratedDeriv_two_gaussian`: `(e^{-t²/2})'' = (t² - 1) e^{-t²/2}`.
* `Real.fourier_gaussian_ofReal`: Mathlib's Fourier transform of `e^{-t²/2}` is
  `√(2π) e^{-(2πξ)²/2}`.
* `Real.fourier_one_sub_sq_mul_gaussian`: the Fourier transform of the Mexican hat
  `(1 - t²) e^{-t²/2}` is `√(2π) (2πξ)² e^{-(2πξ)²/2}`, from the derivative rule.
* `Real.integral_abs_rpow_mul_exp_neg_sq`: the Gaussian moment `∫ |x|^s e^{-x²} dx = Γ((s+1)/2)`.
-/

open MeasureTheory Complex
open scoped FourierTransform Polynomial

/-- Iterated derivatives of a curve commute with a continuous linear map. -/
theorem ContinuousLinearMap.iteratedDeriv_comp_left {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F →L[ℝ] G) {f : ℝ → F}
    {n : ℕ} (hf : ContDiff ℝ n f) (x : ℝ) :
    iteratedDeriv n (g ∘ f) x = g (iteratedDeriv n f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    g.iteratedFDeriv_comp_left hf.contDiffAt le_rfl,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]

namespace Real

/-- The second derivative of the Gaussian: `(e^{-t²/2})'' = (t² - 1) e^{-t²/2}`. -/
theorem iteratedDeriv_two_gaussian (t : ℝ) :
    iteratedDeriv 2 (fun w : ℝ => Real.exp (-w ^ 2 / 2)) t =
      (t ^ 2 - 1) * Real.exp (-t ^ 2 / 2) := by
  have h := iteratedDeriv_polynomial_mul_gaussian 1 2 t
  simp only [Polynomial.eval_one, one_mul] at h
  rw [h]
  congr 1
  simp [gaussianDerivPoly_succ]
  ring

/-- The `n`-th derivative of the complexified Gaussian is a polynomial multiple of it. -/
theorem iteratedDeriv_gaussian_ofReal (n : ℕ) :
    iteratedDeriv n (fun w : ℝ => ((Real.exp (-w ^ 2 / 2) : ℝ) : ℂ)) =
      fun t => ((polynomialGaussianSchwartz (gaussianDerivPoly 1 n) t : ℝ) : ℂ) := by
  funext t
  have h := Complex.ofRealCLM.iteratedDeriv_comp_left
    (f := fun w : ℝ => Real.exp (-w ^ 2 / 2)) (n := n) (by fun_prop) t
  have hfun : (⇑Complex.ofRealCLM ∘ fun w : ℝ => Real.exp (-w ^ 2 / 2)) =
      fun w : ℝ => ((Real.exp (-w ^ 2 / 2) : ℝ) : ℂ) := by
    funext w
    simp
  rw [hfun] at h
  rw [h, Complex.ofRealCLM_apply, polynomialGaussianSchwartz_apply]
  have h1 := iteratedDeriv_polynomial_mul_gaussian 1 n t
  simp only [Polynomial.eval_one, one_mul] at h1
  rw [h1]

/-- Mathlib's Fourier transform of the Gaussian `e^{-t²/2}` is `√(2π) e^{-(2πξ)²/2}`. -/
theorem fourier_gaussian_ofReal (ξ : ℝ) :
    𝓕 (fun t : ℝ => ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) ξ =
      ((Real.sqrt (2 * π) * Real.exp (-(2 * π * ξ) ^ 2 / 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) (-(2 * π * ξ) : ℂ)
  have hfun : (fun v : ℝ => Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) •
      ((Real.exp (-v ^ 2 / 2) : ℝ) : ℂ)) =
      fun x : ℝ =>
        Complex.exp (I * (-(2 * π * ξ) : ℂ) * x) * Complex.exp (-(1 / 2 : ℂ) * x ^ 2) := by
    funext v
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_exp]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [hfun, h]
  have h2 : ((π : ℂ) / (1 / 2)) = ((2 * π : ℝ) : ℂ) := by
    push_cast
    ring
  have h3 : (((2 * π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [Real.sqrt_eq_rpow, Complex.ofReal_mul, h3, Complex.ofReal_exp, h2]
  congr 1
  congr 1
  push_cast
  ring

/-- The Fourier transform of the Mexican hat `(1 - t²) e^{-t²/2}` in Mathlib's convention is
`√(2π) (2πξ)² e^{-(2πξ)²/2}`. -/
theorem fourier_one_sub_sq_mul_gaussian (ξ : ℝ) :
    𝓕 (fun t : ℝ => (((1 - t ^ 2) * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) ξ =
      ((Real.sqrt (2 * π) * (2 * π * ξ) ^ 2 * Real.exp (-(2 * π * ξ) ^ 2 / 2) : ℝ) : ℂ) := by
  set g : ℝ → ℂ := fun t => ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) with hg
  have hcont : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) g := by
    rw [hg]
    exact Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) fun t : ℝ => Real.exp (-t ^ 2 / 2))
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n g) := by
    intro n _
    rw [hg, iteratedDeriv_gaussian_ofReal]
    exact (polynomialGaussianSchwartz _).integrable.ofReal
  have h := Real.fourier_iteratedDeriv (N := 2) (n := 2) hcont hint le_rfl
  have hfun : (fun t : ℝ => (((1 - t ^ 2) * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) =
      -iteratedDeriv 2 g := by
    funext t
    rw [Pi.neg_apply, hg, iteratedDeriv_gaussian_ofReal]
    dsimp only
    rw [polynomialGaussianSchwartz_apply]
    have : (gaussianDerivPoly 1 2).eval t = t ^ 2 - 1 := by
      simp [gaussianDerivPoly_succ]
      ring
    rw [this]
    push_cast
    ring
  have hneg : 𝓕 (-iteratedDeriv 2 g) ξ = -𝓕 (iteratedDeriv 2 g) ξ := by
    simp only [Real.fourier_eq, Pi.neg_apply, smul_neg, integral_neg]
  rw [hfun, hneg, h]
  dsimp only
  rw [hg, fourier_gaussian_ofReal]
  push_cast
  simp only [smul_eq_mul, mul_pow, Complex.I_sq]
  ring

/-- Gaussian moments: `∫ |x|^s e^{-x²} dx = Γ((s+1)/2)` for `s > -1`. -/
theorem integral_abs_rpow_mul_exp_neg_sq {s : ℝ} (hs : -1 < s) :
    ∫ x : ℝ, |x| ^ s * Real.exp (-x ^ 2) = Real.Gamma ((s + 1) / 2) := by
  have h1 := integral_comp_abs (f := fun y : ℝ => y ^ s * Real.exp (-y ^ 2))
  simp only [sq_abs] at h1
  rw [h1, Real.Gamma_eq_integral (by linarith)]
  have h2 := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => Real.exp (-y) * y ^ ((s + 1) / 2 - 1)) two_pos
  rw [← h2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  simp only [smul_eq_mul]
  have e1 : x ^ ((2 : ℝ) - 1) = x := by norm_num
  have e2 : (x ^ (2 : ℝ)) ^ ((s + 1) / 2 - 1) = x ^ s / x := by
    rw [← Real.rpow_mul hx'.le, ← Real.rpow_sub_one hx'.ne']
    congr 1
    ring
  rw [e1, e2, Real.rpow_two]
  field_simp

end Real
