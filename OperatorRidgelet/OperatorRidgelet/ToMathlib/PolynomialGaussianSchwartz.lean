import LeanRidgelet.ToMathlib.GaussianSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial multiples of the Gaussian as real Schwartz functions

For a real polynomial `p`, the function `z ↦ p(z) e^{-z²/2}` is a real Schwartz function
`Real.polynomialGaussianSchwartz p`.  Its `n`-th derivative is `p_n(z) e^{-z²/2}` with
`p_0 = p` and `p_{n+1} = p_n' - X p_n` (`Real.gaussianDerivPoly`), and the Schwartz estimates
follow from the polynomial bounds of `LeanRidgelet.ToMathlib.GaussianSchwartz`.
-/

open scoped Polynomial

/-- Polynomials are smooth. -/
theorem Polynomial.contDiff_eval {n : WithTop ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n fun z : ℝ => p.eval z := by
  induction p using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [Polynomial.eval_add]
    exact hq.add hr
  | monomial k c =>
    simp only [Polynomial.eval_monomial]
    exact contDiff_const.mul (contDiff_id.pow k)

namespace Real

/-- The polynomial `p_n` with `dⁿ/dzⁿ (p(z) e^{-z²/2}) = p_n(z) e^{-z²/2}`: `p_0 = p` and
`p_{n+1} = p_n' - X p_n`. -/
noncomputable def gaussianDerivPoly (p : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | n + 1 => Polynomial.derivative (gaussianDerivPoly p n) - Polynomial.X * gaussianDerivPoly p n

/-- The zeroth Gaussian derivative polynomial is the original polynomial. -/
@[simp]
theorem gaussianDerivPoly_zero (p : ℝ[X]) : gaussianDerivPoly p 0 = p := rfl

/-- Differentiation of a polynomial times a Gaussian gives this derivative-polynomial recurrence. -/
theorem gaussianDerivPoly_succ (p : ℝ[X]) (n : ℕ) :
    gaussianDerivPoly p (n + 1) =
      Polynomial.derivative (gaussianDerivPoly p n) - Polynomial.X * gaussianDerivPoly p n := rfl

/-- The derivative of `p(z) e^{-z²/2}` is `(p' - X p)(z) e^{-z²/2}`. -/
theorem hasDerivAt_polynomial_mul_gaussian (p : ℝ[X]) (z : ℝ) :
    HasDerivAt (fun w : ℝ => p.eval w * Real.exp (-w ^ 2 / 2))
      ((Polynomial.derivative p - Polynomial.X * p).eval z * Real.exp (-z ^ 2 / 2)) z := by
  have hexp : HasDerivAt (fun w : ℝ => Real.exp (-w ^ 2 / 2)) (Real.exp (-z ^ 2 / 2) * (-z)) z := by
    have h3 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-z) z := by
      have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
        simpa using hasDerivAt_pow 2 z
      have h6 := hsq.neg.div_const 2
      have h7 : -(2 * z) / 2 = -z := by ring
      rwa [h7] at h6
    exact h3.exp
  have h := (Polynomial.hasDerivAt p z).mul hexp
  have heq : (Polynomial.derivative p).eval z * Real.exp (-z ^ 2 / 2)
        + p.eval z * (Real.exp (-z ^ 2 / 2) * (-z))
      = (Polynomial.derivative p - Polynomial.X * p).eval z * Real.exp (-z ^ 2 / 2) := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  rwa [heq] at h

/-- The `n`-th derivative of `p(z) e^{-z²/2}` is `p_n(z) e^{-z²/2}`. -/
theorem iteratedDeriv_polynomial_mul_gaussian (p : ℝ[X]) (n : ℕ) (z : ℝ) :
    iteratedDeriv n (fun w : ℝ => p.eval w * Real.exp (-w ^ 2 / 2)) z =
      (gaussianDerivPoly p n).eval z * Real.exp (-z ^ 2 / 2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun w : ℝ => p.eval w * Real.exp (-w ^ 2 / 2)) =
        fun w => (gaussianDerivPoly p n).eval w * Real.exp (-w ^ 2 / 2) := funext ih
    rw [hfun, gaussianDerivPoly_succ]
    exact (hasDerivAt_polynomial_mul_gaussian _ z).deriv

/-- The function `z ↦ p(z) e^{-z²/2}` as a real Schwartz function. -/
noncomputable def polynomialGaussianSchwartz (p : ℝ[X]) : SchwartzMap ℝ ℝ where
  toFun z := p.eval z * Real.exp (-z ^ 2 / 2)
  smooth' := (Polynomial.contDiff_eval p).mul (by fun_prop)
  decay' := by
    intro k n
    obtain ⟨C, d, hC, hbound⟩ := exists_bound_polynomial_eval (gaussianDerivPoly p n)
    refine ⟨C * (2 ^ (k + d) * (1 + 2 ^ (k + d) * ((k + d).factorial : ℝ))), fun z => ?_⟩
    have hexp0 : (0 : ℝ) < Real.exp (-z ^ 2 / 2) := Real.exp_pos _
    have hnorm : ‖iteratedFDeriv ℝ n (fun w : ℝ => p.eval w * Real.exp (-w ^ 2 / 2)) z‖
        = |(gaussianDerivPoly p n).eval z| * Real.exp (-z ^ 2 / 2) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_polynomial_mul_gaussian,
        Real.norm_eq_abs, abs_mul, abs_of_pos hexp0]
    rw [hnorm, Real.norm_eq_abs]
    have hpoly : |z| ^ k * |(gaussianDerivPoly p n).eval z| ≤ C * (1 + |z|) ^ (k + d) := by
      have h1 : |z| ^ k ≤ (1 + |z|) ^ k :=
        pow_le_pow_left₀ (abs_nonneg z) (by linarith [abs_nonneg z]) k
      calc |z| ^ k * |(gaussianDerivPoly p n).eval z| ≤ (1 + |z|) ^ k * (C * (1 + |z|) ^ d) :=
            mul_le_mul h1 (hbound z) (abs_nonneg _) (by positivity)
        _ = C * (1 + |z|) ^ (k + d) := by rw [pow_add]; ring
    have hgauss := one_add_abs_pow_mul_exp_neg_sq_div_two_le (k + d) z
    calc |z| ^ k * (|(gaussianDerivPoly p n).eval z| * Real.exp (-z ^ 2 / 2))
        = (|z| ^ k * |(gaussianDerivPoly p n).eval z|) * Real.exp (-z ^ 2 / 2) := by ring
      _ ≤ (C * (1 + |z|) ^ (k + d)) * Real.exp (-z ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hpoly hexp0.le
      _ = C * ((1 + |z|) ^ (k + d) * Real.exp (-z ^ 2 / 2)) := by ring
      _ ≤ C * (2 ^ (k + d) * (1 + 2 ^ (k + d) * ((k + d).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hgauss hC

/-- Evaluation of the Schwartz function represented by a polynomial times a Gaussian. -/
@[simp]
theorem polynomialGaussianSchwartz_apply (p : ℝ[X]) (z : ℝ) :
    polynomialGaussianSchwartz p z = p.eval z * Real.exp (-z ^ 2 / 2) := rfl

end Real
