import OperatorRidgelet.ToMathlib.PolynomialCoeffBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Derivatives of `p(x) e^{-c x²/2}` for a complex polynomial `p`

For `p : ℂ[X]` and `c : ℂ`, the function `x ↦ p(x) e^{-c x²/2}` on `ℝ` is smooth, and its
`n`-th derivative is `p_n(x) e^{-c x²/2}` with `p_n = (gaussianDerivOp c)^[n] p`,
`gaussianDerivOp c p = p' - c X p` (`Polynomial.iteratedDeriv_eval_ofReal_mul_cexp`).  Together
with the coefficient bounds of `OperatorRidgelet.ToMathlib.PolynomialCoeffBound` this gives
explicit bounds on all derivatives (`Polynomial.norm_iteratedDeriv_eval_ofReal_mul_cexp_le`).
-/

open scoped Polynomial

namespace Polynomial

/-- The derivative of `p(z) e^{-c z²/2}` on `ℂ` is `(p' - c X p)(z) e^{-c z²/2}`. -/
theorem hasDerivAt_eval_mul_cexp (c : ℂ) (p : ℂ[X]) (z : ℂ) :
    HasDerivAt (fun w : ℂ => p.eval w * Complex.exp (-(c * w ^ 2 / 2)))
      ((gaussianDerivOp c p).eval z * Complex.exp (-(c * z ^ 2 / 2))) z := by
  have hz : HasDerivAt (fun w : ℂ => -(c * w ^ 2 / 2)) (-(c * (2 * z) / 2)) z := by
    have h := (hasDerivAt_pow 2 z).const_mul (-(c / 2))
    have h' : HasDerivAt (fun w : ℂ => -(c * w ^ 2 / 2)) (-(c / 2) * ((2 : ℕ) * z ^ (2 - 1))) z :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by ring)
    refine h'.congr_deriv ?_
    norm_num
    ring
  refine ((Polynomial.hasDerivAt p z).mul hz.cexp).congr_deriv ?_
  simp only [gaussianDerivOp, eval_sub, eval_mul, eval_C, eval_X]
  ring

/-- The derivative of `x ↦ p(x) e^{-c x²/2}` on `ℝ` is `(p' - c X p)(x) e^{-c x²/2}`. -/
theorem hasDerivAt_eval_ofReal_mul_cexp (c : ℂ) (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval (y : ℂ) * Complex.exp (-(c * (y : ℂ) ^ 2 / 2)))
      ((gaussianDerivOp c p).eval (x : ℂ) * Complex.exp (-(c * (x : ℂ) ^ 2 / 2))) x :=
  (hasDerivAt_eval_mul_cexp c p x).comp_ofReal

/-- The `n`-th derivative of `x ↦ p(x) e^{-c x²/2}` on `ℝ` is
`((gaussianDerivOp c)^[n] p)(x) e^{-c x²/2}`. -/
theorem iteratedDeriv_eval_ofReal_mul_cexp (c : ℂ) (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => p.eval (y : ℂ) * Complex.exp (-(c * (y : ℂ) ^ 2 / 2))) =
      fun y : ℝ => ((gaussianDerivOp c)^[n] p).eval (y : ℂ) *
        Complex.exp (-(c * (y : ℂ) ^ 2 / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext y
    exact (hasDerivAt_eval_ofReal_mul_cexp c _ y).deriv

/-- `x ↦ p(x)` is smooth on `ℝ` for a complex polynomial `p`. -/
theorem contDiff_eval_ofReal (p : ℂ[X]) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y : ℝ => p.eval (y : ℂ) := by
  have h : ContDiff ℂ n fun w : ℂ => p.eval w := by
    have := contDiff_aeval (𝕜 := ℂ) p n
    simpa only [coe_aeval_eq_eval] using this
  exact (h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- `x ↦ p(x) e^{-c x²/2}` is smooth on `ℝ`. -/
theorem contDiff_eval_ofReal_mul_cexp (c : ℂ) (p : ℂ[X]) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y : ℝ => p.eval (y : ℂ) * Complex.exp (-(c * (y : ℂ) ^ 2 / 2)) := by
  have hin : ContDiff ℝ n fun y : ℝ => -(c * (y : ℂ) ^ 2 / 2) :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.pow 2)).div_const 2).neg
  exact (contDiff_eval_ofReal p).mul (Complex.contDiff_exp.comp hin)

/-- Bound on the `n`-th derivative of `x ↦ p(x) e^{-c x²/2}` for real `c`: if `natDegree p ≤ d`
and `‖coeff p j‖ ≤ M` for all `j`, then
`‖dⁿ/dxⁿ (p(x) e^{-c x²/2})‖ ≤ (d + n + 1) (d + n + |c|)^n M (1 + |x|)^(d + n) e^{-c x²/2}`. -/
theorem norm_iteratedDeriv_eval_ofReal_mul_cexp_le (c : ℝ) {p : ℂ[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) {M : ℝ} (hM : ∀ j, ‖p.coeff j‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n
        (fun y : ℝ => p.eval (y : ℂ) * Complex.exp (-((c : ℂ) * (y : ℂ) ^ 2 / 2))) x‖ ≤
      (d + n + 1) * ((d + n + |c|) ^ n * M) * (1 + |x|) ^ (d + n) *
        Real.exp (-(c * x ^ 2 / 2)) := by
  rw [iteratedDeriv_eval_ofReal_mul_cexp, norm_mul]
  have hexp : ‖Complex.exp (-((c : ℂ) * (x : ℂ) ^ 2 / 2))‖ = Real.exp (-(c * x ^ 2 / 2)) := by
    rw [← Complex.norm_exp_ofReal]
    congr 2
    push_cast
    ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h := norm_eval_gaussianDerivOp_iterate_le (c : ℂ) hd hM n (x : ℂ)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

end Polynomial
