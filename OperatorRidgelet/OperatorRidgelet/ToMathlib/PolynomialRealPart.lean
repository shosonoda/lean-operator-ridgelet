import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The real part of a complex polynomial along the real line

A polynomial `p ∈ ℂ[X]` restricted to `ℝ` splits into its real and imaginary parts, and each
part is again a polynomial function: taking the real parts of the coefficients of `p` gives a
`q ∈ ℝ[X]` with `q(t) = Re p(t)` for every real `t`.  This is the elementary fact behind the
statement that a complex polynomial which is real valued on `ℝ` is a real polynomial.
-/

noncomputable section

namespace OperatorRidgelet

open Polynomial

/-- **A complex polynomial has a real part along `ℝ`.**  For `p ∈ ℂ[X]` there is a real
polynomial `q` with `q(t) = Re p(t)` for every `t : ℝ`; its coefficients are the real parts of
the coefficients of `p`. -/
theorem exists_polynomial_eval_eq_re (p : Polynomial ℂ) :
    ∃ q : Polynomial ℝ, ∀ t : ℝ, q.eval t = (p.eval (t : ℂ)).re := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff i).re * Polynomial.X ^ i,
    fun t => ?_⟩
  rw [Polynomial.eval_finsetSum, p.eval_eq_sum_range (x := (t : ℂ)), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpow : ((t : ℂ)) ^ i = ((t ^ i : ℝ) : ℂ) := by push_cast; ring
  rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp

end OperatorRidgelet
