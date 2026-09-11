import OperatorRidgelet.ToMathlib.PolynomialGaussianSchwartz
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The probabilists' Hermite polynomials against the standard Gaussian

`Polynomial.hermiteR n` is `Polynomial.hermite n` with real coefficients.  Against the standard
Gaussian `γ = 𝒩(0,1)` the family is orthogonal with squared norms `n!`, and its exponential
moments are the powers of `z`:

* `integral_hermiteR_mul_cexp`: `∫ He_n(y) e^{zy} γ(dy) = z^n e^{z²/2}` for every complex `z`;
* `integral_hermiteR_mul_hermiteR`: `∫ He_m He_n dγ = n!` if `m = n` and `0` otherwise.

Both come from one Gaussian integration by parts (`integral_gaussianReal_mul_eval_mul_cexp`,
`∫ y P(y) e^{zy} dγ = ∫ (P'(y) + z P(y)) e^{zy} dγ`), which is the statement that the integral
of the derivative of `P(y) e^{zy - y²/2}` vanishes.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Polynomial Real

noncomputable section

namespace Polynomial

/-! ### The Hermite polynomials with real coefficients -/

/-- The probabilists' Hermite polynomials with real coefficients. -/
def hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

@[simp]
theorem hermiteR_zero : hermiteR 0 = 1 := by
  simp [hermiteR]

theorem hermiteR_succ (n : ℕ) :
    hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := by
  simp [hermiteR, Polynomial.map_mul, Polynomial.map_sub, derivative_map]

theorem monic_hermiteR (n : ℕ) : (hermiteR n).Monic :=
  (hermite_monic n).map _

@[simp]
theorem natDegree_hermiteR (n : ℕ) : (hermiteR n).natDegree = n := by
  rw [hermiteR, (hermite_monic n).natDegree_map, natDegree_hermite]

/-- `aeval` of the integral Hermite polynomial at a real point is the evaluation of
`hermiteR`. -/
theorem aeval_hermite_eq_eval_hermiteR (n : ℕ) (r : ℝ) :
    (aeval r (hermite n) : ℝ) = (hermiteR n).eval r := by
  rw [hermiteR, eval_map, aeval_def, algebraMap_int_eq]

/-- The `n`-th derivative of `He_n` is the constant `n!`. -/
theorem iterate_derivative_hermiteR_self (n : ℕ) :
    derivative^[n] (hermiteR n) = C (n.factorial : ℝ) := by
  have hdeg : (derivative^[n] (hermiteR n)).natDegree = 0 := by
    have := natDegree_iterate_derivative (hermiteR n) n
    simp only [natDegree_hermiteR, Nat.sub_self, Nat.le_zero] at this
    exact this
  have hc : (derivative^[n] (hermiteR n)).coeff 0 = (n.factorial : ℝ) := by
    have h1 : (hermiteR n).coeff n = 1 := by
      have h := (monic_hermiteR n).coeff_natDegree
      rwa [natDegree_hermiteR] at h
    rw [coeff_iterate_derivative]
    simp [h1, Nat.descFactorial_self]
  calc derivative^[n] (hermiteR n)
      = C ((derivative^[n] (hermiteR n)).coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    _ = C (n.factorial : ℝ) := by rw [hc]

end Polynomial

namespace ProbabilityTheory

open Polynomial

/-! ### Integrability of `P(y) e^{zy}` against the Gaussian -/

/-- `|P(y)| e^{ry - y²/2}` is Lebesgue integrable. -/
theorem integrable_abs_eval_mul_exp_sub_sq (P : ℝ[X]) (r : ℝ) :
    Integrable fun y : ℝ => |P.eval y| * Real.exp (r * y - y ^ 2 / 2) := by
  set S : ℝ[X] := P.comp (X + C r) with hS
  have hbase : Integrable fun u : ℝ =>
      Real.exp (r ^ 2 / 2) * |(Real.polynomialGaussianSchwartz S) u| :=
    ((Real.polynomialGaussianSchwartz S).integrable (μ := volume)).norm.const_mul _
  have hshift := hbase.comp_sub_right r
  refine hshift.congr ?_
  filter_upwards with y
  have hev : S.eval (y - r) = P.eval y := by
    simp [hS, eval_comp, sub_add_cancel]
  simp only [Real.polynomialGaussianSchwartz_apply, hev, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [show r * y - y ^ 2 / 2 = r ^ 2 / 2 + -(y - r) ^ 2 / 2 by ring, Real.exp_add]
  ring

/-- `P(y) e^{zy - y²/2}` is Lebesgue integrable. -/
theorem integrable_eval_mul_cexp_sub_sq (P : ℝ[X]) (z : ℂ) :
    Integrable fun y : ℝ => ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y - (y : ℂ) ^ 2 / 2) := by
  refine Integrable.mono' (integrable_abs_eval_mul_exp_sub_sq P z.re) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with y
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (z * (y : ℂ) - (y : ℂ) ^ 2 / 2).re = z.re * y - y ^ 2 / 2 := by
      rw [show z * (y : ℂ) - (y : ℂ) ^ 2 / 2 = z * ((y : ℝ) : ℂ) - ((y ^ 2 / 2 : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    rw [hre]

/-- The Gaussian integral of `P(y) e^{zy}` as a Lebesgue integral. -/
theorem integral_gaussianReal_eval_mul_cexp (P : ℝ[X]) (z : ℂ) :
    ∫ y, ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1 =
      (((Real.sqrt (2 * π))⁻¹ : ℝ) : ℂ) *
        ∫ y : ℝ, ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y - (y : ℂ) ^ 2 / 2) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with y
  have hpdf : gaussianPDFReal 0 1 y = (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    simp [gaussianPDFReal]
  rw [hpdf, Complex.real_smul]
  push_cast
  rw [show z * (y : ℂ) - (y : ℂ) ^ 2 / 2 = -(y : ℂ) ^ 2 / 2 + z * (y : ℂ) by ring,
    Complex.exp_add]
  ring

/-- `P(y) e^{zy}` is integrable against the standard Gaussian. -/
theorem integrable_gaussianReal_eval_mul_cexp (P : ℝ[X]) (z : ℂ) :
    Integrable (fun y : ℝ => ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y)) (gaussianReal 0 1) := by
  have hd : gaussianReal 0 1 = volume.withDensity fun y => ENNReal.ofReal (gaussianPDFReal 0 1 y) :=
    by rw [gaussianReal_of_var_ne_zero _ (by norm_num)]; rfl
  rw [hd, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_eval_mul_cexp_sub_sq P z).const_mul ((Real.sqrt (2 * π))⁻¹) |>.congr ?_
  filter_upwards with y
  have hpdf : gaussianPDFReal 0 1 y = (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    simp [gaussianPDFReal]
  rw [ENNReal.toReal_ofReal (by rw [hpdf]; positivity), hpdf, Complex.real_smul]
  push_cast
  rw [show z * (y : ℂ) - (y : ℂ) ^ 2 / 2 = -(y : ℂ) ^ 2 / 2 + z * (y : ℂ) by ring,
    Complex.exp_add]
  ring



/-! ### Gaussian integration by parts -/

theorem eval_map_ofReal (P : ℝ[X]) (y : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (y : ℂ) = ((P.eval y : ℝ) : ℂ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k c => simp

/-- The Lebesgue form of Gaussian integration by parts: the integral of the derivative of
`P(y) e^{zy - y²/2}` vanishes. -/
theorem integral_eval_mul_cexp_sub_sq_ibp (P : ℝ[X]) (z : ℂ) :
    ∫ y : ℝ, (((X * P).eval y : ℝ) : ℂ) * Complex.exp (z * y - (y : ℂ) ^ 2 / 2) =
      (∫ y : ℝ, (((derivative P).eval y : ℝ) : ℂ) * Complex.exp (z * y - (y : ℂ) ^ 2 / 2)) +
        z * ∫ y : ℝ, ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y - (y : ℂ) ^ 2 / 2) := by
  set Pc : ℂ[X] := P.map (algebraMap ℝ ℂ) with hPc
  set E : ℝ → ℂ := fun y => Complex.exp (z * y - (y : ℂ) ^ 2 / 2) with hE
  have hPcd : derivative Pc = (derivative P).map (algebraMap ℝ ℂ) := by
    rw [hPc, derivative_map]
  -- the derivative of `F w = Pc(w) e^{zw - w²/2}`
  have hF : ∀ w : ℂ, HasDerivAt (fun w : ℂ => Pc.eval w * Complex.exp (z * w - w ^ 2 / 2))
      (((derivative Pc).eval w + Pc.eval w * (z - w)) * Complex.exp (z * w - w ^ 2 / 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℂ => Pc.eval w) ((derivative Pc).eval w) w := Pc.hasDerivAt w
    have ha : HasDerivAt (fun w : ℂ => z * w) z w := by
      simpa using (hasDerivAt_id w).const_mul z
    have hb : HasDerivAt (fun w : ℂ => w ^ 2 / 2) w w := by
      have h := (hasDerivAt_pow 2 w).div_const 2
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun w : ℂ => z * w - w ^ 2 / 2) (z - w) w := ha.sub hb
    have h3 := h2.cexp
    exact (h1.mul h3).congr_deriv (by ring)
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun y : ℝ => ((P.eval y : ℝ) : ℂ) * E y)
      ((((derivative P - X * P).eval y : ℝ) : ℂ) * E y + z * (((P.eval y : ℝ) : ℂ) * E y)) y := by
    intro y
    have h := (hF (y : ℂ)).comp_ofReal
    have hfun : (fun y : ℝ => Pc.eval (y : ℂ) * Complex.exp (z * (y : ℂ) - (y : ℂ) ^ 2 / 2)) =
        fun y : ℝ => ((P.eval y : ℝ) : ℂ) * E y := by
      funext u; rw [eval_map_ofReal]
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [hPcd, eval_map_ofReal, eval_map_ofReal]
    simp only [eval_sub, eval_mul, eval_X, Complex.ofReal_sub, Complex.ofReal_mul, hE]
    ring
  have hint : Integrable fun y : ℝ => ((P.eval y : ℝ) : ℂ) * E y :=
    integrable_eval_mul_cexp_sub_sq P z
  have hint1 : Integrable fun y : ℝ => (((derivative P - X * P).eval y : ℝ) : ℂ) * E y :=
    integrable_eval_mul_cexp_sub_sq _ z
  have hint2 : Integrable fun y : ℝ => (((derivative P).eval y : ℝ) : ℂ) * E y :=
    integrable_eval_mul_cexp_sub_sq _ z
  have hint3 : Integrable fun y : ℝ => (((X * P).eval y : ℝ) : ℂ) * E y :=
    integrable_eval_mul_cexp_sub_sq _ z
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv
    (hint1.add (hint.const_mul z)) hint
  rw [integral_add hint1 (hint.const_mul z), integral_const_mul] at hzero
  have hsplit : ∫ y : ℝ, (((derivative P - X * P).eval y : ℝ) : ℂ) * E y =
      (∫ y : ℝ, (((derivative P).eval y : ℝ) : ℂ) * E y) -
        ∫ y : ℝ, (((X * P).eval y : ℝ) : ℂ) * E y := by
    rw [← integral_sub hint2 hint3]
    refine integral_congr_ae ?_
    filter_upwards with y
    simp only [eval_sub, Complex.ofReal_sub]
    ring
  rw [hsplit] at hzero
  linear_combination -hzero

/-- Gaussian integration by parts: `∫ y P(y) e^{zy} dγ = ∫ (P'(y) + z P(y)) e^{zy} dγ`. -/
theorem integral_gaussianReal_ibp (P : ℝ[X]) (z : ℂ) :
    ∫ y, (((X * P).eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1 =
      (∫ y, (((derivative P).eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1) +
        z * ∫ y, ((P.eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eval_mul_cexp, integral_gaussianReal_eval_mul_cexp,
    integral_gaussianReal_eval_mul_cexp, integral_eval_mul_cexp_sub_sq_ibp]
  ring

/-! ### Exponential moments and orthogonality -/

/-- The exponential moment of the standard Gaussian: `∫ e^{zy} dγ = e^{z²/2}`. -/
theorem integral_gaussianReal_cexp (z : ℂ) :
    ∫ y : ℝ, Complex.exp (z * y) ∂gaussianReal 0 1 = Complex.exp (z ^ 2 / 2) := by
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 1) z
  simp only [complexMGF, id_eq] at h
  simpa using h

/-- `∫ He_n(y) e^{zy} dγ = z^n e^{z²/2}`. -/
theorem integral_gaussianReal_hermiteR_mul_cexp (n : ℕ) (z : ℂ) :
    ∫ y, (((hermiteR n).eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1 =
      z ^ n * Complex.exp (z ^ 2 / 2) := by
  induction n with
  | zero => simpa using integral_gaussianReal_cexp z
  | succ n ih =>
    have hsplit :
        ∫ y, (((hermiteR (n + 1)).eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1 =
          (∫ y, (((X * hermiteR n).eval y : ℝ) : ℂ) * Complex.exp (z * y) ∂gaussianReal 0 1) -
            ∫ y, (((derivative (hermiteR n)).eval y : ℝ) : ℂ) * Complex.exp (z * y)
              ∂gaussianReal 0 1 := by
      rw [← integral_sub (integrable_gaussianReal_eval_mul_cexp _ z)
        (integrable_gaussianReal_eval_mul_cexp _ z)]
      refine integral_congr_ae ?_
      filter_upwards with y
      rw [hermiteR_succ]
      simp only [eval_sub, Complex.ofReal_sub]
      ring
    rw [hsplit, integral_gaussianReal_ibp, ih]
    ring

/-- Polynomial evaluations are integrable against the standard Gaussian. -/
theorem integrable_gaussianReal_eval (P : ℝ[X]) :
    Integrable (fun y : ℝ => P.eval y) (gaussianReal 0 1) := by
  have h := integrable_gaussianReal_eval_mul_cexp P 0
  simp only [zero_mul, Complex.exp_zero, mul_one] at h
  simpa using h.re

theorem integral_gaussianReal_eval_sub (Q R : ℝ[X]) :
    ∫ y, ((Q - R).eval y) ∂gaussianReal 0 1 =
      (∫ y, (Q.eval y) ∂gaussianReal 0 1) - ∫ y, (R.eval y) ∂gaussianReal 0 1 := by
  rw [← integral_sub (integrable_gaussianReal_eval Q) (integrable_gaussianReal_eval R)]
  simp only [eval_sub]

theorem integral_gaussianReal_eval_add (Q R : ℝ[X]) :
    ∫ y, ((Q + R).eval y) ∂gaussianReal 0 1 =
      (∫ y, (Q.eval y) ∂gaussianReal 0 1) + ∫ y, (R.eval y) ∂gaussianReal 0 1 := by
  rw [← integral_add (integrable_gaussianReal_eval Q) (integrable_gaussianReal_eval R)]
  simp only [eval_add]

/-- The real form of Gaussian integration by parts: `∫ y P(y) dγ = ∫ P'(y) dγ`. -/
theorem integral_gaussianReal_ibp_real (P : ℝ[X]) :
    ∫ y, ((X * P).eval y) ∂gaussianReal 0 1 =
      ∫ y, ((derivative P).eval y) ∂gaussianReal 0 1 := by
  have h := integral_gaussianReal_ibp P 0
  simp only [zero_mul, Complex.exp_zero, mul_one, add_zero] at h
  exact_mod_cast h

/-- Iterated Gaussian integration by parts: `∫ He_n P dγ = ∫ P^{(n)} dγ`. -/
theorem integral_gaussianReal_hermiteR_mul_eval (n : ℕ) (P : ℝ[X]) :
    ∫ y, ((hermiteR n * P).eval y) ∂gaussianReal 0 1 =
      ∫ y, ((derivative^[n] P).eval y) ∂gaussianReal 0 1 := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    have e1 : hermiteR (n + 1) * P = X * (hermiteR n * P) - derivative (hermiteR n) * P := by
      rw [hermiteR_succ]; ring
    rw [e1, integral_gaussianReal_eval_sub, integral_gaussianReal_ibp_real, derivative_mul,
      integral_gaussianReal_eval_add, ih (derivative P), Function.iterate_succ_apply]
    ring

/-- Orthogonality of the Hermite polynomials against the standard Gaussian. -/
theorem integral_gaussianReal_hermiteR_mul_hermiteR (m n : ℕ) :
    ∫ y, ((hermiteR m).eval y * (hermiteR n).eval y) ∂gaussianReal 0 1 =
      if m = n then (n.factorial : ℝ) else 0 := by
  have key : ∀ a b : ℕ, b < a →
      ∫ y, ((hermiteR a).eval y * (hermiteR b).eval y) ∂gaussianReal 0 1 = 0 := by
    intro a b hba
    have h := integral_gaussianReal_hermiteR_mul_eval a (hermiteR b)
    simp only [eval_mul] at h
    rw [h, iterate_derivative_eq_zero (by simpa using hba)]
    simp
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg h.ne]
    rw [show (fun y : ℝ => (hermiteR m).eval y * (hermiteR n).eval y) =
      fun y : ℝ => (hermiteR n).eval y * (hermiteR m).eval y from funext fun y => mul_comm _ _]
    exact key n m h
  · subst h
    have hh := integral_gaussianReal_hermiteR_mul_eval m (hermiteR m)
    simp only [eval_mul] at hh
    rw [if_pos rfl, hh, iterate_derivative_hermiteR_self]
    simp
  · rw [if_neg h.ne']
    exact key m n h

/-! ### The real exponential moment -/

theorem cexp_ofReal_mul (s y : ℝ) :
    Complex.exp ((s : ℂ) * (y : ℂ)) = ((Real.exp (s * y) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- `e^{sy}` is integrable against the standard Gaussian. -/
theorem integrable_gaussianReal_rexp (s : ℝ) :
    Integrable (fun y : ℝ => Real.exp (s * y)) (gaussianReal 0 1) := by
  have h := integrable_gaussianReal_eval_mul_cexp 1 (s : ℂ)
  simp only [eval_one, Complex.ofReal_one, one_mul] at h
  have h2 := h.re
  refine h2.congr ?_
  filter_upwards with y
  rw [cexp_ofReal_mul]
  exact Complex.ofReal_re _

/-- The moment generating function of the standard Gaussian: `∫ e^{sy} dγ = e^{s²/2}`. -/
theorem integral_gaussianReal_rexp (s : ℝ) :
    ∫ y : ℝ, Real.exp (s * y) ∂gaussianReal 0 1 = Real.exp (s ^ 2 / 2) := by
  have h := integral_gaussianReal_cexp (s : ℂ)
  have hl : ∫ y : ℝ, Complex.exp ((s : ℂ) * y) ∂gaussianReal 0 1 =
      ((∫ y : ℝ, Real.exp (s * y) ∂gaussianReal 0 1 : ℝ) : ℂ) := by
    rw [integral_congr_ae (g := fun y : ℝ => ((Real.exp (s * y) : ℝ) : ℂ))
      (Eventually.of_forall fun y => cexp_ofReal_mul s y)]
    exact integral_complex_ofReal
  rw [hl] at h
  have hr : ((s : ℂ)) ^ 2 / 2 = ((s ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hr, ← Complex.ofReal_exp] at h
  exact_mod_cast h

end ProbabilityTheory
