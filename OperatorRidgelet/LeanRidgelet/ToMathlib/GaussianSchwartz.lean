-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/GaussianSchwartz.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian as a Schwartz function

Mathlib has the Gaussian integral and the Fourier transform of a Gaussian, but no realization of
the Gaussian as an element of Schwartz space. This file supplies one, together with the two
facts the construction needs: every derivative of the Gaussian is a polynomial multiple of it,
and every polynomial is dominated by the reciprocal Gaussian.

## Main results

* `Real.abs_pow_mul_exp_neg_sq_div_two_le`: `|x|^d e^{-x²/2} ≤ 1 + 2^d d!`, from
  `x^d/d! ≤ exp x`.
* `Real.exists_polynomial_iteratedDeriv_gaussian`: `G^{(n)}(z) = p_n(z) e^{-z²/2}` with
  `p_0 = 1` and `p_{n+1} = p_n' - X p_n`.
* `Real.gaussianSchwartz`: the Gaussian `z ↦ e^{-z²/2}` as a complex-valued Schwartz function,
  with `Real.gaussianSchwartz_apply`. Its Fourier transform is Mathlib's
  `fourierIntegral_gaussian`; the article-convention form is
  `LeanRidgelet.angularFourier1D_gaussianWindow`.

This file is a Mathlib upstream candidate; it imports only Mathlib.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Real

/-! ## Polynomial growth against the Gaussian -/

/-- `t^d e^{-t} ≤ d!` for `t ≥ 0`, from the exponential series. -/
theorem pow_mul_exp_neg_le_factorial (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ d * Real.exp (-t) ≤ (d.factorial : ℝ) := by
  have hfac : (0 : ℝ) < (d.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos d
  have h := Real.pow_div_factorial_le_exp t ht d
  rw [div_le_iff₀ hfac] at h
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos t), mul_comm]
  exact h

/-- Every power is dominated by the Gaussian: `|x|^d e^{-x²/2} ≤ 1 + 2^d d!`. -/
theorem abs_pow_mul_exp_neg_sq_div_two_le (d : ℕ) (x : ℝ) :
    |x| ^ d * Real.exp (-x ^ 2 / 2) ≤ 1 + 2 ^ d * (d.factorial : ℝ) := by
  have hfac : (0 : ℝ) ≤ (d.factorial : ℝ) := by positivity
  have hexp1 : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  have hexp0 : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  have hkey : |x| ^ (2 * d) * Real.exp (-x ^ 2 / 2) ≤ 2 ^ d * (d.factorial : ℝ) := by
    have ht : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
    have h := pow_mul_exp_neg_le_factorial d ht
    have hx : |x| ^ (2 * d) = 2 ^ d * (x ^ 2 / 2) ^ d := by
      rw [pow_mul, sq_abs, ← mul_pow]
      ring_nf
    have hne : Real.exp (-x ^ 2 / 2) = Real.exp (-(x ^ 2 / 2)) := by
      congr 1
      ring
    rw [hx, hne, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hpos : (0 : ℝ) ≤ 2 ^ d * (d.factorial : ℝ) := by positivity
  rcases le_or_gt |x| 1 with hx1 | hx1
  · have h1 : |x| ^ d ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    nlinarith [pow_nonneg (abs_nonneg x) d, hexp0.le]
  · have h1 : |x| ^ d ≤ |x| ^ (2 * d) := pow_le_pow_right₀ (le_of_lt hx1) (by omega)
    nlinarith

/-- A crude polynomial bound: `|p(z)| ≤ C (1 + |z|)^d`. -/
theorem exists_bound_polynomial_eval (p : Polynomial ℝ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ z : ℝ, |p.eval z| ≤ C * (1 + |z|) ^ d := by
  induction p using Polynomial.induction_on' with
  | add q r hq hr =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := hq
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := hr
    refine ⟨C₁ + C₂, max d₁ d₂, by positivity, fun z => ?_⟩
    have hz : (1 : ℝ) ≤ 1 + |z| := by simp [abs_nonneg z]
    have e₁ : C₁ * (1 + |z|) ^ d₁ ≤ C₁ * (1 + |z|) ^ max d₁ d₂ :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (le_max_left _ _)) hC₁
    have e₂ : C₂ * (1 + |z|) ^ d₂ ≤ C₂ * (1 + |z|) ^ max d₁ d₂ :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (le_max_right _ _)) hC₂
    calc |(q + r).eval z| ≤ |q.eval z| + |r.eval z| := by
          rw [Polynomial.eval_add]
          exact abs_add_le _ _
      _ ≤ C₁ * (1 + |z|) ^ max d₁ d₂ + C₂ * (1 + |z|) ^ max d₁ d₂ :=
          add_le_add (le_trans (h₁ z) e₁) (le_trans (h₂ z) e₂)
      _ = (C₁ + C₂) * (1 + |z|) ^ max d₁ d₂ := by ring
  | monomial n a =>
    refine ⟨|a|, n, abs_nonneg a, fun z => ?_⟩
    rw [Polynomial.eval_monomial, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg z) (by linarith [abs_nonneg z]) n) (abs_nonneg a)

/-- `(1 + |x|)^N e^{-x²/2} ≤ 2^N (1 + 2^N N!)`. -/
theorem one_add_abs_pow_mul_exp_neg_sq_div_two_le (N : ℕ) (x : ℝ) :
    (1 + |x|) ^ N * Real.exp (-x ^ 2 / 2) ≤ 2 ^ N * (1 + 2 ^ N * (N.factorial : ℝ)) := by
  have hexp0 : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  have hexp1 : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  have hfac : (0 : ℝ) ≤ 2 ^ N * (N.factorial : ℝ) := by positivity
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  rcases le_or_gt |x| 1 with h | h
  · have h1 : (1 + |x|) ^ N ≤ 2 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + |x|) N]
  · have h1 : (1 + |x|) ^ N ≤ 2 ^ N * |x| ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    have h2 := abs_pow_mul_exp_neg_sq_div_two_le N x
    nlinarith [pow_nonneg (abs_nonneg x) N, pow_nonneg (by positivity : (0:ℝ) ≤ 1 + |x|) N]

/-! ## Derivatives of the Gaussian -/

/-- Every derivative of the Gaussian is a polynomial multiple of it, with the recursion
`p_0 = 1`, `p_{n+1} = p_n' - X p_n`. -/
theorem exists_polynomial_iteratedDeriv_gaussian (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ z : ℝ,
      iteratedDeriv n (fun w : ℝ => ((Real.exp (-w ^ 2 / 2) : ℝ) : ℂ)) z
        = ((p.eval z * Real.exp (-z ^ 2 / 2) : ℝ) : ℂ) := by
  induction n with
  | zero => exact ⟨1, fun z => by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Polynomial.derivative p - Polynomial.X * p, fun z => ?_⟩
    have hfun : iteratedDeriv n (fun w : ℝ => ((Real.exp (-w ^ 2 / 2) : ℝ) : ℂ))
        = fun w : ℝ => ((p.eval w * Real.exp (-w ^ 2 / 2) : ℝ) : ℂ) := funext hp
    rw [iteratedDeriv_succ, hfun]
    have hexpder : HasDerivAt (fun w : ℝ => Real.exp (-w ^ 2 / 2))
        (Real.exp (-z ^ 2 / 2) * (-z)) z := by
      have h3 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-z) z := by
        have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
          simpa using hasDerivAt_pow 2 z
        have h6 := hsq.neg.div_const 2
        have h7 : -(2 * z) / 2 = -z := by ring
        rwa [h7] at h6
      exact h3.exp
    have hreal : HasDerivAt (fun w : ℝ => p.eval w * Real.exp (-w ^ 2 / 2))
        ((Polynomial.derivative p - Polynomial.X * p).eval z * Real.exp (-z ^ 2 / 2)) z := by
      have h := (Polynomial.hasDerivAt p z).mul hexpder
      have heq : (Polynomial.derivative p).eval z * Real.exp (-z ^ 2 / 2)
            + p.eval z * (Real.exp (-z ^ 2 / 2) * (-z))
          = (Polynomial.derivative p - Polynomial.X * p).eval z * Real.exp (-z ^ 2 / 2) := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
        ring
      rwa [heq] at h
    exact hreal.ofReal_comp.deriv

/-! ## The Gaussian as a Schwartz function -/

/-- The Gaussian `z ↦ e^{-z²/2}` as a complex-valued Schwartz function. -/
def gaussianSchwartz : SchwartzMap ℝ ℂ where
  toFun := fun z => ((Real.exp (-z ^ 2 / 2) : ℝ) : ℂ)
  smooth' := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  decay' := by
    intro k n
    obtain ⟨p, hp⟩ := exists_polynomial_iteratedDeriv_gaussian n
    obtain ⟨C, d, hC, hbound⟩ := exists_bound_polynomial_eval p
    refine ⟨C * (2 ^ (k + d) * (1 + 2 ^ (k + d) * ((k + d).factorial : ℝ))), fun z => ?_⟩
    have hz0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have hexp0 : (0 : ℝ) < Real.exp (-z ^ 2 / 2) := Real.exp_pos _
    have hnorm : ‖iteratedFDeriv ℝ n (fun w : ℝ => ((Real.exp (-w ^ 2 / 2) : ℝ) : ℂ)) z‖
        = |p.eval z| * Real.exp (-z ^ 2 / 2) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hp z, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos hexp0]
    rw [hnorm, Real.norm_eq_abs]
    -- `|z|^k |p(z)| ≤ C (1+|z|)^{k+d}`
    have hpoly : |z| ^ k * |p.eval z| ≤ C * (1 + |z|) ^ (k + d) := by
      have h1 : |z| ^ k ≤ (1 + |z|) ^ k :=
        pow_le_pow_left₀ (abs_nonneg z) (by linarith) k
      calc |z| ^ k * |p.eval z| ≤ (1 + |z|) ^ k * (C * (1 + |z|) ^ d) :=
            mul_le_mul h1 (hbound z) (abs_nonneg _) (by positivity)
        _ = C * (1 + |z|) ^ (k + d) := by rw [pow_add]; ring
    have hgauss := one_add_abs_pow_mul_exp_neg_sq_div_two_le (k + d) z
    calc |z| ^ k * (|p.eval z| * Real.exp (-z ^ 2 / 2))
        = (|z| ^ k * |p.eval z|) * Real.exp (-z ^ 2 / 2) := by ring
      _ ≤ (C * (1 + |z|) ^ (k + d)) * Real.exp (-z ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hpoly hexp0.le
      _ = C * ((1 + |z|) ^ (k + d) * Real.exp (-z ^ 2 / 2)) := by ring
      _ ≤ C * (2 ^ (k + d) * (1 + 2 ^ (k + d) * ((k + d).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hgauss hC

@[simp]
theorem gaussianSchwartz_apply (z : ℝ) :
    gaussianSchwartz z = ((Real.exp (-z ^ 2 / 2) : ℝ) : ℂ) := rfl

end Real
