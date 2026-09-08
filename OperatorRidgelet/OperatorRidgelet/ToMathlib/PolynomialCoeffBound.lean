import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Coefficient bounds for polynomials

Elementary estimates for polynomials over a normed field in terms of a uniform bound on their
coefficients and a bound on their degree.

* `Polynomial.norm_eval_le_of_norm_coeff_le`: `‖p(x)‖ ≤ (d + 1) M (1 + ‖x‖)^d` when
  `natDegree p ≤ d` and every coefficient has norm at most `M`.
* `Polynomial.gaussianDerivOp c p = p' - c X p` is the polynomial with
  `d/dx (p(x) e^{-c x²/2}) = (gaussianDerivOp c p)(x) e^{-c x²/2}`; its iterates keep the degree
  and the coefficients under control (`Polynomial.norm_coeff_gaussianDerivOp_iterate_le`,
  `Polynomial.norm_eval_gaussianDerivOp_iterate_le`).
* `MvPolynomial.exists_bound_eval₂_C_mul_X_pow`: substituting `X o ↦ v o * X ^ e o` into a
  multivariate polynomial gives a univariate polynomial whose degree is bounded independently of
  `v` and whose coefficients grow polynomially in the size of `v`.
-/

open scoped Polynomial

namespace Polynomial

section Eval

variable {𝕜 : Type*} [NormedField 𝕜]

/-- `‖p(x)‖ ≤ (d + 1) M (1 + ‖x‖)^d` when `natDegree p ≤ d` and `‖coeff p j‖ ≤ M` for all `j`. -/
theorem norm_eval_le_of_norm_coeff_le {p : 𝕜[X]} {d : ℕ} (hd : p.natDegree ≤ d) {M : ℝ}
    (hM : ∀ j, ‖p.coeff j‖ ≤ M) (x : 𝕜) :
    ‖p.eval x‖ ≤ (d + 1) * M * (1 + ‖x‖) ^ d := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (d + 1), ‖p.coeff i * x ^ i‖
      ≤ ∑ i ∈ Finset.range (d + 1), M * (1 + ‖x‖) ^ d := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : ‖x‖ ^ i ≤ (1 + ‖x‖) ^ d :=
          (pow_le_pow_left₀ (norm_nonneg x) (by linarith) i).trans
            (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hi')
        exact mul_le_mul (hM i) h1 (by positivity) hM0
    _ = (d + 1) * M * (1 + ‖x‖) ^ d := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Eval

section GaussianDerivOp

variable {R : Type*} [CommRing R]

/-- The polynomial `p' - c X p`, which satisfies
`d/dx (p(x) e^{-c x²/2}) = (gaussianDerivOp c p)(x) e^{-c x²/2}`. -/
noncomputable def gaussianDerivOp (c : R) (p : R[X]) : R[X] :=
  derivative p - C c * (X * p)

/-- `gaussianDerivOp` raises the degree by at most one. -/
theorem natDegree_gaussianDerivOp_le (c : R) (p : R[X]) :
    (gaussianDerivOp c p).natDegree ≤ p.natDegree + 1 := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le p).trans (by omega)
  · refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have := natDegree_X_le (R := R)
    omega

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Coefficient bound for `gaussianDerivOp`: if `natDegree p ≤ d` and `‖coeff p j‖ ≤ M` for all
`j`, then every coefficient of `p' - c X p` has norm at most `(d + ‖c‖) M`. -/
theorem norm_coeff_gaussianDerivOp_le (c : 𝕜) {p : 𝕜[X]} {d : ℕ} (hd : p.natDegree ≤ d) {M : ℝ}
    (hM : ∀ j, ‖p.coeff j‖ ≤ M) (j : ℕ) :
    ‖(gaussianDerivOp c p).coeff j‖ ≤ (d + ‖c‖) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hder : ‖(derivative p).coeff j‖ ≤ d * M := by
    rw [coeff_derivative]
    by_cases hj : j + 1 ≤ d
    · rw [norm_mul]
      have h1 : ‖((j : 𝕜) + 1)‖ ≤ d := by
        have h2 : ((j : 𝕜) + 1) = ((j + 1 : ℕ) : 𝕜) := by push_cast; ring
        rw [h2]
        refine (Nat.norm_cast_le (j + 1)).trans ?_
        rw [norm_one, mul_one]
        exact_mod_cast hj
      calc ‖p.coeff (j + 1)‖ * ‖((j : 𝕜) + 1)‖ ≤ M * d :=
            mul_le_mul (hM _) h1 (norm_nonneg _) hM0
        _ = d * M := mul_comm _ _
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, norm_zero]
      positivity
  have hX : ‖(C c * (X * p)).coeff j‖ ≤ ‖c‖ * M := by
    rw [coeff_C_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    cases j with
    | zero => rw [coeff_X_mul_zero, norm_zero]; exact hM0
    | succ n => rw [coeff_X_mul]; exact hM n
  calc ‖(gaussianDerivOp c p).coeff j‖
      = ‖(derivative p).coeff j - (C c * (X * p)).coeff j‖ := by
        rw [gaussianDerivOp, coeff_sub]
    _ ≤ ‖(derivative p).coeff j‖ + ‖(C c * (X * p)).coeff j‖ := norm_sub_le _ _
    _ ≤ d * M + ‖c‖ * M := add_le_add hder hX
    _ = (d + ‖c‖) * M := by ring

/-- Degree and coefficient bounds for the iterates of `gaussianDerivOp`: the `n`-th iterate has
degree at most `d + n` and coefficients of norm at most `(d + n + ‖c‖)^n M`. -/
theorem norm_coeff_gaussianDerivOp_iterate_le (c : 𝕜) {p : 𝕜[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    {M : ℝ} (hM : ∀ j, ‖p.coeff j‖ ≤ M) (n : ℕ) :
    ((gaussianDerivOp c)^[n] p).natDegree ≤ d + n ∧
      ∀ j, ‖((gaussianDerivOp c)^[n] p).coeff j‖ ≤ (d + n + ‖c‖) ^ n * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  induction n with
  | zero => simpa using ⟨hd, hM⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨(natDegree_gaussianDerivOp_le _ _).trans (by omega), fun j => ?_⟩
    refine (norm_coeff_gaussianDerivOp_le c ih1 ih2 j).trans ?_
    have h0 : (0 : ℝ) ≤ d + n + ‖c‖ := by positivity
    have h1 : (d + n + ‖c‖ : ℝ) ≤ d + (n + 1 : ℕ) + ‖c‖ := by push_cast; linarith
    calc ((d + n : ℕ) + ‖c‖) * ((d + n + ‖c‖) ^ n * M) = (d + n + ‖c‖) ^ (n + 1) * M := by
          push_cast
          ring
      _ ≤ (d + (n + 1 : ℕ) + ‖c‖) ^ (n + 1) * M := by gcongr

/-- Evaluation bound for the iterates of `gaussianDerivOp`:
`‖((gaussianDerivOp c)^[n] p)(x)‖ ≤ (d + n + 1) (d + n + ‖c‖)^n M (1 + ‖x‖)^(d + n)`. -/
theorem norm_eval_gaussianDerivOp_iterate_le (c : 𝕜) {p : 𝕜[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    {M : ℝ} (hM : ∀ j, ‖p.coeff j‖ ≤ M) (n : ℕ) (x : 𝕜) :
    ‖((gaussianDerivOp c)^[n] p).eval x‖ ≤
      (d + n + 1) * ((d + n + ‖c‖) ^ n * M) * (1 + ‖x‖) ^ (d + n) := by
  obtain ⟨h1, h2⟩ := norm_coeff_gaussianDerivOp_iterate_le c hd hM n
  have := norm_eval_le_of_norm_coeff_le h1 h2 x
  push_cast at this
  exact this

end GaussianDerivOp

end Polynomial

namespace MvPolynomial

section Subst

variable {σ R : Type*} [CommSemiring R]

/-- Evaluating the univariate polynomial obtained by substituting `X o ↦ v o * X ^ e o` is the
evaluation of the original polynomial at `o ↦ v o * x ^ e o`. -/
theorem eval_eval₂_C_mul_X_pow (q : MvPolynomial σ R) (v : σ → R) (e : σ → ℕ) (x : R) :
    (eval₂ Polynomial.C (fun o => Polynomial.C (v o) * Polynomial.X ^ e o) q).eval x =
      eval (fun o => v o * x ^ e o) q := by
  have h := eval₂_comp_left (Polynomial.evalRingHom x) Polynomial.C
    (fun o => Polynomial.C (v o) * Polynomial.X ^ e o) q
  simp only [Polynomial.coe_evalRingHom, Function.comp_def, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  show eval₂ _ _ q = eval₂ (RingHom.id R) _ q
  congr 1
  ext a
  simp

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Substituting `X o ↦ v o * X ^ e o` into `q` gives a univariate polynomial of degree at most
`d` and with coefficients of norm at most `C t^d`, where `d` and `C` depend only on `q`, `e`,
and the bounds `b`, and `t ≥ 1` is any number with `‖v o‖ ≤ b o * t ^ e o` for all `o`. -/
theorem exists_bound_eval₂_C_mul_X_pow (q : MvPolynomial σ 𝕜) (e : σ → ℕ) (b : σ → ℝ)
    (hb : ∀ o, 0 ≤ b o) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (v : σ → 𝕜) (t : ℝ), 1 ≤ t → (∀ o, ‖v o‖ ≤ b o * t ^ e o) →
      (eval₂ Polynomial.C (fun o => Polynomial.C (v o) * Polynomial.X ^ e o) q).natDegree ≤ d ∧
      ∀ j, ‖(eval₂ Polynomial.C (fun o => Polynomial.C (v o) * Polynomial.X ^ e o) q).coeff j‖ ≤
        C * t ^ d := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ‖a‖, norm_nonneg a, fun v t ht hv => ?_⟩
    simp only [eval₂_C, Polynomial.natDegree_C, le_refl, true_and, pow_zero, mul_one]
    intro j
    rw [Polynomial.coeff_C]
    split_ifs
    · exact le_rfl
    · simp
  | add p q hp hq =>
    obtain ⟨d₁, C₁, hC₁, h₁⟩ := hp
    obtain ⟨d₂, C₂, hC₂, h₂⟩ := hq
    refine ⟨d₁ + d₂, C₁ + C₂, by positivity, fun v t ht hv => ?_⟩
    obtain ⟨hd₁, hc₁⟩ := h₁ v t ht hv
    obtain ⟨hd₂, hc₂⟩ := h₂ v t ht hv
    rw [eval₂_add]
    refine ⟨(Polynomial.natDegree_add_le _ _).trans (max_le (by omega) (by omega)), fun j => ?_⟩
    rw [Polynomial.coeff_add]
    have ht₁ : t ^ d₁ ≤ t ^ (d₁ + d₂) := pow_le_pow_right₀ ht (by omega)
    have ht₂ : t ^ d₂ ≤ t ^ (d₁ + d₂) := pow_le_pow_right₀ ht (by omega)
    calc ‖_ + _‖ ≤ C₁ * t ^ d₁ + C₂ * t ^ d₂ := (norm_add_le _ _).trans (add_le_add (hc₁ j) (hc₂ j))
      _ ≤ C₁ * t ^ (d₁ + d₂) + C₂ * t ^ (d₁ + d₂) := by gcongr
      _ = (C₁ + C₂) * t ^ (d₁ + d₂) := by ring
  | mul_X p n hp =>
    obtain ⟨d₁, C₁, hC₁, h₁⟩ := hp
    refine ⟨d₁ + e n, C₁ * b n, mul_nonneg hC₁ (hb n), fun v t ht hv => ?_⟩
    obtain ⟨hd₁, hc₁⟩ := h₁ v t ht hv
    rw [eval₂_mul, eval₂_X]
    refine ⟨Polynomial.natDegree_mul_le.trans
      (add_le_add hd₁ (Polynomial.natDegree_C_mul_X_pow_le _ _)), fun j => ?_⟩
    rw [mul_left_comm, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow', norm_mul]
    split_ifs with hj
    · calc ‖v n‖ * ‖Polynomial.coeff _ (j - e n)‖ ≤ (b n * t ^ e n) * (C₁ * t ^ d₁) :=
            mul_le_mul (hv n) (hc₁ _) (norm_nonneg _)
              (mul_nonneg (hb n) (pow_nonneg (by linarith) _))
        _ = C₁ * b n * t ^ (d₁ + e n) := by rw [pow_add]; ring
    · rw [norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hC₁ (hb n)) (pow_nonneg (by linarith) _)

end Subst

end MvPolynomial
