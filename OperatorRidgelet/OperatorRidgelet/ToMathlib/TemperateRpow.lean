/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! # Real powers of positive functions of temperate growth

This extends the argument for Mathlib's Bessel-potential multiplier to arbitrary
functions of temperate growth bounded below by one.
-/

noncomputable section
open Set
open scoped Nat NNReal ContDiff
namespace Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real power of a temperate function bounded below by one has temperate growth. -/
theorem HasTemperateGrowth.rpow_of_one_le {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hf1 : ∀ x, 1 ≤ f x) (r : ℝ) : (fun x => f x ^ r).HasTemperateGrowth := by
  set t := {y : ℝ | 1 / 2 < y}
  have ht : Set.range f ⊆ t := by
    rintro - ⟨x, rfl⟩
    exact lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) (hf1 x)
  have hdiff : ContDiffOn ℝ ∞ (fun x ↦ x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx ↦ (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  apply HasTemperateGrowth.comp' ht hunique hdiff _ hf
  -- The remaining part of the proof is proving that `x ↦ x ^ r` has temperate growth on `t`.
  -- This could be generalized to `t := {y : ℝ | ε < y}` for any `0 < ε < 1` if necessary.
  intro N
  /- Since `x ^ r` for negative `r` blows up near the origin (and we can't take
  `t := {y : ℝ | 1 / 2 < y}`), we have to choose `k` later than `N - r` times some factor depending
  on `t`. -/
  obtain ⟨k, hk⟩ := exists_nat_ge (max r <| (N - r) * Real.log 2 / (Real.log (3 / 2)))
  have hk₁ : r ≤ k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N - r) ≤ (Real.log (3 / 2)) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  use k, ∑ k ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ k)‖, by positivity
  intro n hn x hx
  have : ContDiffAt ℝ n (fun x ↦ x ^ r) x :=
    Real.contDiffAt_rpow_const <| Or.inl (lt_trans (by norm_num) hx).ne'
  -- We calculate the derivative of `x ^ r`.
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · have : n ∈ Finset.range (N + 1) := by grind
    apply Finset.single_le_sum (fun _ _ ↦ by positivity) this
  -- It remains to show that `‖x ^ (r - n)‖ ≤ (1 + ‖x‖) ^ k`:
  have hx' : 1 / 2 < x := by simpa [t] using hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans
  -- We consider the two cases `n ≤ r` and `r < n`.
  by_cases! h : 0 ≤ r - n
  · have : r - n ≤ k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) this)
  have h : 0 < n - r := by grind
  calc
    /- In the case `0 < n - r`, we need the factor `Real.log 2 / (Real.log (3 / 2))` to control
    the growth near `‖x‖ = 1/2`. -/
    _ = x ^ (-(n - r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ ≤ (2 : ℝ) ^ (n - r) := by
      simp only [one_div, Set.mem_setOf_eq, t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n - r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ ≤ Real.exp (Real.log (3 / 2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ ≤ (3 / 2) ^ k := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos]
      norm_num
    _ ≤ _ := by
      gcongr
      grind

end Function

