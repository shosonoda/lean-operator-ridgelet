import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Summability of quadratic decay over finite integer products -/

open Finset
namespace Real
theorem summable_one_add_int_sq_rpow {a : ℝ} (ha : 1 / 2 < a) :
    Summable (fun n : ℤ => (1 + (n : ℝ)^2)^(-a)) := by
  have hs := (summable_abs_int_rpow (b := 2*a) (by linarith)).add
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  by_cases hn : n = 0
  · subst n
    simp [show 2*a ≠ 0 by linarith]
  · simp only [Pi.add_apply, if_neg hn, add_zero]
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    calc
      (1 + (n : ℝ)^2)^(-a) ≤ ((n : ℝ)^2)^(-a) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hn') (by linarith) (by linarith)
      _ = |(n : ℝ)| ^ (-(2*a)) := by
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring

theorem summable_fin_prod {α : Type*} {f : α → ℝ} (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n) (d : ℕ) :
    Summable (fun n : Fin d → α => ∏ j, f (n j)) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have hs := hf.mul_of_nonneg ih hf0 (fun n => Finset.prod_nonneg fun j _ => hf0 (n j))
    have he := (Fin.consEquiv (fun _ : Fin (d+1) => α)).summable_iff
      (f := fun n => ∏ j, f (n j))
    apply he.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hs

end Real

namespace Real
theorem summable_one_add_sum_int_sq_rpow (d : ℕ) (s : ℝ) (hs : (d : ℝ)/2 < s) :
    Summable (fun n : Fin d → ℤ => (1 + (∑ j, (n j : ℝ)^2))^(-s)) := by
  by_cases hd : d = 0
  · subst d
    exact Summable.of_finite
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have ha : 1/2 < s / d := by apply (lt_div_iff₀ hdpos).mpr; linarith
  have hsum := Real.summable_fin_prod (Real.summable_one_add_int_sq_rpow ha)
    (fun n : ℤ => Real.rpow_nonneg (by positivity) (-(s/d))) d
  apply hsum.of_norm_bounded
  intro n
  have hA : 0 < 1 + (∑ j, (n j : ℝ)^2) := by
    have hnonneg := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (n j : ℝ))
    linarith
  have hprod : 0 < ∏ j, (1 + (n j : ℝ)^2) := Finset.prod_pos fun j _ => by positivity
  have hle : (∏ j, (1 + (n j : ℝ)^2)) ≤ (1 + (∑ j, (n j : ℝ)^2))^d := by
    calc
      _ ≤ ∏ j : Fin d, (1 + (∑ j, (n j : ℝ)^2)) := by
        apply Finset.prod_le_prod (fun j _ => by positivity)
        intro j hj
        gcongr
        exact Finset.single_le_sum (fun j _ => sq_nonneg (n j : ℝ)) (Finset.mem_univ j)
      _ = _ := by simp
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  calc
    (1 + (∑ j, (n j : ℝ)^2))^(-s) = ((1 + (∑ j, (n j : ℝ)^2))^d)^(-(s/d)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
      congr 1
      field_simp
    _ ≤ (∏ j, (1 + (n j : ℝ)^2))^(-(s/d)) :=
      Real.rpow_le_rpow_of_nonpos hprod hle (by linarith)
    _ = ∏ j, (1 + (n j : ℝ)^2)^(-(s/d)) :=
      (Real.finsetProd_rpow Finset.univ _ (fun j _ => by positivity) _).symm
end Real
