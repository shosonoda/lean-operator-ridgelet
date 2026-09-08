import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The reciprocal of a function of temperate growth bounded away from zero

If `f : E → ℝ` has temperate growth and `f ≥ c > 0`, then `x ↦ (f x)⁻¹` has temperate growth:
the iterated derivatives of `y ↦ y⁻¹` are bounded on `(c/2, ∞)`, and
`Function.HasTemperateGrowth.comp'` composes them with the derivatives of `f`.
-/

open Set
open scoped ContDiff

namespace Function

/-- The iterated derivatives of `y ↦ y⁻¹` are uniformly bounded on `(c/2, ∞)` for `c > 0`. -/
theorem norm_iteratedDeriv_inv_le {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ≤ N) {y : ℝ}
    (hy : c / 2 < y) :
    ‖iteratedDeriv n (fun y : ℝ => y⁻¹) y‖ ≤ (N.factorial : ℝ) * (max 1 (2 / c)) ^ (N + 1) := by
  have hy0 : 0 < y := lt_trans (by positivity) hy
  rw [iteratedDeriv_eq_iterate, show (fun y : ℝ => y⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast,
    Real.norm_eq_abs, abs_of_pos (zpow_pos hy0 _)]
  have h1 : (n.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hn
  have h2 : y ^ (-1 - n : ℤ) ≤ (max 1 (2 / c)) ^ (N + 1) := by
    rw [show (-1 - n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hyc : y⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ hy0 (by positivity), inv_div]
      exact hy.le
    calc (y ^ (n + 1))⁻¹ = (y⁻¹) ^ (n + 1) := by rw [inv_pow]
      _ ≤ (max 1 (2 / c)) ^ (n + 1) := by
          gcongr
          exact hyc.trans (le_max_right _ _)
      _ ≤ (max 1 (2 / c)) ^ (N + 1) := by
          apply pow_le_pow_right₀ (le_max_left _ _)
          omega
  calc (n.factorial : ℝ) * y ^ (-1 - n : ℤ)
      ≤ (N.factorial : ℝ) * (max 1 (2 / c)) ^ (N + 1) := by
        apply mul_le_mul h1 h2 (zpow_pos hy0 _).le (by positivity)

/-- The reciprocal of a real function of temperate growth bounded below by a positive constant
has temperate growth. -/
theorem HasTemperateGrowth.inv_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : f.HasTemperateGrowth) {c : ℝ} (hc : 0 < c) (hcf : ∀ x, c ≤ f x) :
    HasTemperateGrowth (fun x => (f x)⁻¹) := by
  have ht : Set.range f ⊆ Set.Ioi (c / 2) := by
    rintro - ⟨x, rfl⟩
    exact lt_of_lt_of_le (by linarith) (hcf x)
  have hopen : IsOpen (Set.Ioi (c / 2)) := isOpen_Ioi
  have hunique : UniqueDiffOn ℝ (Set.Ioi (c / 2)) := hopen.uniqueDiffOn
  have hdiff : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Set.Ioi (c / 2)) := by
    intro y hy
    exact (contDiffAt_inv ℝ (lt_trans (by positivity) hy).ne').contDiffWithinAt
  change HasTemperateGrowth ((fun y : ℝ => y⁻¹) ∘ f)
  refine HasTemperateGrowth.comp' ht hunique hdiff ?_ hf
  intro N
  refine ⟨0, N.factorial * (max 1 (2 / c)) ^ (N + 1), by positivity, ?_⟩
  intro n hn y hy
  rw [iteratedFDerivWithin_of_isOpen n hopen hy, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    pow_zero, mul_one]
  exact norm_iteratedDeriv_inv_le hc hn hy

end Function
