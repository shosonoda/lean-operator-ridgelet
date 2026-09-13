import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The norm of a vector as a supremum over the unit ball

* `exists_norm_le_real_inner`: in a real inner product space the norm of `w` is attained as
  `⟪y, w⟫_ℝ` at a vector `y` of the closed unit ball, namely at `‖w‖⁻¹ • w` (at `0` when
  `w = 0`).  Together with the Cauchy–Schwarz inequality this is the duality
  `‖w‖ = sup_{‖y‖ ≤ 1} ⟪y, w⟫_ℝ`.
-/

open scoped RealInnerProductSpace

/-- A vector of the closed unit ball at which the real inner product with `w` is at least the
norm of `w`. -/
theorem exists_norm_le_real_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) : ∃ y : E, ‖y‖ ≤ 1 ∧ ‖w‖ ≤ ⟪y, w⟫ := by
  by_cases hw : w = 0
  · exact ⟨0, by simp, by simp [hw]⟩
  · have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm, ← mul_assoc,
        inv_mul_cancel₀ hw0, one_mul]
