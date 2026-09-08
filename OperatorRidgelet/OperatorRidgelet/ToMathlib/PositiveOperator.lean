import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Injective positive operators are positive definite

If a bounded symmetric operator `T` on a real inner product space is positive,
`⟪T x, x⟫ ≥ 0`, and injective, then its quadratic form is positive definite:
`⟪T z, z⟫ > 0` for `z ≠ 0`.  The proof is the Cauchy–Schwarz inequality for the positive
semidefinite form `(x, y) ↦ ⟪T x, y⟫`, obtained from the discriminant of the quadratic
polynomial `t ↦ ⟪T (z + t y), z + t y⟫`.
-/

open scoped RealInnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric positive injective operator has a positive definite quadratic form. -/
theorem inner_map_self_pos_of_injective {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪T x, x⟫) (hinj : Function.Injective T) {z : E} (hz : z ≠ 0) :
    0 < ⟪T z, z⟫ := by
  rcases (hpos z).lt_or_eq with h | h
  · exact h
  exfalso
  apply hz
  apply hinj
  rw [map_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  have key : ∀ t : ℝ, 0 ≤ ⟪T (T z), T z⟫ * (t * t) + (2 * ⟪T z, T z⟫) * t + 0 := by
    intro t
    have h0 := hpos (z + t • T z)
    have h1 : ⟪T (T z), z⟫ = ⟪T z, T z⟫ := hT (T z) z
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      h1, ← h] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (2 * ⟪T z, T z⟫), real_inner_self_nonneg (x := T z)]

end LinearMap.IsSymmetric
