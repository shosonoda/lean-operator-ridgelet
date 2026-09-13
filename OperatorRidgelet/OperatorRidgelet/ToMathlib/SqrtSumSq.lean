import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# The `ℓ²` triangle inequality for finite families of reals

* `Real.sqrt_sum_sq_add_le`: `√(∑ᵢ (aᵢ + bᵢ)²) ≤ √(∑ᵢ aᵢ²) + √(∑ᵢ bᵢ²)`, the triangle
  inequality of `EuclideanSpace ℝ (Fin N)` written with square roots of sums of squares.
-/

/-- The `ℓ²` triangle inequality: `√(∑ᵢ (aᵢ + bᵢ)²) ≤ √(∑ᵢ aᵢ²) + √(∑ᵢ bᵢ²)`. -/
theorem Real.sqrt_sum_sq_add_le {N : ℕ} (a b : Fin N → ℝ) :
    Real.sqrt (∑ j, (a j + b j) ^ 2) ≤
      Real.sqrt (∑ j, a j ^ 2) + Real.sqrt (∑ j, b j ^ 2) := by
  have hnorm : ∀ c : Fin N → ℝ,
      ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin N))‖ = Real.sqrt (∑ j, c j ^ 2) := by
    intro c
    rw [EuclideanSpace.norm_eq]
    exact congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs, sq_abs])
  have h := norm_add_le (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 b)
  rwa [← WithLp.toLp_add, hnorm, hnorm, hnorm] at h
