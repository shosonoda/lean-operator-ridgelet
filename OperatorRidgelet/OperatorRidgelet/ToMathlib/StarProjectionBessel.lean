import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bessel's inequality for the orthogonal projection onto a finite-dimensional subspace

For a finite-dimensional subspace `K` of a real inner product space and a finite orthonormal
family `v`, `∑_i ‖P_K (v i)‖² ≤ dim K`: expanding `P_K (v i)` in an orthonormal basis of `K`
and applying Bessel's inequality to each basis vector.
-/

open scoped RealInnerProductSpace

namespace Orthonormal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of the orthogonal projection onto a finite-dimensional subspace, expanded
in an orthonormal basis of the subspace. -/
theorem _root_.Submodule.norm_sq_starProjection_eq_sum (K : Submodule ℝ E)
    [FiniteDimensional ℝ K] (x : E) :
    ‖K.starProjection x‖ ^ 2 =
      ∑ j, ⟪((stdOrthonormalBasis ℝ K j : K) : E), x⟫ ^ 2 := by
  set b := stdOrthonormalBasis ℝ K
  set y : K := ⟨K.starProjection x, K.starProjection_apply_mem x⟩ with hy
  have h1 : ‖K.starProjection x‖ ^ 2 = ∑ j, ⟪(b j : E), K.starProjection x⟫ ^ 2 := by
    have h := b.sum_inner_mul_inner y y
    rw [real_inner_self_eq_norm_sq] at h
    have hn : ‖y‖ = ‖K.starProjection x‖ := rfl
    rw [hn] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm y (b j), ← sq, Submodule.coe_inner, real_inner_comm]
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h2 := K.starProjection_inner_eq_zero x (b j) (b j).2
  rw [inner_sub_left, sub_eq_zero] at h2
  rw [real_inner_comm, ← h2, real_inner_comm]

/-- Bessel's inequality for a projection: `∑_i ‖P_K (v i)‖² ≤ dim K` for a finite orthonormal
family `v`. -/
theorem sum_norm_sq_starProjection_le (K : Submodule ℝ E) [FiniteDimensional ℝ K] {v : ι → E}
    (hv : Orthonormal ℝ v) (s : Finset ι) :
    ∑ i ∈ s, ‖K.starProjection (v i)‖ ^ 2 ≤ Module.finrank ℝ K := by
  simp_rw [Submodule.norm_sq_starProjection_eq_sum]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i ∈ s, ⟪((stdOrthonormalBasis ℝ K j : K) : E), v i⟫ ^ 2
      ≤ ∑ j : Fin (Module.finrank ℝ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := hv.sum_inner_products_le (s := s) (x := ((stdOrthonormalBasis ℝ K j : K) : E))
        have hn : ‖((stdOrthonormalBasis ℝ K j : K) : E)‖ = 1 := by
          rw [Submodule.norm_coe]
          exact (stdOrthonormalBasis ℝ K).orthonormal.1 j
        rw [hn, one_pow] at h
        refine le_trans (le_of_eq ?_) h
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs, real_inner_comm]
    _ = Module.finrank ℝ K := by simp

end Orthonormal
