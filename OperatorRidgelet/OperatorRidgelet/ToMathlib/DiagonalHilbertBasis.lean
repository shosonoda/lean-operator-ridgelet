import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Operators diagonal in a Hilbert basis -/

noncomputable section

open Topology
open scoped RealInnerProductSpace ENNReal

namespace HilbertBasis

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) {T : H →L[ℝ] H} {p : ι → ℝ}

/-- Applying a diagonal operator to the Hilbert expansion multiplies each coordinate. -/
theorem hasSum_map_of_eigen (hT : ∀ i, T (b i) = p i • b i) (x : H) :
    HasSum (fun i => (p i * ⟪b i, x⟫) • b i) (T x) := by
  convert! (b.hasSum_repr x).mapL T using 1
  ext i
  simp only [map_smul, hT, smul_smul, b.repr_apply_apply, mul_comm]

/-- The coordinate formula for an operator diagonal in an orthonormal basis. -/
theorem inner_map_of_eigen (hT : ∀ i, T (b i) = p i • b i) (x : H) (i : ι) :
    ⟪b i, T x⟫ = p i * ⟪b i, x⟫ := by
  classical
  have h := (b.hasSum_map_of_eigen hT x).mapL (innerSL ℝ (b i))
  simp only [innerSL_apply_apply] at h
  rw [← h.tsum_eq]
  simp only [real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp

/-- A real diagonal bounded operator is self-adjoint. -/
theorem isSelfAdjoint_of_eigen [CompleteSpace H]
    (hT : ∀ i, T (b i) = p i • b i) : IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪T x, y⟫ = ⟪x, T y⟫
  rw [← b.tsum_inner_mul_inner (T x) y, ← b.tsum_inner_mul_inner x (T y)]
  apply tsum_congr
  intro i
  rw [real_inner_comm (b i) (T x), b.inner_map_of_eigen hT, b.inner_map_of_eigen hT]
  rw [real_inner_comm (b i) x]
  ring

/-- Nonnegative diagonal eigenvalues give a nonnegative quadratic form. -/
theorem inner_map_self_nonneg_of_eigen (hT : ∀ i, T (b i) = p i • b i)
    (hp : ∀ i, 0 ≤ p i) (x : H) : 0 ≤ ⟪T x, x⟫ := by
  rw [← b.tsum_inner_mul_inner (T x) x]
  apply tsum_nonneg
  intro i
  rw [real_inner_comm (b i) (T x), b.inner_map_of_eigen hT]
  nlinarith [mul_nonneg (hp i) (sq_nonneg ⟪b i, x⟫)]

/-- A diagonal operator with no zero eigenvalue is injective. -/
theorem injective_of_eigen (hT : ∀ i, T (b i) = p i • b i) (hp : ∀ i, p i ≠ 0) :
    Function.Injective T := by
  intro x y hxy
  apply b.repr.injective
  ext i
  simp only [b.repr_apply_apply]
  apply mul_left_cancel₀ (hp i)
  rw [← b.inner_map_of_eigen hT, ← b.inner_map_of_eigen hT, hxy]

/-- The finite spectral truncation error is bounded by the largest omitted eigenvalue. -/
theorem norm_map_sub_sum_le (hT : ∀ i, T (b i) = p i • b i) (s : Finset ι)
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ i ∉ s, |p i| ≤ C) (x : H) :
    ‖T x - ∑ i ∈ s, (p i * ⟪b i, x⟫) • b i‖ ≤ C * ‖x‖ := by
  classical
  let z := T x - ∑ i ∈ s, (p i * ⟪b i, x⟫) • b i
  have hc (i : ι) : b.repr z i = if i ∈ s then 0 else p i * ⟪b i, x⟫ := by
    simp only [z, b.repr_apply_apply, inner_sub_right, b.inner_map_of_eigen hT,
      inner_sum, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    by_cases hi : i ∈ s <;> simp [hi]
  have hn : ‖b.repr z‖ ≤ ‖C • b.repr x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    rw [hc]
    by_cases hi : i ∈ s
    · rw [if_pos hi, norm_zero]
      exact norm_nonneg _
    · simp only [if_neg hi, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, b.repr_apply_apply]
      exact mul_le_mul_of_nonneg_right (hp i hi) (abs_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hC] using hn

end HilbertBasis
