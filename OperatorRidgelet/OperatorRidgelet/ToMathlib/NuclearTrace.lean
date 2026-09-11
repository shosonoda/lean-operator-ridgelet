import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Positive operators defined by summable weighted rank-one series -/

noncomputable section
open scoped RealInnerProductSpace
open InnerProductSpace
namespace ContinuousLinearMap
variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem summable_weighted_rankOne {p : ι → ℝ} {v : ι → H}
    (hp : ∀ i, 0 ≤ p i) (hs : Summable fun i => p i * ‖v i‖^2) :
    Summable (fun i => p i • rankOne ℝ (v i) (v i)) := by
  apply Summable.of_norm
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp _), norm_rankOne, pow_two] using hs

theorem hasSum_inner_weighted_rankOne {p : ι → ℝ} {v : ι → H}
    (hp : ∀ i, 0 ≤ p i) (hs : Summable fun i => p i * ‖v i‖^2) (x y : H) :
    HasSum (fun i => p i * ⟪v i,x⟫ * ⟪v i,y⟫)
      ⟪(∑' i, p i • rankOne ℝ (v i) (v i)) x, y⟫ := by
  have h := ((summable_weighted_rankOne hp hs).hasSum.mapL
    (ContinuousLinearMap.apply ℝ H x)).mapL (innerSL ℝ y)
  simpa only [ContinuousLinearMap.apply_apply, innerSL_apply_apply, smul_apply,
    rankOne_apply, real_inner_smul_right, real_inner_comm, mul_assoc] using h

theorem isSelfAdjoint_tsum_weighted_rankOne {p : ι → ℝ} {v : ι → H}
    (hp : ∀ i, 0 ≤ p i) (hs : Summable fun i => p i * ‖v i‖^2) :
    IsSelfAdjoint (∑' i, p i • rankOne ℝ (v i) (v i)) := by
  apply isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  conv_rhs => rw [real_inner_comm]
  apply HasSum.unique (hasSum_inner_weighted_rankOne hp hs x y)
  convert! hasSum_inner_weighted_rankOne hp hs y x using 1
  ext i
  ring

theorem inner_tsum_weighted_rankOne_nonneg {p : ι → ℝ} {v : ι → H}
    (hp : ∀ i, 0 ≤ p i) (hs : Summable fun i => p i * ‖v i‖^2) (x : H) :
    0 ≤ ⟪(∑' i, p i • rankOne ℝ (v i) (v i)) x,x⟫ := by
  rw [← (hasSum_inner_weighted_rankOne hp hs x x).tsum_eq]
  apply tsum_nonneg
  intro i
  nlinarith [hp i, sq_nonneg ⟪v i,x⟫, mul_nonneg (hp i) (sq_nonneg ⟪v i,x⟫)]

theorem summable_inner_tsum_weighted_rankOne {p : ι → ℝ} {v : ι → H}
    (hp : ∀ i, 0 ≤ p i) (hs : Summable fun i => p i * ‖v i‖^2)
    (b : HilbertBasis κ ℝ H) :
    Summable (fun j => ⟪(∑' i, p i • rankOne ℝ (v i) (v i)) (b j), b j⟫) := by
  have hrow (i : ι) : HasSum (fun j => p i * ⟪v i,b j⟫ * ⟪v i,b j⟫)
      (p i * ‖v i‖^2) := by
    have h := (b.hasSum_inner_mul_inner (v i) (v i)).mul_left (p i)
    simpa only [real_inner_comm, inner_self_eq_norm_sq_to_K, mul_assoc] using! h
  have hn (a : ι × κ) : 0 ≤ p a.1 * ⟪v a.1,b a.2⟫ * ⟪v a.1,b a.2⟫ := by
    nlinarith [mul_nonneg (hp a.1) (sq_nonneg ⟪v a.1,b a.2⟫)]
  have hdouble : Summable (fun a : ι × κ => p a.1 * ⟪v a.1,b a.2⟫ * ⟪v a.1,b a.2⟫) := by
    apply (summable_prod_of_nonneg hn).mpr
    refine ⟨fun i => (hrow i).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using hs
  have hcol := hdouble.prod_symm.prod
  convert! hcol using 1
  ext j
  exact (hasSum_inner_weighted_rankOne hp hs (b j) (b j)).tsum_eq.symm
end ContinuousLinearMap

namespace ContinuousLinearMap

theorem summable_weight_norm_sq {ι H : Type*} [NormedAddCommGroup H]
    {p : ι → ℝ} {v : ι → H} (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (hv : ∀ i, ‖v i‖ ≤ 1) : Summable (fun i => p i * ‖v i‖^2) := by
  apply hs.of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp i) (sq_nonneg _))]
  apply mul_le_of_le_one_right (hp i)
  nlinarith [norm_nonneg (v i), hv i]

end ContinuousLinearMap
