import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Countability and integral norm identities for Hilbert bases -/

noncomputable section
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal

variable {ι E 𝕜 Ω : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An orthonormal family in a separable Hilbert space has countable index type. -/
theorem Orthonormal.countable_index [SeparableSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 2 : ℝ))
      (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    have hn : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq 𝕜, hv.norm_eq_one, hv.norm_eq_one, hv.inner_eq_zero hij]
      norm_num
    have ht := dist_triangle (v i) x (v j)
    have hx' : dist (v i) x < 1 / 2 := by simpa [dist_comm] using hx
    have hy' : dist x (v j) < 1 / 2 := hy
    have hb : ‖v i - v j‖ < 1 := by rw [← dist_eq_norm]; linarith
    nlinarith [norm_nonneg (v i - v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- Parseval's norm identity in the extended nonnegative reals. -/
theorem HilbertBasis.tsum_enorm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖inner 𝕜 (b i) x‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  have hs : HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map,
      b.repr_apply_apply] using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr x)
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]

/-- The integral of the squared norm is the sum of the integrals of squared coordinates. -/
theorem HilbertBasis.lintegral_enorm_sq [Countable ι] [MeasurableSpace Ω]
    (b : HilbertBasis ι 𝕜 E) {f : Ω → E} {μ : Measure Ω} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∑' i, ∫⁻ x, ‖inner 𝕜 (b i) (f x)‖ₑ ^ 2 ∂μ := by
  simp_rw [← b.tsum_enorm_inner_sq]
  exact lintegral_tsum fun i => (hf.const_inner (𝕜 := 𝕜) (c := b i)).enorm.pow_const 2
