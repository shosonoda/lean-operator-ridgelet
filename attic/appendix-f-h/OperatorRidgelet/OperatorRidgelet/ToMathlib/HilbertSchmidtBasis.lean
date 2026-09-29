import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The Hilbert–Schmidt norm along a Hilbert basis

The squared Hilbert–Schmidt norm of a bounded operator `A` on a real Hilbert space can be
defined intrinsically as the supremum of `∑_{e ∈ s} ‖A e‖²` over the finite orthonormal
subsets `s ⊆ H`, or as the sum `∑_i ‖A e_i‖²` along a Hilbert basis.  This file proves that the
two agree, so that the intrinsic definition may be computed along any Hilbert basis:

* `ContinuousLinearMap.tsum_ofReal_norm_apply_sq_eq_adjoint`: `∑_i ‖A b_i‖² = ∑_m ‖A* c_m‖²` for
  any two Hilbert bases `b` and `c` (double Parseval);
* `ContinuousLinearMap.tsum_ofReal_norm_apply_sq_eq`: the sum `∑_i ‖A b_i‖²` does not depend on
  the Hilbert basis `b`;
* `ContinuousLinearMap.iSup_finset_sum_enorm_apply_sq`: the supremum over finite orthonormal
  subsets equals `∑_i ‖A b_i‖²`.

All sums are taken in `ℝ≥0∞`, so no summability hypothesis is needed.
-/

open scoped RealInnerProductSpace ENNReal

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι κ : Type*}

omit [CompleteSpace H] in
/-- Parseval's identity in `ℝ≥0∞`: `∑_i ⟪b_i, x⟫² = ‖x‖²` along a Hilbert basis `b`. -/
theorem tsum_ofReal_inner_sq (b : HilbertBasis ι ℝ H) (x : H) :
    ∑' i, ENNReal.ofReal (⟪b i, x⟫ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  have hfun : (fun i => ⟪x, b i⟫ * ⟪b i, x⟫) = fun i => ⟪b i, x⟫ ^ 2 := by
    funext i
    rw [real_inner_comm x (b i), sq]
  rw [hfun] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable, h.tsum_eq]

/-- Double Parseval: the Hilbert–Schmidt sum of `A` along a Hilbert basis `b` equals the
Hilbert–Schmidt sum of the adjoint `A*` along any Hilbert basis `c`. -/
theorem tsum_ofReal_norm_apply_sq_eq_adjoint (A : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (c : HilbertBasis κ ℝ H) :
    ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) = ∑' m, ENNReal.ofReal (‖adjoint A (c m)‖ ^ 2) := by
  have h1 : ∀ i, ENNReal.ofReal (‖A (b i)‖ ^ 2)
      = ∑' m, ENNReal.ofReal (⟪b i, adjoint A (c m)⟫ ^ 2) := by
    intro i
    rw [← tsum_ofReal_inner_sq c (A (b i))]
    refine tsum_congr fun m => ?_
    rw [adjoint_inner_right, real_inner_comm]
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun m => tsum_ofReal_inner_sq b (adjoint A (c m))

/-- The Hilbert–Schmidt sum `∑_i ‖A e_i‖²` does not depend on the Hilbert basis `e`. -/
theorem tsum_ofReal_norm_apply_sq_eq (A : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (c : HilbertBasis κ ℝ H) :
    ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) = ∑' m, ENNReal.ofReal (‖A (c m)‖ ^ 2) := by
  rw [tsum_ofReal_norm_apply_sq_eq_adjoint A b c, ← tsum_ofReal_norm_apply_sq_eq_adjoint A c c]

/-- The intrinsic squared Hilbert–Schmidt norm, the supremum of `∑_{e ∈ s} ‖A e‖²` over the
finite orthonormal subsets `s ⊆ H`, is computed by the sum along any Hilbert basis. -/
theorem iSup_finset_sum_enorm_apply_sq (A : H →L[ℝ] H) (b : HilbertBasis ι ℝ H) :
    (⨆ (s : Finset H) (_ : Orthonormal ℝ ((↑) : s → H)), ∑ e ∈ s, ‖A e‖ₑ ^ 2)
      = ∑' i, ‖A (b i)‖ₑ ^ 2 := by
  classical
  have hsq : ∀ y : H, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
    rw [ENNReal.ofReal_pow (norm_nonneg y), ofReal_norm]
  refine le_antisymm ?_ ?_
  · -- Bessel's inequality for a finite orthonormal family, applied to the adjoint
    refine iSup_le fun s => iSup_le fun hs => ?_
    have hterm : ∀ e : H, ‖A e‖ₑ ^ 2 = ∑' i, ENNReal.ofReal (⟪adjoint A (b i), e⟫ ^ 2) := by
      intro e
      rw [hsq, ← tsum_ofReal_inner_sq b (A e)]
      exact tsum_congr fun i => by rw [adjoint_inner_left]
    calc ∑ e ∈ s, ‖A e‖ₑ ^ 2
        = ∑ e ∈ s, ∑' i, ENNReal.ofReal (⟪adjoint A (b i), e⟫ ^ 2) :=
          Finset.sum_congr rfl fun e _ => hterm e
      _ = ∑' i, ∑ e ∈ s, ENNReal.ofReal (⟪adjoint A (b i), e⟫ ^ 2) := by
          rw [← Finset.tsum_subtype s fun e => ∑' i, ENNReal.ofReal (⟪adjoint A (b i), e⟫ ^ 2),
            ENNReal.tsum_comm]
          exact tsum_congr fun i =>
            Finset.tsum_subtype s fun e => ENNReal.ofReal (⟪adjoint A (b i), e⟫ ^ 2)
      _ ≤ ∑' i, ENNReal.ofReal (‖adjoint A (b i)‖ ^ 2) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _]
          refine ENNReal.ofReal_le_ofReal ?_
          have hb := hs.sum_inner_products_le (s := Finset.univ) (adjoint A (b i))
          refine le_trans (le_of_eq ?_) hb
          rw [← Finset.sum_coe_sort s fun e => ⟪adjoint A (b i), e⟫ ^ 2]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Real.norm_eq_abs, sq_abs, real_inner_comm]
      _ = ∑' i, ‖A (b i)‖ₑ ^ 2 := by
          rw [← tsum_ofReal_norm_apply_sq_eq_adjoint A b b]
          exact tsum_congr fun i => (hsq _).symm
  · -- the finite subsets of the basis are orthonormal
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hinj : Function.Injective b := b.orthonormal.linearIndependent.injective
    have horth : Orthonormal ℝ ((↑) : ↥(F.image b) → H) := by
      rw [orthonormal_iff_ite]
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨j, -, rfl⟩ := hy
      have hij := (orthonormal_iff_ite.mp b.orthonormal) i j
      by_cases h : i = j
      · subst h
        simpa using hij
      · rw [if_neg h] at hij
        rw [hij, if_neg]
        simpa [Subtype.ext_iff] using fun hc => h (hinj hc)
    calc ∑ i ∈ F, ‖A (b i)‖ₑ ^ 2
        = ∑ e ∈ F.image b, ‖A e‖ₑ ^ 2 := by
          rw [Finset.sum_image fun x _ y _ h => hinj h]
      _ ≤ ⨆ (s : Finset H) (_ : Orthonormal ℝ ((↑) : s → H)), ∑ e ∈ s, ‖A e‖ₑ ^ 2 :=
          le_iSup_of_le (F.image b) (le_iSup_of_le horth le_rfl)

end ContinuousLinearMap
