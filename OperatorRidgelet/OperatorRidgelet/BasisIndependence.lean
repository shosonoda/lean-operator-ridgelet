import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.ToMathlib.TraceBasisIndependent
import OperatorRidgelet.ToMathlib.FredholmDetEigenbasis

/-!
# The trace and Fredholm determinant are basis independent

The chosen values of `traceOf` and `fredholmDet` agree with the sum along every Hilbert
basis and the product along every orthonormal eigenbasis, respectively. The general
mathematics is in `ToMathlib.TraceBasisIndependent` and `ToMathlib.FredholmDetEigenbasis`.
-/

namespace OperatorRidgelet

open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The trace of a positive operator converges along every Hilbert basis as soon as it converges
along one of them. -/
theorem summable_trace_along {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) (hpos : ∀ x, 0 ≤ ⟪P x, x⟫)
    (h : HasSummableTrace P) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    Summable fun i => ⟪P (b i), b i⟫ :=
  ContinuousLinearMap.summable_inner_map_self_of_summable hP hpos b h.choose_spec.choose_spec

/-- **The trace is the sum along every Hilbert basis.**  The basis chosen in the definition of
`traceOf` is immaterial: for a positive self-adjoint operator with summable trace,
`traceOf P = ∑ ⟪P e_i, e_i⟫` along any Hilbert basis. -/
theorem traceOf_eq_traceAlong {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) (hpos : ∀ x, 0 ≤ ⟪P x, x⟫)
    (h : HasSummableTrace P) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    traceOf P = traceAlong b P := by
  rw [traceOf, dif_pos h]
  exact ContinuousLinearMap.tsum_inner_map_self_eq hP hpos h.choose_spec.choose b
    h.choose_spec.choose_spec

/-- **The Fredholm determinant is the product along every orthonormal eigenbasis.**  The basis
chosen in the definition of `fredholmDet` is immaterial: for a positive self-adjoint operator
with summable trace, `fredholmDet M = ∏ (1 + ⟪M e_i, e_i⟫)` along any orthonormal eigenbasis. -/
theorem fredholmDet_eq_fredholmDetAlong {M : H →L[ℝ] H} (hM : IsSelfAdjoint M)
    (hpos : ∀ x, 0 ≤ ⟪M x, x⟫) (htr : HasSummableTrace M)
    (hex : ∃ (κ : Type) (e' : HilbertBasis κ ℝ H) (w' : κ → ℝ), HasEigenbasis M e' w')
    {ι : Type*} {e : HilbertBasis ι ℝ H} {w : ι → ℝ} (he : HasEigenbasis M e w) :
    fredholmDet M = fredholmDetAlong e M := by
  rw [fredholmDet, dif_pos hex]
  exact ContinuousLinearMap.tprod_one_add_inner_eigen_eq hM hpos
    hex.choose_spec.choose_spec.choose_spec he
    (summable_trace_along hM hpos htr hex.choose_spec.choose)

end OperatorRidgelet
