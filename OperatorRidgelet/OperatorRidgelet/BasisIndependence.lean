import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Architecture.Defs
import OperatorRidgelet.ToMathlib.TraceBasisIndependent
import OperatorRidgelet.ToMathlib.FredholmDetEigenbasis
import OperatorRidgelet.ToMathlib.HilbertSchmidtBasis

/-!
# The trace, the Fredholm determinant, and the Hilbert–Schmidt norm are basis independent

The trace `traceOf P` and the Fredholm determinant `fredholmDet M` are defined by choosing a
Hilbert basis, respectively an orthonormal eigenbasis, with `Classical.choice`, and the squared
Hilbert–Schmidt norm `hsNormSq A` is defined intrinsically as a supremum over finite orthonormal
families.  This module discharges the resulting fidelity obligations:

* `OperatorRidgelet.summable_trace_along`: `HasSummableTrace` does not depend on the basis;
* `OperatorRidgelet.traceOf_eq_traceAlong`: the chosen value `traceOf P` is the sum
  `∑ ⟪P e_i, e_i⟫` along *every* Hilbert basis;
* `OperatorRidgelet.fredholmDet_eq_fredholmDetAlong`: the chosen value `fredholmDet M` is the
  product `∏ (1 + ⟪M e_i, e_i⟫)` along *every* orthonormal eigenbasis;
* `OperatorRidgelet.hsNormSq_eq_tsum` and `OperatorRidgelet.hsNorm_eq_sqrt_tsum`: the intrinsic
  Hilbert–Schmidt norm is the sum `∑ ‖A e_i‖²` along every Hilbert basis.

The mathematics is in `OperatorRidgelet.ToMathlib.TraceBasisIndependent`,
`OperatorRidgelet.ToMathlib.FredholmDetEigenbasis` and
`OperatorRidgelet.ToMathlib.HilbertSchmidtBasis`.
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

/-- **The Hilbert–Schmidt norm is the sum along every Hilbert basis.**  The intrinsic definition
of `hsNormSq` as a supremum over finite orthonormal families is computed by `∑ ‖A e_i‖²` along
any Hilbert basis. -/
theorem hsNormSq_eq_tsum (A : H →L[ℝ] H) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    hsNormSq A = ∑' i, ‖A (b i)‖ₑ ^ 2 :=
  ContinuousLinearMap.iSup_finset_sum_enorm_apply_sq A b

/-- The Hilbert–Schmidt norm as a real number, along any Hilbert basis. -/
theorem hsNorm_eq_sqrt_tsum (A : H →L[ℝ] H) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    hsNorm A = Real.sqrt (∑' i, ‖A (b i)‖ₑ ^ 2).toReal := by
  rw [hsNorm, hsNormSq_eq_tsum A b]

end OperatorRidgelet
