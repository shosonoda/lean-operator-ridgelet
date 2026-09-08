import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Rank-one operator lift

This realizes a vector parameter as the adjoint readout of a rank-one bounded operator.  It is
the operator-valued bridge used to lift scalar infinite-dimensional examples to operator learning.
-/

noncomputable section

namespace OperatorRidgelet

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The normalized rank-one operator whose adjoint sends `ψ` to `a`. -/
def rankOneLift (ψ a : H) : H →L[ℝ] H :=
  (‖ψ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ ψ a

theorem adjoint_rankOneLift_apply (ψ a : H) (hψ : ψ ≠ 0) :
    ContinuousLinearMap.adjoint (rankOneLift ψ a) ψ = a := by
  rw [rankOneLift, map_smul, InnerProductSpace.adjoint_rankOne]
  change (‖ψ‖ ^ 2)⁻¹ • (inner ℝ ψ ψ • a) = a
  rw [real_inner_self_eq_norm_sq, smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))]
  exact one_smul ℝ a

end OperatorRidgelet
