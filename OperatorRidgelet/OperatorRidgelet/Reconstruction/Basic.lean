import OperatorRidgelet.Reconstruction.Defs

/-!
# Auxiliary lemmas for Section 4 (representation and reconstruction)

Elementary facts about the anti-dual representation of `𝓔_α'` used by the proofs in
`OperatorRidgelet.Paper.Reconstruction`: the functional `innerSLFlip ℂ x` has norm `‖x‖`, and
the inverse Riesz map `rieszInv` is a right inverse of the Riesz map `rieszMap`.  This module is
not imported by `Challenge`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

/-- The conjugate-linear functional `y ↦ ⟪y, x⟫` has norm `‖x‖`. -/
theorem norm_innerSLFlip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    ‖innerSLFlip ℂ x‖ = ‖x‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => ?_) ?_
  · rw [innerSLFlip_apply_apply]
    exact (norm_inner_le_norm y x).trans (le_of_eq (mul_comm _ _))
  · by_cases hx : x = 0
    · simp [hx]
    · have h1 : ‖innerSLFlip ℂ x x‖ ≤ ‖innerSLFlip ℂ x‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      simp only [innerSLFlip_apply_apply, inner_self_eq_norm_sq_to_K, norm_pow,
        RCLike.norm_ofReal, abs_norm] at h1
      rw [sq] at h1
      exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hx)

/-- The Riesz representation: `innerSLFlip ℂ` applied to the vector representing a continuous
conjugate-linear functional gives the functional back. -/
theorem innerSLFlip_toDual_symm_antiDualConj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F : E →L⋆[ℂ] ℂ) :
    innerSLFlip ℂ ((InnerProductSpace.toDual ℂ E).symm (antiDualConj F)) = F := by
  ext g
  rw [innerSLFlip_apply_apply, ← inner_conj_symm, InnerProductSpace.toDual_symm_apply,
    antiDualConj_apply, Complex.conj_conj]

/-- `innerSLFlip ℂ` is injective. -/
theorem innerSLFlip_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Function.Injective (innerSLFlip ℂ : E →L[ℂ] E →L⋆[ℂ] ℂ) := by
  intro f g hfg
  apply ext_inner_left ℂ
  intro h
  have := congrArg (fun T : E →L⋆[ℂ] ℂ => T h) hfg
  simpa [innerSLFlip_apply_apply] using this

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- `J (J⁻¹ F) = F`. -/
theorem rieszMap_rieszInv (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDual μ ν) :
    rieszMap μ ν (rieszInv μ ν F) = F :=
  innerSLFlip_toDual_symm_antiDualConj F

/-- `J (J⁻¹ F) = F` for `Y`-valued targets. -/
theorem rieszMapVec_rieszInvVec {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDualVec Y μ ν) :
    rieszMapVec Y μ ν (rieszInvVec μ ν F) = F :=
  innerSLFlip_toDual_symm_antiDualConj F

end

end OperatorRidgelet
