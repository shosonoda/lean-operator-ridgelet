import OperatorRidgelet.Transform.Gaussian

/-! # Gaussian invariance and ridgelet transforms under linear isometries -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory
section Gaussian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
open scoped RealInnerProductSpace
open ProbabilityTheory

/-- An isometry commuting with the covariance preserves the centered Gaussian measure. -/
theorem IsCenteredGaussian.measurePreserving_isometry {Q : H →L[ℝ] H} {μ : Measure H}
    (hμ : IsCenteredGaussian Q μ) (U : H ≃ₗᵢ[ℝ] H)
    (hcomm : ∀ x, Q (U x) = U (Q x)) : MeasurePreserving U μ μ := by
  haveI := hμ.isProbabilityMeasure
  refine ⟨U.continuous.measurable, ?_⟩
  apply IsCenteredGaussian.unique _ hμ
  refine ⟨Measure.isProbabilityMeasure_map U.continuous.measurable.aemeasurable, fun ξ => ?_⟩
  have hinner (x : H) : ⟪U x, ξ⟫ = ⟪x, U.symm ξ⟫ := by
    simpa using U.inner_map_map x (U.symm ξ)
  rw [charFun_apply, integral_map U.continuous.measurable.aemeasurable (by fun_prop)]
  simp_rw [hinner]
  change charFun μ (U.symm ξ) = _
  rw [hμ.charFun_eq]
  have he : ⟪Q (U.symm ξ), U.symm ξ⟫ = ⟪Q ξ, ξ⟫ := by
    rw [← U.inner_map_map, ← hcomm, U.apply_symm_apply]
  rw [he]

/-- The Gaussian ridgelet transform intertwines a covariance-preserving isometry. -/
theorem ridgelet_comp_isometry (μ : Measure H) (U : H ≃ₗᵢ[ℝ] H)
    (hU : MeasurePreserving U μ μ) (ρ : ℝ → ℝ) (f : H → ℂ) (p : H × ℝ) :
    ridgelet μ ρ (fun x => f (U x)) p = ridgelet μ ρ f (U p.1, p.2) := by
  unfold ridgelet
  rw [← hU.integral_comp U.toHomeomorph.measurableEmbedding
    (fun x => f x * (ρ (⟪U p.1, x⟫ + p.2) : ℂ))]
  simp only [U.inner_map_map]
end Gaussian

end OperatorRidgelet
