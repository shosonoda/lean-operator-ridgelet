import OperatorRidgelet.Transform.Defs

/-!
# Missing infrastructure for Section 3: Gaussian measures with a prescribed covariance

The manuscript realizes the Gaussian layers `𝒩(0,2sP)` by the Gaussian series
`X = ∑ √p_j Z_j e_j` (Appendix A).  Mathlib v4.32.0 has the class `ProbabilityTheory.IsGaussian`
but no constructor of a centred Gaussian measure with a prescribed trace-class covariance on an
infinite-dimensional Hilbert space.  The statement below records that gap: it is not a paper
item, and its proof is `sorry` until the construction is available.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Existence of the Gaussian layers `𝒩(0,2sP)`, `s > 0`, for an injective, positive,
self-adjoint, trace-class `P`: the Gaussian series construction of Appendix A. -/
theorem exists_isCenteredGaussianLayers (P : H →L[ℝ] H) (hP : IsTraceClassCovariance P) :
    ∃ N : ℝ → Measure H, IsCenteredGaussianLayers P N := by
  sorry

end OperatorRidgelet
