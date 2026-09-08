import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Transform.Gaussian

/-!
# Infrastructure for Section 3: Gaussian measures with a prescribed covariance

The manuscript realizes the Gaussian layers `𝒩(0,2sP)` by the Gaussian series
`X = ∑ √p_j Z_j e_j` (Appendix A).  Mathlib v4.32.0 has the class `ProbabilityTheory.IsGaussian`
but no constructor of a centred Gaussian measure with a prescribed trace-class covariance on an
infinite-dimensional Hilbert space; the construction is carried out in
`OperatorRidgelet.ToMathlib.TraceClassEigenbasis` (the eigenbasis of `P`),
`OperatorRidgelet.ToMathlib.GaussianHilbert` (the Gaussian series), and
`OperatorRidgelet.Transform.Gaussian` (the layers).  The statement below records the result; it
is not a paper item.
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
  obtain ⟨μ, hμ⟩ := hP.exists_isCenteredGaussian
  exact ⟨_, hμ.isCenteredGaussianLayers_map_smul⟩

end OperatorRidgelet
