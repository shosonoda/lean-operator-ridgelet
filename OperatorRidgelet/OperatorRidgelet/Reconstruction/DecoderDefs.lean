import OperatorRidgelet.Reconstruction.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The bounded coefficient decoder -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The coefficient decoder, the scaled Hilbert adjoint of the extended transform. -/
def coefficientDecoder (α : ℝ) (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) :
    Lp ℂ 2 (parameterMeasure ν) →L[ℂ] spectralRange μ ν :=
  ((admissibilityConst α ρ : ℂ)⁻¹) • (ridgeletExtension μ ν ρ).adjoint

end OperatorRidgelet
