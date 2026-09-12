import OperatorRidgelet.Reconstruction.Defs

/-! # Finite-order ray moments -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The finite-order ray moment: `r` parameter powers and derivatives up to order `m`. -/
def finiteRayMoment (ν : Measure H) (I : Set ℝ) (G : H → Y) (m r : ℕ) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ r) * rayDerivBound I G m a ∂ν

end OperatorRidgelet
