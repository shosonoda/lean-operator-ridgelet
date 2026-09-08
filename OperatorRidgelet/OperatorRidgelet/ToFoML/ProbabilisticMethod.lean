import Mathlib.MeasureTheory.Integral.Average

/-!
# First-moment sample selection

This is the probabilistic-method step in a Monte Carlo discretization: once the expected error is
bounded, at least one finite realization has no larger error.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_realization_le_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (error : Ω → ℝ) (herror : Integrable error μ) :
    ∃ ω, error ω ≤ ∫ x, error x ∂μ := by
  exact MeasureTheory.exists_le_integral herror

end OperatorRidgelet
