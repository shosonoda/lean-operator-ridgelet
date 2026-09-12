import OperatorRidgelet.Reconstruction.Defs

/-! # Finite-order ray moments -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal

/-- A common scalar bound for the first `N` filter derivatives, or zero if none exists. -/
def finiteFilterDerivativeBound (ρ : SchwartzMap ℝ ℝ) (N : ℕ) : ℝ := by
  classical
  exact if h : ∃ B : ℝ, 0 ≤ B ∧
      ∀ j ≤ N, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B then h.choose else 0

/-- A coefficient decay constant depending only on the filter and derivative order. -/
def finiteCoefficientDecayConstant (ρ : SchwartzMap ℝ ℝ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ N * (1 + 2 ^ N) * ((2 * Real.pi)⁻¹ *
    ((volume (tsupport (filterFourier ρ))).toReal * finiteFilterDerivativeBound ρ N)) + 1)

/-- A coefficient moment constant independent of the input and output spaces and measures. -/
def finiteCoefficientMomentConstant (ρ : SchwartzMap ℝ ℝ) (r : ℕ) : ℝ≥0∞ :=
  finiteCoefficientDecayConstant ρ (r + 2) *
    ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The finite-order ray moment: `r` parameter powers and derivatives up to order `m`. -/
def finiteRayMoment (ν : Measure H) (I : Set ℝ) (G : H → Y) (m r : ℕ) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ r) * rayDerivBound I G m a ∂ν

end OperatorRidgelet
