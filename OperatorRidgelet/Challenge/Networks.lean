import OperatorRidgelet.Network.Defs

/-!
# comparator challenge: Section 2 (networks with Hilbert-space inputs)

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Networks`.  This module
imports only definition modules, never `OperatorRidgelet.Paper`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Topology
open scoped ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Section 2: integral networks -/

/-- **Definition [def:2.2]** Integral network.  If `β` is globally Lipschitz and
`∫ (1 + ‖a‖ + |c|) d|Γ| < ∞`, then the Bochner integral defining `S_β[Γ](x)` exists for every
`x`. -/
theorem def_2_2_i [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hmom : Integrable (fun θ : H × ℝ => 1 + ‖θ.1‖ + |θ.2|) Γ.variation) (x : H) :
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) := by
  sorry

/-- **Definition [def:2.2]** Integral network.  For `Γ = γ λ` with a density `γ`
with respect to a σ-finite reference measure `λ`, the integral network `S_β[Γ]` is the Bochner
integral `S_β[γ](x) = ∫ β(⟪a, x⟫ + c) γ(a, c) λ(da, dc)`, whenever the latter exists. -/
theorem def_2_2_ii [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ}
    (hβ : Continuous β) (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (x : H)
    (hint : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) • γ θ) lam) :
    integralNetwork β (lam.withDensityᵥ γ) x = integralNetworkDensity β lam γ x := by
  sorry

end OperatorRidgelet.Paper
