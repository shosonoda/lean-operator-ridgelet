import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Network.Basic
import OperatorRidgelet.ToMathlib.VectorMeasureWithDensity

/-!
# Statements of Section 2 (Hilbert-space inputs)

Each item is `theorem OperatorRidgelet.Paper.<kind>_<number>[_<part>]`, identical to its twin in
`Challenge.Networks`, and proved from the library.

The ambient space `H` is a real Hilbert space; the manuscript's separability, Borel structure,
and the output Hilbert space `Y` enter as explicit instance hypotheses where the statement uses
them.  Vector measures of bounded variation are `MeasureTheory.VectorMeasure` with finite
`variation` (see `OperatorRidgelet.Network.Defs`).
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
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) :=
  integrable_ridge_of_lipschitz hβ Γ hmom x

/-- **Definition [def:2.2]** Integral network.  For `Γ = γ λ` with a density `γ`
with respect to a σ-finite reference measure `λ`, the integral network `S_β[Γ]` is the Bochner
integral `S_β[γ](x) = ∫ β(⟪a, x⟫ + c) γ(a, c) λ(da, dc)`, whenever the latter exists. -/
theorem def_2_2_ii [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y] {β : ℝ → ℂ}
    (hβ : Continuous β) (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (x : H)
    (hint : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) • γ θ) lam) :
    integralNetwork β (lam.withDensityᵥ γ) x = integralNetworkDensity β lam γ x := by
  unfold integralNetwork integralNetworkDensity
  have hmeas : AEStronglyMeasurable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2)) lam :=
    (hβ.comp (by fun_prop : Continuous fun θ : H × ℝ => inner ℝ θ.1 x + θ.2)).aestronglyMeasurable
  have hf : Integrable (fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2))
      (lam.withDensity fun θ => ‖γ θ‖ₑ) := by
    refine (integrable_withDensity_iff_integrable_coe_smul₀
      hγ.aestronglyMeasurable.nnnorm.aemeasurable).mpr ?_
    refine hint.norm.mono' (hγ.aestronglyMeasurable.norm.smul hmeas)
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [norm_smul, norm_smul, coe_nnnorm, Real.norm_eq_abs, abs_norm, mul_comm]
  rw [VectorMeasure.integral_withDensityᵥ hγ hf]
  rfl

end OperatorRidgelet.Paper
