import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Definitions for Section 2 (networks with Hilbert-space inputs)

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

* `finiteNetwork`: the width-`N` network `f_N(x) = ∑_j v_j β(⟪a_j, x⟫ + c_j)` of Definition
  `def:finite-network`.
* `integralNetwork`: the integral network `S_β[Γ](x) = ∫ β(⟪a, x⟫ + c) Γ(da, dc)` of Definition
  `def:integral-network`, together with `totalVariation` and the density form
  `integralNetworkDensity` (`S_β[γ]` for `Γ = γ λ`).
* `IsPolynomialFun`: the scalar activations excluded by the universality statements.

## Vector measures of bounded variation

A `Y`-valued Borel measure of bounded variation on `Θ = H × ℝ` is represented by a Mathlib
`MeasureTheory.VectorMeasure (H × ℝ) Y` (countably additive, `Y`-valued) whose variation measure
`Γ.variation` (`MeasureTheory.VectorMeasure.variation`, the supremum over finite measurable
partitions of `∑ ‖Γ Eᵢ‖`) is finite; the statements carry this as the hypothesis
`[IsFiniteMeasure Γ.variation]`.  The Bochner integral against `Γ` is Mathlib's
`MeasureTheory.VectorMeasure.integral` with the pairing `ContinuousLinearMap.lsmul ℝ ℂ`
(complex scalars acting on `Y`); it is `0` when the integrand is not integrable with respect to
`Γ.variation`, which encodes the manuscript's "whenever the Bochner integral exists".

The output space `Y` is a complex Banach space in the definitions; the manuscript's `Y` is a
separable complex Hilbert space, and the statements assume what they need.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Definition [def:finite-network]** The width-`N` network on `H` with values in `Y`,
`f_N(x) = ∑_{j} β(⟪a_j, x⟫ + c_j) • v_j`, with outer weights `v : Fin N → Y`, directions
`a : Fin N → H`, biases `c : Fin N → ℝ`, and scalar activation `β : ℝ → ℂ` (continuous in the
manuscript).  The scalar case is `Y = ℂ`. -/
def finiteNetwork {N : ℕ} (β : ℝ → ℂ) (v : Fin N → Y) (a : Fin N → H) (c : Fin N → ℝ)
    (x : H) : Y :=
  ∑ j, β (inner ℝ (a j) x + c j) • v j

/-- `β : ℝ → ℝ` is a polynomial: it is the evaluation of some `p : Polynomial ℝ`.  The
universality statements assume `¬ IsPolynomialFun β`. -/
def IsPolynomialFun (β : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, ∀ t, β t = p.eval t

section IntegralNetwork

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The total variation `‖Γ‖_TV = |Γ|(Θ)` of a vector measure `Γ`, in `ℝ≥0∞`. -/
def totalVariation (Γ : VectorMeasure Θ Y) : ℝ≥0∞ :=
  Γ.variation Set.univ

variable [MeasurableSpace H]

/-- **Definition [def:integral-network]** The integral network
`S_β[Γ](x) = ∫ β(⟪a, x⟫ + c) Γ(da, dc)` of a `Y`-valued measure `Γ` on `Θ = H × ℝ`, as the
vector-measure Bochner integral with complex scalars acting on `Y`; it is `0` when the integrand
is not integrable against `Γ.variation`. -/
def integralNetwork (β : ℝ → ℂ) (Γ : VectorMeasure (H × ℝ) Y) (x : H) : Y :=
  ∫ᵛ θ, β (inner ℝ θ.1 x + θ.2) ∂[ContinuousLinearMap.lsmul ℝ ℂ; Γ]

/-- The integral network `S_β[γ](x) = ∫ β(⟪a, x⟫ + c) γ(a, c) λ(da, dc)` of a coefficient
density `γ` with respect to a reference measure `λ` on `Θ = H × ℝ` (the manuscript's
`Γ = γ λ`), as a Bochner integral. -/
def integralNetworkDensity (β : ℝ → ℂ) (lam : Measure (H × ℝ)) (γ : H × ℝ → Y) (x : H) : Y :=
  ∫ θ, β (inner ℝ θ.1 x + θ.2) • γ θ ∂lam

end IntegralNetwork

end OperatorRidgelet
