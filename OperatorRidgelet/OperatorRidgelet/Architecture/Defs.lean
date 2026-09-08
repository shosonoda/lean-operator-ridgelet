import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.CompactOpen
import OperatorRidgelet.Network.Defs
import OperatorRidgelet.OperatorValuedRidgelet

/-!
# Definitions for the operator-valued architecture (Section 2.2 and Appendix F)

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

* Hilbert–Schmidt operators: `hsNormSq`, `IsHilbertSchmidt`, `hsNorm`.
* The operator neuron `n_{ℓ,A,b}(x) = ⟪ℓ, σ(A x + b)⟫` (`operatorNeuron`), the sets of neurons
  with operator parameter in a given set (`operatorNeuronSet`), and the real scalar ridges
  (`ridgeSet`), all as subsets of `C(H, ℝ)` with its compact-open topology, which is the topology
  of uniform convergence on compact sets.
* The rank-one activation `σ_β(y) = β(⟪ψ, y⟫) z` (`rankOneActivation`).
* The operator syntheses `S_op Γ_op(x) = ∫ n_{ℓ,A,b}(x) Γ_op(dA, db)` (`operatorSynthesis`) and
  the finite-width operator network (`operatorFiniteNetwork`).

The parameter projection `π_ψ(A, b) = (A^* ψ, ⟪ψ, b⟫)` and the rank-one section
`J_ψ(a, c) = (A_a, b_c)` are `operatorParameterMap ψ` and `operatorRidgeletSection ψ` of
`OperatorRidgelet.OperatorValuedRidgelet`, with `A_a = rankOneLift ψ a` and
`b_c = biasLift ψ c`.

## Hilbert–Schmidt operators

Mathlib has no Hilbert–Schmidt class.  The squared Hilbert–Schmidt norm is defined here
intrinsically, as the supremum over finite orthonormal families `s` of `∑_{e ∈ s} ‖A e‖²`, so
that no choice of orthonormal basis enters the definition; that it equals `∑_n ‖A e_n‖²` for
every Hilbert basis `(e_n)` is a later proof obligation, not needed for the statements.  The
space `𝓛₂(H)` of the manuscript is the set `{A | IsHilbertSchmidt A}` of bounded operators, with
the Borel structure inherited from the operator norm.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Hilbert–Schmidt operators -/

/-- The squared Hilbert–Schmidt norm `‖A‖²_{𝓛₂}` of a bounded operator, in `ℝ≥0∞`: the
supremum over finite orthonormal families `s ⊆ H` of `∑_{e ∈ s} ‖A e‖²`. -/
def hsNormSq (A : H →L[ℝ] H) : ℝ≥0∞ :=
  ⨆ (s : Finset H) (_ : Orthonormal ℝ ((↑) : s → H)), ∑ e ∈ s, ‖A e‖ₑ ^ 2

/-- `A ∈ 𝓛₂(H)`: the bounded operator `A` is Hilbert–Schmidt. -/
def IsHilbertSchmidt (A : H →L[ℝ] H) : Prop :=
  hsNormSq A ≠ ∞

/-- The Hilbert–Schmidt norm `‖A‖_{𝓛₂}` as a real number; it is `0` (junk) when `A` is not
Hilbert–Schmidt. -/
def hsNorm (A : H →L[ℝ] H) : ℝ :=
  Real.sqrt (hsNormSq A).toReal

/-! ## Operator neurons -/

/-- The operator neuron `n_{ℓ,A,b}(x) = ⟪ℓ, σ(A x + b)⟫` with activation `σ : H → H`, readout
`ℓ`, operator parameter `A`, and bias `b`. -/
def operatorNeuron (σ : H → H) (ℓ : H) (A : H →L[ℝ] H) (b : H) (x : H) : ℝ :=
  inner ℝ ℓ (σ (A x + b))

/-- The continuous operator neurons `n_{ℓ,A,b}` with operator parameter `A ∈ P`, as a subset of
`C(H, ℝ)`; `P = Set.univ` is `𝓛(H)` and `P = {A | IsHilbertSchmidt A}` is `𝓛₂(H)`. -/
def operatorNeuronSet (σ : H → H) (P : Set (H →L[ℝ] H)) : Set C(H, ℝ) :=
  {f | ∃ ℓ b : H, ∃ A ∈ P, ⇑f = operatorNeuron σ ℓ A b}

/-- The continuous real ridge functions `x ↦ β(⟪a, x⟫ + c)` with `(a, c) ∈ H × ℝ`, as a subset
of `C(H, ℝ)`. -/
def ridgeSet (β : ℝ → ℝ) : Set C(H, ℝ) :=
  {f | ∃ (a : H) (c : ℝ), ⇑f = fun x => β (inner ℝ a x + c)}

/-- The rank-one activation `σ_β(y) = β(⟪ψ, y⟫) z` built from a real scalar activation `β` and
fixed vectors `ψ, z ∈ H`. -/
def rankOneActivation (β : ℝ → ℝ) (ψ z : H) (y : H) : H :=
  β (inner ℝ ψ y) • z

/-- The finite-width operator network `x ↦ ∑_j n_{ℓ,A_j,b_j}(x) • v_j` with values in `Y`. -/
def operatorFiniteNetwork {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {N : ℕ}
    (σ : H → H) (ℓ : H) (v : Fin N → Y) (A : Fin N → (H →L[ℝ] H)) (b : Fin N → H) (x : H) : Y :=
  ∑ j, operatorNeuron σ ℓ (A j) (b j) x • v j

/-- The operator synthesis `S_op Γ_op(x) = ∫ n_{ℓ,A,b}(x) Γ_op(dA, db)` of a complex measure
`Γ_op` on operator parameters `(A, b)`: the real neuron is integrated as a complex-valued
function against `Γ_op`, with the same convention as `integralNetwork`. -/
def operatorSynthesis [MeasurableSpace H] (σ : H → H) (ℓ : H)
    (Γ : ComplexMeasure (OperatorRidgeParameter H)) (x : H) : ℂ :=
  ∫ᵛ p, ((operatorNeuron σ ℓ p.1 p.2 x : ℝ) : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; Γ]

end OperatorRidgelet
