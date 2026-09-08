import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Architecture.Defs

/-!
# Definitions for Section 6 (finite-width approximation) and Appendix D

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

## The compact-open seminorms

`‖f‖_{C(K;Y)} = sup_{x ∈ K} ‖f(x)‖` is `compactSupNorm K f`, the supremum of the image
`{‖f x‖ : x ∈ K}` (junk value `0` when `K` is empty or the norms are unbounded on `K`; for
continuous `f` and compact `K` it is the manuscript's norm).  `R_K = sup_{x ∈ K} √(‖x‖² + 1)` is
`compactRadius K`.  The statements that need the Banach space `C(K)` itself (Theorem
`thm:general-rademacher`) use `BoundedContinuousFunction K Y` on the subtype `K`.

## The polar decomposition and the sampled network

For a `Y`-valued measure `Γ` of bounded variation (`MeasureTheory.VectorMeasure` with finite
`variation`, as in `OperatorRidgelet.Network.Defs`), the polar decomposition `Γ = h|Γ|` with
`‖h‖ = 1` `|Γ|`-almost everywhere is represented by

* `polarDensity Γ = h`, a density of `Γ` with respect to `|Γ|` of norm one almost everywhere,
  chosen when one exists (it always does for complex and Hilbert-space-valued measures by the
  Radon–Nikodym theorem, which is a theorem and not part of the definition) and `0` otherwise;
* `polarWeight Γ = V = ‖Γ‖_TV` as a real number;
* `polarLaw Γ = p = |Γ|/V`, the probability law of the parameters (the zero measure when
  `Γ = 0`, which represents the manuscript's "if `Γ = 0` take the zero network").

For a coefficient measure `Γ = γ λ` with a density (Theorems `thm:E` and `thm:D`), the
manuscript writes `V = ‖γ‖_{L¹(λ)}`, `p = |γ| λ / V`, `h = γ/|γ|` explicitly; these are
`densityWeight`, `densityLaw`, and `densityPhase`.

The `N` independent samples `θ = (θ_1, …, θ_N) ∼ p^{⊗N}` live on `Fin N → H × ℝ` with the
product measure `sampleLaw N p = Measure.pi (fun _ => p)`, and the sampled network is
`sampledNetwork β V h θ (x) = (V/N) ∑_j β(⟪a_j, x⟫ + c_j) • h(θ_j)` (`eq:polar-network`), a
`finiteNetwork` with outer weights `(V/N) h(θ_j)`; `polarSampledNetwork β Γ` and
`densitySampledNetwork β λ γ` instantiate it with the polar data of `Γ` and of `γ λ`.
Expectations `𝔼‖f_N − f‖_{C(K)}` are Bochner integrals against `sampleLaw N p`.

## Rademacher signs and the Rademacher complexity

Independent Rademacher signs `ε ∈ {-1, 1}^N` are represented by real-valued coordinates with
the law `rademacherMeasure N = Measure.pi (fun _ => (δ_{-1} + δ_{1})/2)` on `Fin N → ℝ`.  The
activation-dependent Rademacher complexity `𝔑_N(K; p, β)` of Definition
`def:rademacher-complexity` is `rademacherComplexity N K p β h`, the joint expectation over
`(θ, ε) ∼ p^{⊗N} ⊗ rademacherMeasure N` of `sup_{x ∈ K} ‖N⁻¹ ∑_j ε_j β(⟪a_j, x⟫ + c_j) h(θ_j)‖`;
it is polymorphic in the output space, so that `𝔑^Y_N` of Corollary `cor:vector-rates` is the
same definition with `Y`-valued phases `h`.

## Moments, atomic measures, and operator parameters

`secondMoment p = M₂² = ∫ (‖a‖² + |c|²) dp`; `M₂` itself is `√(secondMoment p)`.  The Lipschitz
constant `Lip(β)` is not a separate definition: the statements take any `L` with
`LipschitzWith L β` and are stated with `L`, which is equivalent to the statement with the least
Lipschitz constant.  A finite atomic measure `∑_j w_j δ_{θ_j}` is `atomicMeasure w θ`.  The
operator-parameter sampled network of Corollary `cor:operator-sampling` is
`sampledOperatorNetwork σ ℓ V h ω`, an `operatorFiniteNetwork` with outer weights
`(V/N) h(A_j, b_j)`, and `operatorSecondMoment ψ p = M_op² = ∫ (‖A^*ψ‖² + |⟪ψ, b⟫|²) dp`.
`IsFiniteRankProjection P` is the hypothesis of Corollary `cor:two-stage-error` on each `Π_m`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-! ### The compact sup norm and the radius of a compact set -/

section SupNorm

variable {X : Type*} {Y : Type*} [NormedAddCommGroup Y]

/-- The compact sup norm `‖f‖_{C(K;Y)} = sup_{x ∈ K} ‖f(x)‖` of a function `f : X → Y` on a
set `K`, as the supremum of the image `{‖f x‖ : x ∈ K}` (`0` when `K` is empty or the norms are
unbounded on `K`). -/
def compactSupNorm (K : Set X) (f : X → Y) : ℝ :=
  sSup ((fun x => ‖f x‖) '' K)

end SupNorm

/-- The radius `R_K = sup_{x ∈ K} √(‖x‖² + 1)` of a set `K` (Theorem `thm:lipschitz-barron`). -/
def compactRadius {H : Type*} [NormedAddCommGroup H] (K : Set H) : ℝ :=
  sSup ((fun x => Real.sqrt (‖x‖ ^ 2 + 1)) '' K)

/-! ### The polar decomposition of a measure of bounded variation -/

section Polar

variable {Θ : Type*} [MeasurableSpace Θ] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

open Classical in
/-- The phase `h` of the polar decomposition `Γ = h |Γ|` of a `Y`-valued measure of bounded
variation: a density of `Γ` with respect to its variation measure `|Γ|` with `‖h‖ = 1`
`|Γ|`-almost everywhere, chosen when one exists, and `0` otherwise. -/
def polarDensity (Γ : VectorMeasure Θ Y) : Θ → Y :=
  if h : ∃ g : Θ → Y, (∀ᵐ θ ∂Γ.variation, ‖g θ‖ = 1) ∧ Γ = Γ.variation.withDensityᵥ g then
    h.choose
  else 0

/-- The weight `V = ‖Γ‖_TV = |Γ|(Θ)` of the polar decomposition, as a real number
(`eq:polar-decomposition`). -/
def polarWeight (Γ : VectorMeasure Θ Y) : ℝ :=
  (totalVariation Γ).toReal

/-- The parameter law `p = |Γ| / V` of the polar decomposition (`eq:polar-decomposition`); it
is a probability measure when `Γ ≠ 0` and the zero measure when `Γ = 0`. -/
def polarLaw (Γ : VectorMeasure Θ Y) : Measure Θ :=
  (totalVariation Γ)⁻¹ • Γ.variation

/-- The weight `V = ‖γ‖_{L¹(λ)} = ∫ ‖γ‖ dλ` of a coefficient measure `γ λ` with a density. -/
def densityWeight (lam : Measure Θ) (γ : Θ → Y) : ℝ :=
  ∫ θ, ‖γ θ‖ ∂lam

/-- The parameter law `p = |γ| λ / V` of a coefficient measure `γ λ` with a density. -/
def densityLaw (lam : Measure Θ) (γ : Θ → Y) : Measure Θ :=
  (ENNReal.ofReal (densityWeight lam γ))⁻¹ • lam.withDensity fun θ => ‖γ θ‖ₑ

/-- The phase `h = γ / ‖γ‖` of a coefficient measure `γ λ` with a density (`0` where `γ`
vanishes). -/
def densityPhase (γ : Θ → Y) (θ : Θ) : Y :=
  (‖γ θ‖⁻¹ : ℝ) • γ θ

end Polar

/-! ### Independent samples, Rademacher signs, and the sampled network -/

/-- The law `p^{⊗N}` of `N` independent parameters `θ_1, …, θ_N ∼ p`, on `Fin N → Θ`. -/
def sampleLaw {Θ : Type*} [MeasurableSpace Θ] (N : ℕ) (p : Measure Θ) : Measure (Fin N → Θ) :=
  Measure.pi fun _ => p

/-- The law of `N` independent Rademacher signs `ε_1, …, ε_N ∈ {-1, 1}`, represented as real
numbers: the product of `N` copies of `(δ_{-1} + δ_1)/2` on `Fin N → ℝ`. -/
def rademacherMeasure (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ => (2⁻¹ : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

section Sampling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The sampled network `f_N(x) = (V/N) ∑_j β(⟪a_j, x⟫ + c_j) • h(θ_j)` (`eq:polar-network`)
of the samples `θ_j = (a_j, c_j)`, with weight `V` and phase `h`: a width-`N` network with outer
weights `(V/N) h(θ_j)`.  The scalar case is `Y = ℂ`. -/
def sampledNetwork {N : ℕ} (β : ℝ → ℂ) (V : ℝ) (h : H × ℝ → Y) (θ : Fin N → H × ℝ) : H → Y :=
  finiteNetwork β (fun j => ((V / N : ℝ) : ℂ) • h (θ j)) (fun j => (θ j).1) (fun j => (θ j).2)

/-- The sampled network `eq:polar-network` of a measure `Γ` of bounded variation: the weight
`V = ‖Γ‖_TV` and the phase `h` of its polar decomposition, with samples `θ_j ∼ p = |Γ|/V`. -/
def polarSampledNetwork {N : ℕ} (β : ℝ → ℂ) (Γ : VectorMeasure (H × ℝ) Y)
    (θ : Fin N → H × ℝ) : H → Y :=
  sampledNetwork β (polarWeight Γ) (polarDensity Γ) θ

/-- The sampled network `eq:polar-network` of a coefficient measure `γ λ` with a density: the
weight `V = ‖γ‖_{L¹(λ)}` and the phase `h = γ/‖γ‖`, with samples `θ_j ∼ p = |γ| λ / V`. -/
def densitySampledNetwork {N : ℕ} (β : ℝ → ℂ) (lam : Measure (H × ℝ)) (γ : H × ℝ → Y)
    (θ : Fin N → H × ℝ) : H → Y :=
  sampledNetwork β (densityWeight lam γ) (densityPhase γ) θ

/-- **Definition [def:rademacher-complexity]** The activation-dependent Rademacher complexity
`𝔑_N(K; p, β) = 𝔼_{θ,ε} sup_{x ∈ K} ‖N⁻¹ ∑_j ε_j β(⟪a_j, x⟫ + c_j) h(θ_j)‖`
(`eq:rademacher-complexity`), with `θ_j ∼ p` independent and `ε_j` independent Rademacher
signs; `h` is the phase of the polar decomposition.  The scalar case is `Y = ℂ`, and `Y`-valued
phases give `𝔑^Y_N(K; p, β)` of Corollary `cor:vector-rates`. -/
def rademacherComplexity (N : ℕ) (K : Set H) (p : Measure (H × ℝ)) (β : ℝ → ℂ)
    (h : H × ℝ → Y) : ℝ :=
  ∫ ω, compactSupNorm K (fun x =>
      (N : ℂ)⁻¹ • ∑ j, ((ω.2 j : ℝ) : ℂ) • (β (⟪(ω.1 j).1, x⟫ + (ω.1 j).2) • h (ω.1 j)))
    ∂((sampleLaw N p).prod (rademacherMeasure N))

/-- The second moment `M₂² = ∫ (‖a‖² + |c|²) p(da, dc)` (`eq:second-moment`) of a parameter
law `p`; `M₂` is its square root. -/
def secondMoment (p : Measure (H × ℝ)) : ℝ :=
  ∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂p

/-- The finite atomic `Y`-valued measure `∑_j w_j δ_{θ_j}` on `H × ℝ`. -/
def atomicMeasure {n : ℕ} (w : Fin n → Y) (θ : Fin n → H × ℝ) : VectorMeasure (H × ℝ) Y :=
  ∑ j, VectorMeasure.dirac (θ j) (w j)

end Sampling

/-! ### Operator parameters and finite-rank projections -/

section Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The sampled operator network `f_{op,N}(x) = (V/N) ∑_j h(A_j, b_j) n_{ℓ,A_j,b_j}(x)` of
Corollary `cor:operator-sampling`: a finite-width operator network with the samples
`(A_j, b_j)` and outer weights `(V/N) h(A_j, b_j)`. -/
def sampledOperatorNetwork {N : ℕ} (σ : H → H) (ℓ : H) (V : ℝ)
    (h : OperatorRidgeParameter H → ℂ) (ω : Fin N → OperatorRidgeParameter H) : H → ℂ :=
  operatorFiniteNetwork σ ℓ (fun j => ((V / N : ℝ) : ℂ) • h (ω j)) (fun j => (ω j).1)
    (fun j => (ω j).2)

/-- The operator second moment `M_op² = ∫ (‖A^*ψ‖² + |⟪ψ, b⟫|²) p_op(dA, db)` of Corollary
`cor:operator-sampling`. -/
def operatorSecondMoment [MeasurableSpace H] (ψ : H)
    (p : Measure (OperatorRidgeParameter H)) : ℝ :=
  ∫ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2) ∂p

/-- `P` is a finite-rank orthogonal projection: a self-adjoint idempotent with
finite-dimensional range. -/
structure IsFiniteRankProjection (P : H →L[ℝ] H) : Prop where
  /-- `P` is an orthogonal projection: `P^* = P = P²`. -/
  isStarProjection : IsStarProjection P
  /-- The range of `P` is finite dimensional. -/
  finiteDimensional_range : FiniteDimensional ℝ (LinearMap.range (P : H →ₗ[ℝ] H))

end Operator

end OperatorRidgelet
