import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Gaussian-weighted ridgelet transform

This module states the constructions and the main theorems of the Gaussian-weighted ridgelet
transform on a real Hilbert space, as developed in the manuscript.

The input variable carries a Gaussian weight `μ`, the parameter variable carries a `σ`-finite
reference measure `ν` that is homogeneous of some degree `α > 0` under dilations, and the bias
variable carries Lebesgue measure.  The spectral variable is never dilated, which is what
distinguishes this construction from the Fourier-side one: on an infinite-dimensional space the
dilations move a Gaussian spectral measure across a continuum of mutually singular measures, and
no `σ`-finite measure dominates such a family.

Every main theorem below is stated and left with `sorry` so that the formalization status is
visible in the blueprint.  Only the definitions and a few immediate lemmas are proved.

## Main statements

* `isHomogeneous_map_smul`: the change of variables supplied by homogeneity, which is the only
  place where a substitution in the parameter variable is used.
* `integral_ridgelet_mul_character`: the Fourier-slice identity.
* `plancherel`: the ridgelet Plancherel identity.
* `injective_ridgelet`: the transform has trivial null space.
* `gaussFourier_eq_of_ridgelet`: the inversion formula for the Gaussian-weighted Fourier
  transform.
* `gaussFourier_injective`: the analysis map is injective, so the inversion is unambiguous.
* `frameOperator_eq_energyInner`: the frame operator is the Riesz map of the energy form.
-/

noncomputable section

namespace OperatorRidgelet.GaussianWeighted

open MeasureTheory Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Characters and the two Fourier transforms -/

/-- The character `x ↦ exp(-i⟪x,ξ⟫)` used by the analysis map. -/
def character (ξ x : H) : ℂ :=
  Complex.exp (-((inner ℝ x ξ : ℝ) * Complex.I))

@[simp]
theorem character_zero_right (x : H) : character (0 : H) x = 1 := by
  simp [character]

@[simp]
theorem character_zero_left (ξ : H) : character ξ (0 : H) = 1 := by
  simp [character]

section Measures

variable [MeasurableSpace H]

/-- The Gaussian-weighted Fourier transform
`𝒢f(ξ) = ∫ f(x) exp(-i⟪x,ξ⟫) dμ(x)`.  It is the Fourier--Stieltjes transform of the complex
measure `f μ`, evaluated at `-ξ`. -/
def gaussFourier (μ : Measure H) (f : H → ℂ) (ξ : H) : ℂ :=
  ∫ x, f x * character ξ x ∂μ

@[simp]
theorem gaussFourier_zero (μ : Measure H) : gaussFourier μ 0 = 0 := by
  funext ξ
  simp [gaussFourier]

/-- The Gaussian-weighted Fourier transform of the constant function `1` is the characteristic
function of `μ` at `-ξ`. -/
theorem gaussFourier_one (μ : Measure H) (ξ : H) :
    gaussFourier μ (fun _ => (1 : ℂ)) ξ = charFun μ (-ξ) := by
  simp only [gaussFourier, charFun, character, one_mul]
  congr 1
  funext x
  rw [inner_neg_right]
  push_cast
  ring_nf

/-- The one-dimensional Fourier transform in the convention of the manuscript,
`ρ̂(ω) = ∫ ρ(t) exp(-iωt) dt`. -/
def filterFourier (ρ : ℝ → ℝ) (ω : ℝ) : ℂ :=
  ∫ t : ℝ, (ρ t : ℂ) * Complex.exp (-((ω * t : ℝ) * Complex.I))

@[simp]
theorem filterFourier_zero (ω : ℝ) : filterFourier 0 ω = 0 := by
  simp [filterFourier]

/-! ### Homogeneous reference measures -/

/-- A measure on `H` is homogeneous of degree `α` when every dilation scales it by
`|ω|^(-α)`.  On `ℝ^m` Lebesgue measure is homogeneous of degree `m`; on an infinite-dimensional
space the degree is an independent parameter. -/
def IsHomogeneous (α : ℝ) (ν : Measure H) : Prop :=
  ∀ ω : ℝ, ω ≠ 0 → ν.map (fun a => ω • a) = ENNReal.ofReal (|ω| ^ (-α)) • ν

/-- Existence of a `σ`-finite homogeneous reference measure of any positive degree on an
infinite-dimensional space.  The manuscript constructs one as the Gaussian mixture
`ν_α = ∫₀^∞ 𝒩(0,2sP) s^(α/2-1) ds` with `P` injective, positive and trace class; the mixture is
finite on balls by the Gaussian small-ball estimate and has total mass `∞`. -/
theorem exists_isHomogeneous_sFinite (α : ℝ) (hα : 0 < α) [Nontrivial H] :
    ∃ ν : Measure H, SFinite ν ∧ IsHomogeneous α ν ∧ ν ≠ 0 := by
  sorry

/-- The topological support of the Gaussian mixture is all of `H`, because the support of a
centred Gaussian measure is the closure of its Cameron--Martin space and `P` is injective. -/
theorem exists_isHomogeneous_sFinite_support (α : ℝ) (hα : 0 < α) [Nontrivial H] :
    ∃ ν : Measure H, SFinite ν ∧ IsHomogeneous α ν ∧
      ∀ U : Set H, IsOpen U → U.Nonempty → ν U ≠ 0 := by
  sorry

/-- The change of variables supplied by homogeneity.  This is the only substitution performed in
the parameter variable, and it is the reason the construction never requires any measure to be
absolutely continuous with respect to `ν`. -/
theorem isHomogeneous_map_smul {α : ℝ} {ν : Measure H} (hν : IsHomogeneous α ν)
    {ω : ℝ} (hω : ω ≠ 0) (F : H → ENNReal) (hF : Measurable F) :
    ∫⁻ a, F (ω • a) ∂ν = ENNReal.ofReal (|ω| ^ (-α)) * ∫⁻ a, F a ∂ν := by
  sorry

/-! ### The transform -/

/-- The Gaussian-weighted ridgelet transform
`R_ρ[f](a,c) = ∫ f(x) ρ(⟪a,x⟫ + c) dμ(x)`.  No reference measure on `H` other than the Gaussian
weight `μ` occurs, so the transform is defined for every `f ∈ L²(H,μ)` without further
hypotheses. -/
def ridgelet (μ : Measure H) (ρ : ℝ → ℝ) (f : H → ℂ) (p : H × ℝ) : ℂ :=
  ∫ x, f x * (ρ (inner ℝ p.1 x + p.2) : ℂ) ∂μ

@[simp]
theorem ridgelet_zero (μ : Measure H) (ρ : ℝ → ℝ) : ridgelet μ ρ 0 = 0 := by
  funext p
  simp [ridgelet]

/-- The parameter measure on `H × ℝ`: the homogeneous reference measure on the ridge direction
and Lebesgue measure on the bias. -/
def parameterMeasure (ν : Measure H) [SFinite ν] : Measure (H × ℝ) :=
  ν.prod volume

/-- The admissibility constant
`C^{(α)}_{ρ₁,ρ₂} = (2π)⁻¹ ∫ ρ̂₁(ω) conj(ρ̂₂(ω)) |ω|^(-α) dω`.  For `α = 1` this is the Calderón
condition of the one-dimensional wavelet transform, and no dimension occurs in it. -/
def admissibilityConst (α : ℝ) (ρ₁ ρ₂ : ℝ → ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, filterFourier ρ₁ ω * (starRingEnd ℂ) (filterFourier ρ₂ ω) *
      ((|ω| ^ (-α) : ℝ) : ℂ)

/-- A filter is admissible when its Fourier transform is smooth and compactly supported away from
the origin.  Compact support away from `0` makes every admissibility constant absolutely
convergent, and it lets the activation be merely locally integrable on the frequency side, which
is what admits ReLU. -/
structure IsAdmissibleFilter (ρ : ℝ → ℝ) : Prop where
  /-- The filter is smooth. -/
  schwartz : ContDiff ℝ (⊤ : ℕ∞) ρ
  /-- The Fourier transform of the filter vanishes outside an annulus `r ≤ |ω| ≤ R` with
  `0 < r < R`; in particular it vanishes near the origin. -/
  compactSupportAwayFromZero :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ ∀ ω : ℝ, filterFourier ρ ω ≠ 0 → r ≤ |ω| ∧ |ω| ≤ R

/-- The Fourier-slice identity
`∫ R_ρ[f](a,c) exp(-iωc) dc = ρ̂(ω) 𝒢f(-ω a)`.  It is the single computation from which the
Plancherel identity, injectivity and the inversion formula all follow. -/
theorem integral_ridgelet_mul_character (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ) (f : H → ℂ) (hf : Integrable f μ)
    (a : H) (ω : ℝ) :
    ∫ c : ℝ, ridgelet μ ρ f (a, c) * Complex.exp (-((ω * c : ℝ) * Complex.I)) =
      filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
  sorry

/-! ### The energy form and the Plancherel identity -/

/-- The energy inner product `⟨f,g⟩_𝔈 = ∫ 𝒢f conj(𝒢g) dν`. -/
def energyInner (μ ν : Measure H) (f g : H → ℂ) : ℂ :=
  ∫ ξ, gaussFourier μ f ξ * (starRingEnd ℂ) (gaussFourier μ g ξ) ∂ν

/-- Membership in the energy space `𝔈_α = {f ∈ L²(H,μ) : ∫ |𝒢f|² dν < ∞}`. -/
def MemEnergySpace (μ ν : Measure H) (f : H → ℂ) : Prop :=
  MemLp f 2 μ ∧ Integrable (fun ξ => ‖gaussFourier μ f ξ‖ ^ 2) ν

/-- Gaussian decay of the analysis map is enough for membership in the energy space.  In the
manuscript this follows from `∫ exp(-t⟪Qξ,ξ⟫) dν_α < ∞`, which holds for every `t > 0` and every
`α > 0` when the covariances are injective and `dim H = ∞`. -/
theorem memEnergySpace_of_gaussian_decay (μ ν : Measure H) [IsProbabilityMeasure μ]
    (f : H → ℂ) (hf : MemLp f 2 μ) (Q : H →L[ℝ] H) (C t : ℝ) (ht : 0 < t)
    (hdecay : ∀ ξ : H, ‖gaussFourier μ f ξ‖ ≤ C * Real.exp (-t * inner ℝ (Q ξ) ξ / 2)) :
    MemEnergySpace μ ν f := by
  sorry

/-- The ridgelet Plancherel identity: the parameter-space inner product of two transforms is the
admissibility constant times the energy inner product of the targets.  In finite dimension, with
`ν` Lebesgue and `α = m`, this reduces to the classical ridgelet Plancherel formula; the only
change in infinite dimension is that the right-hand side is a weighted energy rather than an
`L²` inner product. -/
theorem plancherel {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    (hν : IsHomogeneous α ν) (ρ₁ ρ₂ : ℝ → ℝ)
    (hρ₁ : IsAdmissibleFilter ρ₁) (hρ₂ : IsAdmissibleFilter ρ₂)
    (f g : H → ℂ) (hf : MemEnergySpace μ ν f) (hg : MemEnergySpace μ ν g) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      admissibilityConst α ρ₁ ρ₂ * energyInner μ ν f g := by
  sorry

/-- The transform of an energy-space element is square integrable on the parameter space, with
norm given by the Plancherel identity. -/
theorem memLp_ridgelet {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] (hν : IsHomogeneous α ν) (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ)
    (f : H → ℂ) (hf : MemEnergySpace μ ν f) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure ν) := by
  sorry

/-! ### Injectivity and inversion -/

/-- The analysis map is injective: a finite complex measure on a separable Hilbert space is
determined by its characteristic functional, so `𝒢f = 0` forces `f = 0`.  In Mathlib the
underlying uniqueness statement is `MeasureTheory.Measure.ext_of_charFun`. -/
theorem gaussFourier_injective [CompleteSpace H] [SecondCountableTopology H]
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H → ℂ) (hf : Integrable f μ)
    (h : ∀ ξ : H, gaussFourier μ f ξ = 0) :
    f =ᵐ[μ] 0 := by
  sorry

/-- The transform has trivial null space.  The proof combines the Fourier-slice identity, the
homogeneity change of variables, continuity of `𝒢f`, and the fact that `ν` charges every
nonempty open set. -/
theorem injective_ridgelet [CompleteSpace H] [SecondCountableTopology H]
    {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    (hν : IsHomogeneous α ν) (hsupp : ∀ U : Set H, IsOpen U → U.Nonempty → ν U ≠ 0)
    (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ) (hρ0 : ρ ≠ 0)
    (f : H → ℂ) (hf : Integrable f μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure ν] 0) :
    f =ᵐ[μ] 0 := by
  sorry

/-- The inversion formula: the analysis map is recovered from the ridgelet coefficients along any
ray, that is for any factorization `ξ = -ω a`.  The redundancy of the transform is exactly the
non-uniqueness of that factorization, and equality of the resulting expressions characterizes the
range of the transform. -/
theorem gaussFourier_eq_of_ridgelet (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ) (f : H → ℂ) (hf : Integrable f μ)
    (ξ : H) (ω : ℝ) (hω : ω ≠ 0) (hρω : filterFourier ρ ω ≠ 0) :
    gaussFourier μ f ξ =
      (filterFourier ρ ω)⁻¹ *
        ∫ c : ℝ, ridgelet μ ρ f (-(ω⁻¹ • ξ), c) *
          Complex.exp (-((ω * c : ℝ) * Complex.I)) := by
  sorry

/-- The de-Gaussianized analysis map `G(ξ) = exp(⟪Qξ,ξ⟫/2) 𝒢f(ξ)`.  Along every ray it is an
entire function of the scaling parameter, with the Taylor coefficients of the manuscript. -/
def deGaussianized (μ : Measure H) (Q : H →L[ℝ] H) (f : H → ℂ) (ξ : H) : ℂ :=
  Complex.exp ((inner ℝ (Q ξ) ξ : ℝ) / 2) * gaussFourier μ f ξ

/-- The Taylor coefficients of the de-Gaussianized analysis map along a ray are the Wick moments
of `f`, and those moments determine `f` because the Wick powers are total in `L²(H,μ)`.  This is
the inversion of the analysis map, that is `𝒢⁻¹`. -/
theorem deGaussianized_determines (μ : Measure H) [IsProbabilityMeasure μ]
    (Q : H →L[ℝ] H) (f g : H → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (h : ∀ ξ : H, deGaussianized μ Q f ξ = deGaussianized μ Q g ξ) :
    f =ᵐ[μ] g := by
  sorry

/-! ### The frame operator -/

/-- The frame operator applied to `f`, namely `T_α f = 𝒢^* 𝒢 f`, written as the
Fourier--Stieltjes transform of `(𝒢f) ν`. -/
def frameOperator (μ ν : Measure H) (f : H → ℂ) (x : H) : ℂ :=
  ∫ ξ, gaussFourier μ f ξ * (starRingEnd ℂ) (character ξ x) ∂ν

/-- The frame operator represents the energy form: `⟨T_α f, g⟩_{L²(μ)} = ⟨f,g⟩_𝔈`.  Consequently
`T_α` is the Riesz isomorphism of the energy space onto its dual, and reconstruction from the
synthesis of the transform is the inverse Riesz map. -/
theorem frameOperator_eq_energyInner (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    (f g : H → ℂ) (hf : MemEnergySpace μ ν f) (hg : MemEnergySpace μ ν g) :
    ∫ x, frameOperator μ ν f x * (starRingEnd ℂ) (g x) ∂μ = energyInner μ ν f g := by
  sorry

/-- Composing the transform with the adjoint of a second transform gives the admissibility
constant times the frame operator.  This is the synthesis form of the Plancherel identity. -/
theorem synthesis_comp_ridgelet {α : ℝ} (hα : 0 < α) (μ ν : Measure H)
    [IsProbabilityMeasure μ] [SFinite ν] (hν : IsHomogeneous α ν)
    (ρ₁ ρ₂ : ℝ → ℝ) (hρ₁ : IsAdmissibleFilter ρ₁) (hρ₂ : IsAdmissibleFilter ρ₂)
    (f g : H → ℂ) (hf : MemEnergySpace μ ν f) (hg : MemEnergySpace μ ν g) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      admissibilityConst α ρ₁ ρ₂ *
        ∫ x, frameOperator μ ν f x * (starRingEnd ℂ) (g x) ∂μ := by
  sorry

/-! ### The reproducing formula -/

/-- The bias-Fourier transform of a coefficient function. -/
def biasFourier (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) : ℂ :=
  ∫ c : ℝ, γ (a, c) * Complex.exp (-((ω * c : ℝ) * Complex.I))

/-- The ray average of a coefficient function,
`Λ[γ](ξ) = (2π)⁻¹ ∫ conj(ρ̂(ω)) |ω|^(-α) γ̂(-ξ/ω, ω) dω`.  It averages the inversion over every
factorization `ξ = -ω a` instead of choosing one ray, and is the analogue of the filtered
backprojection of the Radon inversion. -/
def rayAverage (α : ℝ) (ρ : ℝ → ℝ) (γ : H × ℝ → ℂ) (ξ : H) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) *
      biasFourier γ (-(ω⁻¹ • ξ)) ω

/-- The ray average is the adjoint of the transform: pairing a coefficient function with a
transform on the parameter side equals pairing its ray average with the analysis map on the
spectral side. -/
theorem inner_rayAverage {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] (hν : IsHomogeneous α ν) (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ)
    (γ : H × ℝ → ℂ) (hγ : MemLp γ 2 (parameterMeasure ν))
    (f : H → ℂ) (hf : MemEnergySpace μ ν f) :
    ∫ p, γ p * (starRingEnd ℂ) (ridgelet μ ρ f p) ∂parameterMeasure ν =
      ∫ ξ, rayAverage α ρ γ ξ * (starRingEnd ℂ) (gaussFourier μ f ξ) ∂ν := by
  sorry

/-- The ray average inverts the transform exactly, up to the admissibility constant:
`Λ[R_ρ[f]] = C * 𝒢f`.  Together with the inversion of the analysis map this is the reconstruction
formula `Δ[C⁻¹ Λ[R_ρ[f]]] = f`. -/
theorem rayAverage_ridgelet {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] (hν : IsHomogeneous α ν) (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ)
    (f : H → ℂ) (hf : MemEnergySpace μ ν f) (ξ : H) :
    rayAverage α ρ (ridgelet μ ρ f) ξ =
      admissibilityConst α ρ ρ * gaussFourier μ f ξ := by
  sorry

/-- The orthogonal projection onto the closure of the range of the transform, written on the
bias-Fourier side.  A coefficient function lies in the range exactly when it is a fixed point;
this is the reproducing identity, and it is the range characterization of the transform. -/
def rangeProjection (α : ℝ) (ρ : ℝ → ℝ) (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) : ℂ :=
  (admissibilityConst α ρ ρ)⁻¹ * filterFourier ρ ω * rayAverage α ρ γ (-(ω • a))

/-- The transform is a fixed point of the projection: the reproducing identity. -/
theorem rangeProjection_ridgelet {α : ℝ} (hα : 0 < α) (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] (hν : IsHomogeneous α ν) (ρ : ℝ → ℝ) (hρ : IsAdmissibleFilter ρ)
    (hC : admissibilityConst α ρ ρ ≠ 0)
    (f : H → ℂ) (hf : MemEnergySpace μ ν f) (a : H) (ω : ℝ) :
    rangeProjection α ρ (ridgelet μ ρ f) a ω = biasFourier (ridgelet μ ρ f) a ω := by
  sorry

/-! ### General weights

The isometry half of the theory needs no Gaussian structure.  Note that `plancherel`,
`inner_rayAverage`, `rayAverage_ridgelet`, `rangeProjection_ridgelet` and `injective_ridgelet` are
already stated for an arbitrary probability weight `μ`: no Gaussian hypothesis appears in any of
them.  The only statement that needs the Gaussian structure is `deGaussianized_determines`, which
inverts the analysis map through the Wiener--Ito chaos decomposition.

What a general weight does change is whether the energy space is rich enough, and that is exactly a
decay condition on the characteristic functional of the weight. -/

/-- The energy space contains the constants exactly when the characteristic functional of the
weight is square integrable against the reference measure.  For a Gaussian weight this holds for
every degree of homogeneity; for a weight with an atom it fails. -/
theorem memEnergySpace_one_iff (μ ν : Measure H) [IsProbabilityMeasure μ] :
    MemEnergySpace μ ν (fun _ => (1 : ℂ)) ↔
      Integrable (fun ξ => ‖charFun μ (-ξ)‖ ^ 2) ν := by
  sorry

/-! ### The obstruction to the dilation-based construction -/

/-- A `σ`-finite measure dominates at most countably many pairwise mutually singular probability
measures.  Mutual singularity gives pairwise disjoint carriers of positive `ν`-measure, and a
`σ`-finite measure admits only countably many such sets. -/
theorem countable_of_absolutelyContinuous_of_pairwise_mutuallySingular
    {ι : Type*} (ν : Measure H) [SFinite ν] (π : ι → Measure H)
    (hprob : ∀ i, IsProbabilityMeasure (π i))
    (hac : ∀ i, π i ≪ ν)
    (hsing : Pairwise fun i j => (π i).MutuallySingular (π j)) :
    Countable ι := by
  sorry

/-- The obstruction to the dilation-based construction, in the form used by the manuscript.  An
uncountable pairwise mutually singular family of probability measures is carried by no
`σ`-finite measure.  Applied to the dilated Gaussian spectral measures
`𝒩(0,R/ω²)`, which are pairwise mutually singular in infinite dimension by the
Feldman--Hájek dichotomy, this shows that the hypothesis of the Fourier-side finite-measure
reconstruction theorem is unsatisfiable. -/
theorem not_exists_sFinite_dominating {ι : Type*} [Uncountable ι]
    (π : ι → Measure H) (hprob : ∀ i, IsProbabilityMeasure (π i))
    (hsing : Pairwise fun i j => (π i).MutuallySingular (π j)) :
    ¬ ∃ ν : Measure H, SFinite ν ∧ ∀ i, π i ≪ ν := by
  sorry

end Measures

end OperatorRidgelet.GaussianWeighted
