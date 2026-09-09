import LeanRidgelet.Fourier.Convention
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Definitions for Section 3 (the Gaussian-weighted ridgelet transform) and Appendices A, G, H, I

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

## The abstract pair `(μ, ν)`

Following Appendix H of the manuscript, the core theory is set up for an abstract pair: `μ` is
a Borel probability measure on the input space `H` (the manuscript's `μ_Q = 𝒩(0,Q)`), and `ν`
is a σ-finite Borel measure on the direction space `H` with full support which is homogeneous of
degree `α` under dilations, `(D_ω)_# ν = |ω|^{-α} ν` (the manuscript's Gaussian mixture `ν_α`).
The Gaussian objects are represented as follows.

* `𝒩(0,Q)` is the predicate `IsCenteredGaussian Q μ`: `μ` is a probability measure with
  characteristic functional `ξ ↦ exp(-⟨Qξ,ξ⟩/2)`, which is the manuscript's definition of the
  centred Gaussian measure with covariance `Q`.
* "positive, self-adjoint, trace class" is the predicate `IsPositiveTraceClass` (the
  hypothesis of Lemma `lem:gaussian-quadratic`), and "injective, positive, self-adjoint, trace
  class" is `IsTraceClassCovariance`, which extends it by injectivity.  The trace condition
  `HasSummableTrace P` is the summability of `∑ ⟪P e_j, e_j⟫` along some Hilbert basis, and the
  trace `tr P` is `traceOf P`, the sum along such a basis (`traceAlong`); for a positive
  operator the value is basis independent, which is a proof obligation and not part of the
  definition.
* The Gaussian layers `𝒩(0,2sP)`, `s > 0`, are a family `N : ℝ → Measure H` satisfying
  `IsCenteredGaussianLayers P N`; Mathlib has no constructor of a Gaussian measure with a
  prescribed trace-class covariance in infinite dimension, so the existence of such a family is
  recorded as a separate infrastructure statement (`exists_isCenteredGaussianLayers`).
* The mixture `ν_α = ∫₀^∞ 𝒩(0,2sP) s^{α/2-1} ds` is `gaussianMixture N α`, the Giry-monad bind
  of the weight `s^{α/2-1} ds` on `(0,∞)` against the layers (Lemma A.1).

## The Hilbert space `𝓔_α`

The manuscript completes the pre-Hilbert space `𝒟_α = {f ∈ L²(μ) : 𝒢_μ f ∈ L²(ν)}` in the
spectral norm.  Building that completion in Lean would require the positivity of the spectral
form inside a definition (it is Lemma 3.8, a theorem).  We therefore represent `𝓔_α` by the
closed subspace `𝒦_α = closure (𝒢_μ 𝒟_α) ⊆ L²(ν)` (`spectralRange`), to which Lemma 3.8 shows
`𝓔_α` is unitarily equivalent; the unitary `U_α` becomes the map `spectralEmbed : 𝒟_α → 𝒦_α`,
and the Riesz map and the extension of `R_ρ` are stated on `𝒦_α`.

## The coefficient operator

`W_ρ G ∈ L²(λ_α)` is "the function whose partial Fourier transform in the bias is
`ρ̂(ω) G(-ωa)`".  The partial Fourier transform of an `L²` function is characterized through
Parseval's identity against Schwartz test functions in the bias variable together with the
square integrability of the transform along almost every ray (`HasBiasFourier`), and
`spectralCoefficient` is the element of `L²(λ_α)` with that property (junk value `0` if there is
none); Lemma 3.6 states existence, uniqueness, and the explicit formula `coefficientFormula`.

## Fourier convention

The one-dimensional Fourier transform `ρ̂(ω) = ∫ ρ(t) e^{-itω} dt` is the vendored
`LeanRidgelet.Fourier.angularFourierIntegralInner` on `ℝ`, not Mathlib's `𝓕` (which carries
`2π` in the exponent).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### Characters, the two Fourier transforms, and homogeneity -/

section Character

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The character `x ↦ exp(-i⟪x,ξ⟫)` used by the analysis map. -/
def character (ξ x : H) : ℂ :=
  Complex.exp (-((⟪x, ξ⟫ : ℝ) * Complex.I))

@[simp]
theorem character_zero_right (x : H) : character (0 : H) x = 1 := by
  simp [character]

@[simp]
theorem character_zero_left (ξ : H) : character ξ (0 : H) = 1 := by
  simp [character]

theorem continuous_character (ξ : H) : Continuous (character ξ) := by
  unfold character
  fun_prop

theorem norm_character (ξ x : H) : ‖character ξ x‖ = 1 := by
  have : -((⟪x, ξ⟫ : ℝ) * Complex.I) = ((-⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [character, this, Complex.norm_exp_ofReal_mul_I]

/-- The one-dimensional Fourier transform of a complex function in the convention of the
manuscript, `ĥ(ω) = ∫ h(t) exp(-itω) dt`. -/
def lineFourier (h : ℝ → ℂ) (ω : ℝ) : ℂ :=
  LeanRidgelet.Fourier.angularFourierIntegralInner h ω

/-- The Fourier transform `ρ̂(ω) = ∫ ρ(t) exp(-itω) dt` of a real filter. -/
def filterFourier (ρ : ℝ → ℝ) (ω : ℝ) : ℂ :=
  lineFourier (fun t => (ρ t : ℂ)) ω

@[simp]
theorem filterFourier_zero (ω : ℝ) : filterFourier 0 ω = 0 := by
  simp [filterFourier, lineFourier, LeanRidgelet.Fourier.angularFourierIntegralInner]

/-- The set `E_t` of the dilation obstruction: inputs whose normalized coordinate sums along the
eigenvectors `e_j` with eigenvalues `w_j` satisfy the strong law with limit `t`. -/
def strongLawSet (e : ℕ → H) (w : ℕ → ℝ) (t : ℝ) : Set H :=
  {x | Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ⟪x, e j⟫ ^ 2 / w j)
    atTop (𝓝 t)}

end Character

section Basic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The weighted Fourier transform `𝒢_μ f (ξ) = ∫ f(x) exp(-i⟪x,ξ⟫) dμ(x)`, the Fourier
transform of the finite complex measure `f μ`; for `μ = μ_Q` this is the manuscript's `𝒢_Q`. -/
def gaussFourier (μ : Measure H) (f : H → ℂ) (ξ : H) : ℂ :=
  ∫ x, f x * character ξ x ∂μ

@[simp]
theorem gaussFourier_zero (μ : Measure H) : gaussFourier μ 0 = 0 := by
  funext ξ
  simp [gaussFourier]

/-- The weighted Fourier transform of the constant function `1` is the characteristic
functional of `μ` at `-ξ`. -/
theorem gaussFourier_one (μ : Measure H) (ξ : H) :
    gaussFourier μ (fun _ => (1 : ℂ)) ξ = charFun μ (-ξ) := by
  simp only [gaussFourier, charFun, character, one_mul]
  congr 1
  funext x
  rw [inner_neg_right]
  push_cast
  ring_nf

/-- A measure on `H` is homogeneous of degree `α` when every dilation `D_ω a = ω a`, `ω ≠ 0`,
scales it by `|ω|^(-α)`: `(D_ω)_# ν = |ω|^{-α} ν`. -/
def IsHomogeneous (α : ℝ) (ν : Measure H) : Prop :=
  ∀ ω : ℝ, ω ≠ 0 → ν.map (fun a => ω • a) = ENNReal.ofReal (|ω| ^ (-α)) • ν

end Basic

/-! ### Covariance operators, centred Gaussian measures, and the Gaussian mixture -/

section Gaussian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H]

/-- The trace `∑ ⟪P e_i, e_i⟫` of `P` along the Hilbert basis `b`. -/
def traceAlong {ι : Type*} (b : HilbertBasis ι ℝ H) (P : H →L[ℝ] H) : ℝ :=
  ∑' i, ⟪P (b i), b i⟫

/-- `P` is trace class in the sense of the manuscript: `∑ ⟪P e_i, e_i⟫` converges along some
Hilbert basis. -/
def HasSummableTrace (P : H →L[ℝ] H) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι ℝ H), Summable fun i => ⟪P (b i), b i⟫

open Classical in
/-- The trace `tr P = ∑ ⟪P e_i, e_i⟫`, along a Hilbert basis for which the sum converges (`0`
if there is none); for a positive operator the value does not depend on the basis. -/
def traceOf (P : H →L[ℝ] H) : ℝ :=
  if h : HasSummableTrace P then traceAlong h.choose_spec.choose P else 0

/-- A positive, self-adjoint, trace-class operator: the hypothesis on `Σ` in Lemma
`lem:gaussian-quadratic`, and the covariance hypothesis `IsTraceClassCovariance` without
injectivity. -/
structure IsPositiveTraceClass (P : H →L[ℝ] H) : Prop where
  /-- `P` is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint P
  /-- `P` is positive: `⟪P x, x⟫ ≥ 0`. -/
  inner_nonneg : ∀ x, 0 ≤ ⟪P x, x⟫
  /-- `P` is trace class: `∑ ⟪P e_j, e_j⟫ < ∞` along a Hilbert basis. -/
  hasSummableTrace : HasSummableTrace P

/-- The standing hypothesis on the covariance operators `P` and `Q` of the manuscript: injective,
positive, self-adjoint, and trace class (`IsPositiveTraceClass` together with injectivity).  The
trace condition is expressed along a Hilbert basis; for a positive operator the sum
`∑ ⟪P e_j, e_j⟫` does not depend on the basis. -/
structure IsTraceClassCovariance (P : H →L[ℝ] H) : Prop extends IsPositiveTraceClass P where
  /-- `P` is injective. -/
  injective : Function.Injective P

/-- `μ = 𝒩(0,Q)`: the manuscript's centred Gaussian measure with covariance `Q` is the Borel
probability measure whose characteristic functional is `∫ e^{i⟪x,ξ⟫} dμ(x) = e^{-⟪Qξ,ξ⟫/2}`. -/
structure IsCenteredGaussian (Q : H →L[ℝ] H) (μ : Measure H) : Prop where
  /-- `μ` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- The characteristic functional of `μ` is `exp(-⟪Qξ,ξ⟫/2)`. -/
  charFun_eq : ∀ ξ, charFun μ ξ = Complex.exp (-((⟪Q ξ, ξ⟫ / 2 : ℝ) : ℂ))

/-- A family of Gaussian layers `N s = 𝒩(0, 2sP)` for `s > 0` (the value of `N` at `s ≤ 0` is
irrelevant).  The characteristic functional of `𝒩(0,2sP)` is `exp(-s⟪Pξ,ξ⟫)`. -/
def IsCenteredGaussianLayers (P : H →L[ℝ] H) (N : ℝ → Measure H) : Prop :=
  ∀ s : ℝ, 0 < s → IsCenteredGaussian ((2 * s) • P) (N s)

/-- The weight `s^{α/2-1} ds` restricted to a set `S` of scales. -/
def mixtureWeight (α : ℝ) (S : Set ℝ) : Measure ℝ :=
  (volume.restrict S).withDensity fun s => ENNReal.ofReal (s ^ (α / 2 - 1))

/-- The Gaussian mixture over a set `S` of scales, `∫_S 𝒩(0,2sP) s^{α/2-1} ds`, as the
Giry-monad bind of the weight `s^{α/2-1} ds` on `S` against the layers `N`. -/
def gaussianMixtureOn (N : ℝ → Measure H) (α : ℝ) (S : Set ℝ) : Measure H :=
  (mixtureWeight α S).bind N

/-- The homogeneous Gaussian mixture `ν_α = ∫₀^∞ 𝒩(0,2sP) s^{α/2-1} ds` of the manuscript. -/
def gaussianMixture (N : ℝ → Measure H) (α : ℝ) : Measure H :=
  gaussianMixtureOn N α (Set.Ioi 0)

end Gaussian

/-! ### Admissible filters -/

/-- The cross admissibility constant
`C^{(α)}_{ρ₁,ρ₂} = (2π)⁻¹ ∫ ρ̂₁(ω) conj(ρ̂₂(ω)) |ω|^{-α} dω`. -/
def crossAdmissibilityConst (α : ℝ) (ρ₁ ρ₂ : ℝ → ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, filterFourier ρ₁ ω * (starRingEnd ℂ) (filterFourier ρ₂ ω) *
      ((|ω| ^ (-α) : ℝ) : ℂ)

/-- The admissibility constant `C^{(α)}_ρ = (2π)⁻¹ ∫ |ρ̂(ω)|² |ω|^{-α} dω`. -/
def admissibilityConst (α : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ ω : ℝ, ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)

/-- A real Schwartz function `ρ` is `α`-admissible if `0 < C^{(α)}_ρ < ∞`; finiteness is the
integrability of `|ρ̂(ω)|² |ω|^{-α}`. -/
structure IsAdmissible (α : ℝ) (ρ : SchwartzMap ℝ ℝ) : Prop where
  /-- `C^{(α)}_ρ < ∞`. -/
  integrable : Integrable fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)
  /-- `0 < C^{(α)}_ρ`. -/
  pos : 0 < admissibilityConst α ρ

/-- A band-pass filter: a nonzero real Schwartz function whose Fourier transform lies in
`C_c^∞(ℝ ∖ {0})`.  (An analysis filter is admissible, hence nonzero; the nonvanishing is part
of the notion so that band-pass filters are `α`-admissible for every `α > 0`.) -/
structure IsBandPass (ρ : SchwartzMap ℝ ℝ) : Prop where
  /-- `ρ ≠ 0`. -/
  ne_zero : ρ ≠ 0
  /-- `ρ̂` is smooth. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) (filterFourier ρ)
  /-- `ρ̂` has compact support. -/
  hasCompactSupport : HasCompactSupport (filterFourier ρ)
  /-- The support of `ρ̂` stays away from the origin. -/
  zero_notMem_tsupport : (0 : ℝ) ∉ tsupport (filterFourier ρ)

/-! ### The transform, the parameter measure, and the coefficient operator -/

section Transform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The weighted ridgelet transform `R_ρ f (a,c) = ∫ f(x) ρ(⟪a,x⟫ + c) dμ(x)`. -/
def ridgelet (μ : Measure H) (ρ : ℝ → ℝ) (f : H → ℂ) (p : H × ℝ) : ℂ :=
  ∫ x, f x * (ρ (⟪p.1, x⟫ + p.2) : ℂ) ∂μ

@[simp]
theorem ridgelet_zero (μ : Measure H) (ρ : ℝ → ℝ) : ridgelet μ ρ 0 = 0 := by
  funext p
  simp [ridgelet]

/-- The parameter measure `λ = ν ⊗ dc` on `H × ℝ`. -/
def parameterMeasure (ν : Measure H) : Measure (H × ℝ) :=
  ν.prod volume

/-- The partial Fourier transform in the bias variable,
`γ̂(a,ω) = ∫ γ(a,c) exp(-iωc) dc`. -/
def biasFourier (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) : ℂ :=
  ∫ c : ℝ, γ (a, c) * Complex.exp (-((ω * c : ℝ) * Complex.I))

/-- The explicit coefficient
`γ_G(a,c) = (2π)⁻¹ ∫ ρ̂(ω) G(-ωa) exp(iωc) dω` of a spectral density `G`. -/
def coefficientFormula (ρ : ℝ → ℝ) (G : H → ℂ) (p : H × ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, filterFourier ρ ω * G (-(ω • p.1)) * Complex.exp ((ω * p.2 : ℝ) * Complex.I)

/-- `HasBiasFourier ν γ Φ` says that the partial Fourier transform of `γ` in the bias is `Φ`:
for `ν`-almost every direction `a`, the ray function `Φ(a,·)` is square integrable and
Parseval's identity `∫ γ(a,c) conj(φ(c)) dc = (2π)⁻¹ ∫ Φ(a,ω) conj(φ̂(ω)) dω` holds for every
Schwartz test function `φ` on `ℝ`.  This characterizes `Φ(a,·)` up to a null set as the `L²`
Fourier transform of `γ(a,·)` (`HasBiasFourier.ae_ae_eq`), and for `γ ∈ L²(λ)` such a
representative exists and can be chosen jointly measurable
(`exists_measurable_hasBiasFourier`).

The square-integrability clause is essential.  Parseval's identity alone says nothing about
`Φ(a,·)` where the integrand `Φ(a,ω) conj(φ̂(ω))` fails to be integrable, since Lean's Bochner
integral of a non-integrable function is `0`: without the clause an arbitrary non-integrable
function would be a "representative" of every coefficient, and the ray average
`backprojectionOf` computed from it would be meaningless.  With the clause all representatives
of `γ` agree almost everywhere on almost every ray, so that `backprojection` does not depend on
the choice (Proposition `prop:coefficient-projection`(ii)). -/
structure HasBiasFourier (ν : Measure H) (γ : H × ℝ → ℂ) (Φ : H → ℝ → ℂ) : Prop where
  /-- `Φ(a,·) ∈ L²(ℝ)` for `ν`-almost every direction `a`. -/
  memLp : ∀ᵐ a ∂ν, MemLp (Φ a) 2 volume
  /-- Parseval's identity against Schwartz test functions, for `ν`-almost every direction. -/
  parseval : ∀ᵐ a ∂ν, ∀ φ : SchwartzMap ℝ ℂ,
    ∫ c : ℝ, γ (a, c) * (starRingEnd ℂ) (φ c) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ ω : ℝ, Φ a ω * (starRingEnd ℂ) (lineFourier φ ω)

open Classical in
/-- The coefficient operator `W_ρ G ∈ L²(λ)`: the element of `L²(λ)` whose partial Fourier
transform in the bias is `(a,ω) ↦ ρ̂(ω) G(-ωa)`, and `0` if there is none. -/
def spectralCoefficient (ν : Measure H) (ρ : ℝ → ℝ) (G : H → ℂ) :
    Lp ℂ 2 (parameterMeasure ν) :=
  if h : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) then
    h.choose
  else 0

end Transform

/-! ### The spectral space -/

section SpectralSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

theorem gaussFourier_smul (μ : Measure H) (c : ℂ) (f : Lp ℂ 2 μ) :
    gaussFourier μ ((c • f : Lp ℂ 2 μ) : H → ℂ) = c • gaussFourier μ f := by
  funext ξ
  simp only [gaussFourier, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem gaussFourier_zero' (μ : Measure H) :
    gaussFourier μ ((0 : Lp ℂ 2 μ) : H → ℂ) = 0 := by
  funext ξ
  simp only [gaussFourier, Pi.zero_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
  rw [hx]
  simp

/-- The spectral inner product `⟨f,g⟩_𝓔 = ∫ 𝒢_μ f conj(𝒢_μ g) dν`, linear in the first
argument as in the manuscript. -/
def spectralInner (μ ν : Measure H) (f g : H → ℂ) : ℂ :=
  ∫ ξ, gaussFourier μ f ξ * (starRingEnd ℂ) (gaussFourier μ g ξ) ∂ν

variable [OpensMeasurableSpace H]

theorem integrable_mul_character (μ : Measure H) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) (ξ : H) :
    Integrable (fun x => (f : H → ℂ) x * character ξ x) μ :=
  ((Lp.memLp f).integrable one_le_two).mul_unimodular
    (continuous_character ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_character ξ x).le)

theorem gaussFourier_add (μ : Measure H) [IsFiniteMeasure μ] (f g : Lp ℂ 2 μ) :
    gaussFourier μ ((f + g : Lp ℂ 2 μ) : H → ℂ) = gaussFourier μ f + gaussFourier μ g := by
  funext ξ
  simp only [gaussFourier, Pi.add_apply]
  rw [← integral_add (integrable_mul_character μ f ξ) (integrable_mul_character μ g ξ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx, Pi.add_apply, add_mul]

/-- The core `𝒟 = {f ∈ L²(μ) : 𝒢_μ f ∈ L²(ν)}` (the manuscript's `𝒟_α` for `ν = ν_α`), as a
submodule of `L²(μ)`. -/
def spectralCore (μ ν : Measure H) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (gaussFourier μ f) 2 ν}
  add_mem' {f g} hf hg := by
    change MemLp (gaussFourier μ ((f + g : Lp ℂ 2 μ) : H → ℂ)) 2 ν
    rw [gaussFourier_add]
    exact MemLp.add hf hg
  zero_mem' := by
    change MemLp (gaussFourier μ ((0 : Lp ℂ 2 μ) : H → ℂ)) 2 ν
    rw [gaussFourier_zero']
    exact MemLp.zero
  smul_mem' c {f} hf := by
    change MemLp (gaussFourier μ ((c • f : Lp ℂ 2 μ) : H → ℂ)) 2 ν
    rw [gaussFourier_smul]
    exact MemLp.const_smul hf c

theorem mem_spectralCore_iff (μ ν : Measure H) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    f ∈ spectralCore μ ν ↔ MemLp (gaussFourier μ f) 2 ν :=
  Iff.rfl

/-- `𝒢_μ f` as an element of `L²(ν)`, for `f ∈ 𝒟`. -/
def gaussFourierLp (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralCore μ ν) : Lp ℂ 2 ν :=
  MemLp.toLp (gaussFourier μ f) f.2

/-- The closed subspace `𝒦 = closure (𝒢_μ 𝒟) ⊆ L²(ν)` (the manuscript's `𝒦_α`), which
represents the Hilbert space `𝓔_α` in this formalization. -/
def spectralRange (μ ν : Measure H) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 ν) :=
  (Submodule.span ℂ (Set.range (gaussFourierLp μ ν))).topologicalClosure

/-- The map `U : 𝒟 → 𝒦`, `f ↦ 𝒢_μ f`; the unitary `U_α : 𝓔_α → 𝒦_α` of the manuscript is
its extension to the completion, which is the identity of `𝒦` in this representation. -/
def spectralEmbed (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralCore μ ν) :
    spectralRange μ ν :=
  ⟨gaussFourierLp μ ν f,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)⟩

end SpectralSpace

end OperatorRidgelet
