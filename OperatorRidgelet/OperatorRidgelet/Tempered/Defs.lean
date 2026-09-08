import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Network.Defs
import LeanRidgelet.Fourier.AngularDistribution
import LeanRidgelet.Fourier.AngularLp
import LeanRidgelet.Space.Activation
import LeanRidgelet.Activation.ReLU
import LeanRidgelet.Activation.Tanh
import LeanRidgelet.Activation.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Definitions for Section 5 (tempered synthesis activations and ReLU) and Appendix C

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

## Tempered distributions

A synthesis activation is a tempered distribution `β : TemperedDistribution ℝ ℂ` (Mathlib's
`𝓢'(ℝ, ℂ)`), whose Fourier transform in the manuscript's convention is the vendored
`angularFourierDistribution`.  The manuscript's "real `β ∈ 𝒮'(ℝ)`" is `IsRealDistribution`:
`β` is fixed by the distributional conjugation `conj u [φ] = conj (u [conj φ])`
(`temperedDistributionConjugation`), equivalently `β` pairs real test functions to real numbers.
"`β` is a polynomial", equivalently `β = 0` in `𝒮'/𝒫`, is `IsPolynomialDistribution`: `β` acts by
integration against a polynomial.

## Regularized synthesis (Definition `def:regularized-synthesis`)

The cutoff `χ` and the approximate identity `(η_ε)_{ε>0}` are functions `ℝ → ℝ` and
`ℝ → ℝ → ℝ` with the predicates `IsCutoff ρ χ` (even, `C_c^∞(ℝ ∖ {0})`, equal to one on a
neighbourhood of `supp ρ̂`) and `IsApproximateIdentity η` (each `η_ε`, `ε > 0`, is smooth,
compactly supported, even, nonnegative, with integral one, and the supports shrink to `{0}` as
`ε ↓ 0`; a mollifier `η_ε = ε⁻¹ η(·/ε)` is the standard instance).  The convolution of a
tempered distribution with a test function is `(u * η)(ω) = ⟨u, η(ω - ·)⟩`
(`distributionConvolution`), the regularized spectrum is `β̂_ε = χ (β̂ * η_ε)`
(`regularizedSpectrum`), and `β_ε` (`regularizedActivation`) is the real Schwartz function with
this Fourier transform, obtained by choice (junk `0` if none; uniqueness follows from Fourier
injectivity).  The claims implicit in the definition (existence of `χ` and `(η_ε)`, membership
`β̂_ε ∈ C_c^∞(ℝ ∖ {0})`, existence and uniqueness of `β_ε`, well-definedness of `S_{β_ε} γ`) are
the theorems `OperatorRidgelet.Paper.def_regularized_synthesis_*`.

## The anti-dual `𝓔_α'`, the extended transform, synthesis, and the Riesz map

Section 4 defines `𝓔_α'` as the continuous *anti-dual* of `𝓔_α`, `S_ρ := R_ρ'` and the Riesz
map `T_α = J_α`, `J_α f [g] = ⟨f, g⟩_{𝓔_α}`.  These objects belong to the reconstruction work
package; the minimal versions needed here live in the namespace `OperatorRidgelet.Tempered`
(to be unified with `Reconstruction/Defs.lean`):

* `Tempered.spectralAntiDual μ ν := spectralRange μ ν →L⋆[ℂ] ℂ`, continuous conjugate-linear
  functionals on `𝒦_α` (which represents `𝓔_α`, see `Transform/Defs.lean`), a normed space.
  In a linear-dual representation (`NormedSpace.Dual ℂ 𝒦`) every functional below is replaced
  by its complex conjugate and `T_α` by `InnerProductSpace.toDual ℂ 𝒦`.
* `Tempered.ridgeletExtension μ ν ρ G := W_ρ G` is the bounded extension `R_ρ : 𝓔_α → L²(λ)`
  of Theorem B(ii): `R_ρ = W_ρ U_α` and `U_α` is the identity of `𝒦_α` in this representation.
* `Tempered.synthesisFunctional μ ν ρ γ` is `S_ρ γ = R_ρ' γ`, the continuous anti-linear
  functional `g ↦ ⟨γ, R_ρ g⟩_{L²(λ)}` (in Mathlib's inner product, conjugate linear in the first
  slot, this is `inner ℂ (R_ρ g) γ`), obtained by choice (junk `0` if none).
* `Tempered.rieszMap μ ν := innerSLFlip ℂ`, `f ↦ (g ↦ ⟪g, f⟫) = (g ↦ ⟨f, g⟩_{𝓔_α})`, and
  `Tempered.rieszInv μ ν` its inverse, obtained by choice (junk `0` off the range, which is all
  of `𝓔_α'` by the Riesz representation theorem).

The regularized synthesis `S_{β_ε} γ := R'_{β_ε} γ` is `regularizedSynthesis`, and the synthesis
with `β` is `temperedSynthesis μ ν β χ η γ := lim_{ε ↓ 0} S_{β_ε} γ` in `𝓔_α'`, obtained by choice
whenever the limit exists (junk `0` otherwise).

## Standard activations and the weighted Sobolev spaces (Appendix C)

ReLU and `tanh` are the vendored realizations `reluTemperedDistribution` and
`tanhTemperedDistribution` (with weight exponent `t = 2`); the Gaussian distribution function
`Φ` and the Gaussian `e^{-u²/2}` are realized through the same weighted construction
`weightedDistribution t β = ⟨x⟩^t (⟨x⟩^{-t} β)` with `⟨x⟩^{-t} β ∈ L²(ℝ)`, which acts by
integration against `β`.  "`β ∈ 𝒜_{s,t}`" for a function `β` is `MemActivationSpaceFun s t β`:
some tempered distribution acting by integration against `β` satisfies the vendored
`MemActivationSpace s t`.  The coordinate `⟨ω⟩^s B^{-t} β̂` of the manuscript's isometry
`𝒜_{s,t} → L²(ℝ)` is `activationFourierCoordinate` (as a distribution) and
`activationCoordinate` (as the `L²` element representing it, by choice), the norm
`‖β‖_{𝒜_{s,t}}` is `activationNorm`, and the dual test norm `‖r‖_{ℋ^♯_{s,t}}` is
`testFilterNorm`, with `testFilterCoordinate r = ⟨ω⟩^{-s} B^t r`.  The Bessel operator `B^q` on
the frequency variable is the vendored `angularBesselPotential q` on distributions and
`SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol q)` on Schwartz functions.

## Regularity along rays (Definition `def:ray-regular`, minimal local version)

`Tempered.IsRayRegular ν I G` and the target `Tempered.spectralTarget ν G = g_G` are the minimal
versions of the Section 4 objects needed to state that Theorem A(iii) holds with ReLU synthesis
(Corollary `cor:relu-admissible`); they belong to the reconstruction work package and are to be
unified with `Reconstruction/Defs.lean`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped ENNReal RealInnerProductSpace

/-! ### Real tempered distributions, polynomials, and Schwartz functions by choice -/

/-- `β ∈ 𝒮'(ℝ)` is real: it is fixed by the distributional conjugation
`conj u [φ] = conj (u [conj φ])`; equivalently, `β` pairs real test functions to real numbers. -/
def IsRealDistribution (β : TemperedDistribution ℝ ℂ) : Prop :=
  temperedDistributionConjugation β = β

/-- `β ∈ 𝒮'(ℝ)` is a polynomial (`β = 0` in `𝒮'/𝒫`): it acts by integration against the
evaluation of some `p : ℂ[X]`. -/
def IsPolynomialDistribution (β : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ p : Polynomial ℂ, ∀ φ : SchwartzMap ℝ ℂ, β φ = ∫ x : ℝ, φ x * p.eval (x : ℂ)

open Classical in
/-- The Schwartz function with the values `f`, when one exists; `0` otherwise. -/
def schwartzOfFun (f : ℝ → ℂ) : SchwartzMap ℝ ℂ :=
  if h : ∃ φ : SchwartzMap ℝ ℂ, ⇑φ = f then h.choose else 0

/-- The convolution `(u * η)(ω) = ⟨u, η(ω - ·)⟩` of a tempered distribution `u` with a test
function `η` (smooth and compactly supported in the applications). -/
def distributionConvolution (u : TemperedDistribution ℝ ℂ) (η : ℝ → ℝ) (ω : ℝ) : ℂ :=
  u (schwartzOfFun fun x : ℝ => ((η (ω - x) : ℝ) : ℂ))

/-! ### Cutoffs, approximate identities, and the regularized activations -/

/-- An even `χ ∈ C_c^∞(ℝ ∖ {0})` equal to one on a neighbourhood of `supp ρ̂`. -/
structure IsCutoff (ρ : SchwartzMap ℝ ℝ) (χ : ℝ → ℝ) : Prop where
  /-- `χ` is smooth. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) χ
  /-- `χ` has compact support. -/
  hasCompactSupport : HasCompactSupport χ
  /-- The support of `χ` stays away from the origin. -/
  zero_notMem_tsupport : (0 : ℝ) ∉ tsupport χ
  /-- `χ` is even. -/
  even : ∀ ω : ℝ, χ (-ω) = χ ω
  /-- `χ = 1` on a neighbourhood of `supp ρ̂`. -/
  eventuallyEq_one : ∀ᶠ ω in 𝓝ˢ (tsupport (filterFourier ρ)), χ ω = 1

/-- An even, compactly supported, smooth approximate identity `(η_ε)_{ε>0}`: for every `ε > 0`
the function `η_ε` is smooth, compactly supported, even, nonnegative, with integral one, and the
supports shrink to `{0}` as `ε ↓ 0`.  (The values of `η` at `ε ≤ 0` are irrelevant.) -/
structure IsApproximateIdentity (η : ℝ → ℝ → ℝ) : Prop where
  /-- Each `η_ε` is smooth. -/
  contDiff : ∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) (η ε)
  /-- Each `η_ε` has compact support. -/
  hasCompactSupport : ∀ ε : ℝ, 0 < ε → HasCompactSupport (η ε)
  /-- Each `η_ε` is even. -/
  even : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, η ε (-x) = η ε x
  /-- Each `η_ε` is nonnegative. -/
  nonneg : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 ≤ η ε x
  /-- Each `η_ε` has integral one. -/
  integral_eq_one : ∀ ε : ℝ, 0 < ε → ∫ x : ℝ, η ε x = 1
  /-- The supports of `η_ε` shrink to `{0}` as `ε ↓ 0`. -/
  tendsto_tsupport : Tendsto (fun ε : ℝ => tsupport (η ε)) (𝓝[>] 0) (𝓝 (0 : ℝ)).smallSets

/-- The regularized spectrum `β̂_ε = χ (β̂ * η_ε)` of a tempered activation `β`. -/
def regularizedSpectrum (β : TemperedDistribution ℝ ℂ) (χ : ℝ → ℝ) (η : ℝ → ℝ → ℝ) (ε : ℝ)
    (ω : ℝ) : ℂ :=
  (χ ω : ℂ) * distributionConvolution (angularFourierDistribution β) (η ε) ω

open Classical in
/-- The regularized activation `β_ε`: the real Schwartz function with `β̂_ε = χ (β̂ * η_ε)`
(unique by Fourier injectivity), and `0` if there is none. -/
def regularizedActivation (β : TemperedDistribution ℝ ℂ) (χ : ℝ → ℝ) (η : ℝ → ℝ → ℝ) (ε : ℝ) :
    SchwartzMap ℝ ℝ :=
  if h : ∃ b : SchwartzMap ℝ ℝ, ∀ ω : ℝ, filterFourier b ω = regularizedSpectrum β χ η ε ω then
    h.choose
  else 0

/-! ### The anti-dual `𝓔_α'`, the extended transform, synthesis, and the Riesz map -/

namespace Tempered

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- The continuous anti-dual `𝓔_α'` of `𝓔_α`, represented by the continuous conjugate-linear
functionals on `𝒦_α = spectralRange μ ν`. -/
abbrev spectralAntiDual (μ ν : Measure H) [IsFiniteMeasure μ] : Type _ :=
  spectralRange μ ν →L⋆[ℂ] ℂ

/-- The bounded extension `R_ρ : 𝓔_α → L²(λ)` of the transform (Theorem B(ii)): in the
representation `𝓔_α ≅ 𝒦_α` it is `R_ρ = W_ρ U_α` with `U_α` the identity of `𝒦_α`, so
`R_ρ G = W_ρ G`. -/
def ridgeletExtension (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) (G : spectralRange μ ν) :
    Lp ℂ 2 (parameterMeasure ν) :=
  spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ)

open Classical in
/-- Synthesis with the filter `ρ` as the transpose of the transform, `S_ρ γ = R_ρ' γ ∈ 𝓔_α'`,
`(S_ρ γ)[g] = ⟨γ, R_ρ g⟩_{L²(λ)}` (conjugate linear in `g`): the continuous anti-linear
functional with these values, and `0` if there is none. -/
def synthesisFunctional (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)
    (γ : Lp ℂ 2 (parameterMeasure ν)) : spectralAntiDual μ ν :=
  if h : ∃ F : spectralAntiDual μ ν, ∀ g : spectralRange μ ν,
      F g = inner ℂ (ridgeletExtension μ ν ρ g) γ then
    h.choose
  else 0

/-- The Riesz map `T_α = J_α : 𝓔_α → 𝓔_α'`, `T_α f [g] = ⟨f, g⟩_{𝓔_α}`, which in Mathlib's inner
product (conjugate linear in the first slot) is `f ↦ (g ↦ ⟪g, f⟫)`. -/
def rieszMap (μ ν : Measure H) [IsFiniteMeasure μ] :
    spectralRange μ ν →L[ℂ] spectralAntiDual μ ν :=
  innerSLFlip ℂ

open Classical in
/-- The inverse `T_α⁻¹ : 𝓔_α' → 𝓔_α` of the Riesz map, obtained by choice (junk `0` off the
range, which is all of `𝓔_α'` by the Riesz representation theorem). -/
def rieszInv (μ ν : Measure H) [IsFiniteMeasure μ] (F : spectralAntiDual μ ν) :
    spectralRange μ ν :=
  if h : ∃ f : spectralRange μ ν, rieszMap μ ν f = F then h.choose else 0

/-- The target `g_G(x) = ∫ e^{i⟪x,ξ⟫} G(ξ) ν(dξ)` with spectral density `G` (minimal local
version of the Section 4 object). -/
def spectralTarget (ν : Measure H) (G : H → ℂ) (x : H) : ℂ :=
  ∫ ξ, Complex.exp (((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * G ξ ∂ν

/-- The ray bound `max_{k ≤ m} sup_{ω ∈ I} |∂_ω^k G(ω a)|` of Definition `def:ray-regular`. -/
def rayDerivBound (I : Set ℝ) (m : ℕ) (G : H → ℂ) (a : H) : ℝ :=
  ⨆ k : Fin (m + 1), ⨆ ω ∈ I, ‖iteratedDeriv (k : ℕ) (fun ω : ℝ => G (ω • a)) ω‖

/-- `G` is regular along rays with respect to the symmetric compact set `I ⊆ ℝ ∖ {0}`
(Definition `def:ray-regular`, minimal local version): `G` is bounded Borel, for every `a` the
function `ω ↦ G(ωa)` is `C^∞` on a neighbourhood of `I`, and for every `m ≥ 0`
`M_m(G) = ∫ (1 + ‖a‖)^{m+2} max_{k ≤ m} sup_{ω ∈ I} |∂_ω^k G(ωa)| ν(da) < ∞`. -/
structure IsRayRegular (ν : Measure H) (I : Set ℝ) (G : H → ℂ) : Prop where
  /-- `G` is Borel. -/
  measurable : Measurable G
  /-- `G` is bounded. -/
  bounded : ∃ M : ℝ, ∀ ξ : H, ‖G ξ‖ ≤ M
  /-- `ω ↦ G(ωa)` is `C^∞` on a neighbourhood of `I`. -/
  contDiffOn : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U
  /-- `M_m(G) < ∞` for every `m`. -/
  integrable : ∀ m : ℕ, Integrable (fun a : H => (1 + ‖a‖) ^ (m + 2) * rayDerivBound I m G a) ν

end Tempered

section Synthesis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- The regularized synthesis `S_{β_ε} γ := R'_{β_ε} γ ∈ 𝓔_α'`. -/
def regularizedSynthesis (μ ν : Measure H) [IsFiniteMeasure μ] (β : TemperedDistribution ℝ ℂ)
    (χ : ℝ → ℝ) (η : ℝ → ℝ → ℝ) (ε : ℝ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    Tempered.spectralAntiDual μ ν :=
  Tempered.synthesisFunctional μ ν (regularizedActivation β χ η ε) γ

open Classical in
/-- The synthesis with the tempered activation `β`, `S_β γ := lim_{ε ↓ 0} S_{β_ε} γ` in
`𝓔_α'`, whenever the limit exists (and `0` otherwise). -/
def temperedSynthesis (μ ν : Measure H) [IsFiniteMeasure μ] (β : TemperedDistribution ℝ ℂ)
    (χ : ℝ → ℝ) (η : ℝ → ℝ → ℝ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    Tempered.spectralAntiDual μ ν :=
  if h : ∃ F : Tempered.spectralAntiDual μ ν,
      Tendsto (fun ε : ℝ => regularizedSynthesis μ ν β χ η ε γ) (𝓝[>] 0) (𝓝 F) then
    h.choose
  else 0

end Synthesis

/-! ### Standard activations -/

open Classical in
/-- The tempered distribution `⟨x⟩^t (⟨x⟩^{-t} β)` of a function `β` of polynomial growth with
`⟨x⟩^{-t} β ∈ L²(ℝ)` (and `0` otherwise); it acts by integration against `β`. -/
def weightedDistribution (t : ℝ) (β : ℝ → ℝ) : TemperedDistribution ℝ ℂ :=
  if h : MemLp (fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) 2 volume then
    temperedWeightMultiplier t
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (h.toLp fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)))
  else 0

/-- `ReLU ∈ 𝒮'(ℝ)`, the vendored realization `reluTemperedDistribution` (weight exponent
`t = 2`), which acts by integration against `ReLU(t) = max(t, 0)`. -/
def reluDistribution : TemperedDistribution ℝ ℂ :=
  reluTemperedDistribution 2 (by norm_num)

/-- `tanh ∈ 𝒮'(ℝ)`, the vendored realization `tanhTemperedDistribution` (weight exponent
`t = 2`), which acts by integration against `tanh`. -/
def tanhDistribution : TemperedDistribution ℝ ℂ :=
  tanhTemperedDistribution 2 (by norm_num)

/-- The Gaussian distribution function `Φ(u) = ∫_{-∞}^u (2π)^{-1/2} e^{-v²/2} dv`. -/
def gaussianCdf (u : ℝ) : ℝ :=
  ∫ v in Set.Iic u, ProbabilityTheory.gaussianPDFReal 0 1 v

/-- `Φ ∈ 𝒮'(ℝ)`, the weighted realization of the Gaussian distribution function. -/
def gaussianCdfDistribution : TemperedDistribution ℝ ℂ :=
  weightedDistribution 2 gaussianCdf

/-- The Gaussian activation `u ↦ e^{-u²/2}`. -/
def gaussianFun (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / 2)

/-- `e^{-u²/2} ∈ 𝒮'(ℝ)`, the weighted realization of the Gaussian activation. -/
def gaussianDistribution : TemperedDistribution ℝ ℂ :=
  weightedDistribution 2 gaussianFun

/-- A function `β : ℝ → ℝ` belongs to `𝒜_{s,t}`: some tempered distribution acting by
integration against `β` lies in `𝒜_{s,t}` (vendored `MemActivationSpace`). -/
def MemActivationSpaceFun (s t : ℝ) (β : ℝ → ℝ) : Prop :=
  ∃ u : TemperedDistribution ℝ ℂ,
    (∀ φ : SchwartzMap ℝ ℂ, u φ = ∫ x : ℝ, φ x * (β x : ℂ)) ∧ MemActivationSpace s t u

/-! ### ReLU admissibility constants -/

/-- The ReLU admissibility constant `-(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω` of a filter with real `ρ̂`. -/
def reluAdmissibilityScale (α : ℝ) (ρ : SchwartzMap ℝ ℝ) : ℝ :=
  -((2 * Real.pi)⁻¹ * ∫ ω : ℝ, (filterFourier ρ ω).re * |ω| ^ (-α - 2))

/-- The filter `ρ` rescaled so that `C^{(α)}_{ReLU,ρ} = 1`. -/
def reluNormalizedFilter (α : ℝ) (ρ : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (reluAdmissibilityScale α ρ)⁻¹ • ρ

/-! ### Weighted Sobolev activation spaces -/

/-- The coordinate `⟨ω⟩^s B^{-t} β̂` of `β` under the manuscript's isometry
`𝒜_{s,t} → L²(ℝ)`, as a tempered distribution. -/
def activationFourierCoordinate (s t : ℝ) (β : TemperedDistribution ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  temperedWeightMultiplier s (angularBesselPotential (-t) (angularFourierDistribution β))

open Classical in
/-- The `L²(ℝ)` element representing `⟨ω⟩^s B^{-t} β̂`, when there is one (i.e. when
`β ∈ 𝒜_{s,t}`), and `0` otherwise. -/
def activationCoordinate (s t : ℝ) (β : TemperedDistribution ℝ ℂ) : L2 ℝ volume :=
  if h : ∃ σ : L2 ℝ volume,
      Lp.toTemperedDistributionCLM ℂ volume 2 σ = activationFourierCoordinate s t β then
    h.choose
  else 0

/-- The norm `‖β‖_{𝒜_{s,t}} = ‖⟨ω⟩^s B^{-t} β̂‖_{L²}`. -/
def activationNorm (s t : ℝ) (β : TemperedDistribution ℝ ℂ) : ℝ :=
  ‖activationCoordinate s t β‖

/-- The test coordinate `⟨ω⟩^{-s} B^t r` of a Schwartz test filter `r`. -/
def testFilterCoordinate (s t : ℝ) (r : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s))
    (SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol t) r)

/-- The dual test norm `‖r‖_{ℋ^♯_{s,t}} = ‖⟨ω⟩^{-s} B^t r‖_{L²}`. -/
def testFilterNorm (s t : ℝ) (r : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(testFilterCoordinate s t r).toLp 2 volume‖

end OperatorRidgelet
