import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Network.Defs
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Definitions for Section 4 (representation and reconstruction) and Appendix B

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.  They build on the Section 3 objects of `OperatorRidgelet.Transform.Defs` (`gaussFourier`,
`ridgelet`, `coefficientFormula`, `spectralCoefficient`, `spectralCore`, `spectralRange`,
`spectralEmbed`) and on the distributional constant of `OperatorRidgelet.Tempered.Const`.

## Targets with a spectral density and regularity along rays

* `spectralTarget ν G` is `g_G(x) = ∫ e^{i⟪x,ξ⟫} G(ξ) ν(dξ)`, stated for a density `G` with
  values in any complex normed space (the scalar case is `Y = ℂ`, where `•` is `*`).
* The compact symmetric set `I ⊆ ℝ ∖ {0}` containing `supp ρ̂` that the manuscript fixes before
  Definition `def:ray-regular` is the predicate `IsFrequencyWindow ρ I`.
* `rayDerivBound I G m a = max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖` and the moment
  `rayMoment ν I G m = M_m(G)` are taken in `ℝ≥0∞`, so that "`M_m(G) < ∞`" is literally
  `rayMoment ν I G m < ⊤`; `IsRegularAlongRays ν I G` bundles boundedness, Borel measurability
  (`StronglyMeasurable`, which is Borel measurability for separable targets), smoothness of
  `ω ↦ G(ωa)` on an open neighbourhood of `I`, and the finiteness of every `M_m(G)`.

## Tempered synthesis activations

A tempered distribution `β ∈ 𝒮'(ℝ)` "that is a continuous function of polynomial growth" is
represented by the pair of `β : TemperedDistribution ℝ ℂ` and a function `b : ℝ → ℝ` with
`IsTemperedFunction β b`: `b` is continuous, of polynomial growth (`HasPolynomialGrowth b` of
`OperatorRidgelet.Network.Defs`), and `β` is integration against `b`.  The distributional
constant `C^{(α)}_{β,ρ}` is `temperedAdmissibilityConst α β ρ` of
`OperatorRidgelet.Tempered.Const`; the bias integrals use the function `b`.

## The frame operator, the synthesis operator, and the reconstruction formulas

`𝓔_α` is represented by `𝒦_α = spectralRange μ ν ⊆ L²(ν)` (see `OperatorRidgelet.Transform.Defs`),
and `U_α` is the inclusion.  The manuscript's continuous anti-dual `𝓔_α'` is taken literally as
the space `SpectralAntiDual μ ν = spectralRange μ ν →L⋆[ℂ] ℂ` of continuous conjugate-linear
functionals, so that the values of all functionals agree with the manuscript without
conjugation (Mathlib's inner product is conjugate linear in the first argument, the
manuscript's in the second; `innerSLFlip ℂ f g = ⟪g, f⟫ = ⟨f,g⟩_manuscript`):

* `rieszMap μ ν = J_α`, `J_α f [g] = ⟨f,g⟩_𝓔`, is `innerSLFlip ℂ`; `rieszInv μ ν = J_α⁻¹` is the
  Riesz representation, obtained from Mathlib's `InnerProductSpace.toDual` after conjugating the
  functional (`antiDualConj`).
* `transposeEmbed μ ν F = U_α' F`, `U_α' F [g] = ⟨F, U_α g⟩_{L²(ν)}`.
* `frameOperator μ ν f = T_α f = U_α' U_α f`; Theorem `thm:C`(i) says `T_α = J_α`, so `T_α⁻¹`
  is `rieszInv`.
* `ridgeletExtension μ ν ρ` is the bounded extension `R_ρ : 𝓔_α → L²(λ)` of Theorem `thm:B`(ii):
  the continuous linear map agreeing almost everywhere with `f ↦ R_ρ f` on `U_α(𝒟_α)`, chosen
  when one exists and `0` otherwise (existence and uniqueness are Theorem `thm:B`(ii), a theorem
  and not a definition); `ridgeletRange μ ν ρ = Ran R_ρ`.
* `synthesis μ ν ρ γ = S_ρ γ = R_ρ' γ`, `(S_ρ γ)[g] = ⟨γ, R_ρ g⟩_{L²(λ)}` (`eq:weak-synthesis`).

These are the only definitions of `𝓔_α'`, `R_ρ` on `𝓔_α`, `S_ρ`, `J_α`, `J_α⁻¹`, `g_G`, and
regularity along rays in the library: Section 5 (`OperatorRidgelet.Tempered.Defs`, the
regularized and tempered synthesis `S_{β_ε}`, `S_β`, and Corollary `cor:relu-admissible`) and
Section 7 (`OperatorRidgelet.Examples.Defs`) build on them.

## Backprojection, coefficient projection, and the Hermite inverse

* `backprojectionOf α ρ Φ ξ` is the ray average `eq:ray-average` computed from a partial
  bias-Fourier representative `Φ` of the coefficient; `backprojection α ν ρ γ = Λ_ρ γ` uses a
  jointly measurable representative of `γ ∈ L²(λ)` chosen through `HasBiasFourier` (`0` if there
  is none), which requires the representative to be square integrable along almost every ray;
  Proposition `prop:coefficient-projection` states that the choice is immaterial.
  `backprojectionLp` is `Λ_ρ γ` as an element of `L²(ν)` and `coefficientProjection` is
  `Π_ρ = C⁻¹ W_ρ P_{𝒦_α} Λ_ρ`.  The space `𝒴` of Appendix B is `L²(λ)`: the norm defined
  through the partial Fourier transform in the bias coincides with the `L²(λ)`-norm by
  Plancherel.
* `gaussFourierLine μ f ξ z = 𝒢_μ f(zξ) = ∫ f(x) e^{-iz⟪x,ξ⟫} μ(dx)` for complex `z` is the
  analytic continuation of `z ↦ 𝒢_μ f(zξ)`; `hermiteExtension μ Q f ξ z = e^{z²τ(ξ)²/2} 𝒢_μ f(zξ)`
  with `τ(ξ)² = ⟪Qξ,ξ⟫`; `hermiteCoefficient μ Q f ξ n = E_μ[f He_n(⟪x,ξ⟫/τ(ξ))]` with the
  probabilists' Hermite polynomials `Polynomial.hermite` of Mathlib (`He_{n+1} = X He_n - He_n'`).
* `gaussFourierInv μ ν = Δ_Q`, the inverse of `𝒢_μ` on its range on `𝒟`, chosen as the element
  of `𝒟` with the given transform (unique by Theorem `thm:C`(iv)) and `0` otherwise.

## Vector-valued targets

For a complex Hilbert space `Y` the `Y`-valued versions of the Section 3 and Section 4 objects
carry the suffix `Vec` (`gaussFourierVec`, `ridgeletVec`, `coefficientFormulaVec`,
`biasFourierVec`, `HasBiasFourierVec`, `spectralCoefficientVec`, `spectralInnerVec`, `spectralCoreVec`,
`spectralRangeVec`, `spectralEmbedVec`, `ridgeletExtensionVec`, `SpectralAntiDualVec`,
`rieszMapVec`, `rieszInvVec`, `transposeEmbedVec`, `frameOperatorVec`, `synthesisVec`,
`backprojectionOfVec`, `backprojectionVec`, `coefficientProjectionVec`, `gaussFourierLineVec`,
`hermiteExtensionVec`, `hermiteCoefficientVec`, `gaussFourierInvVec`); scalar integrals become
Bochner integrals and products `f(x) φ(x)` become `φ(x) • f(x)`.  `spectralTarget`,
`IsRegularAlongRays`, and `integralNetworkDensity` are already polymorphic in the target.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### Targets with a spectral density and regularity along rays -/

section SpectralTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The target with spectral density `G` with respect to `ν`,
`g_G(x) = ∫ e^{i⟪x,ξ⟫} G(ξ) ν(dξ)` (`eq:spectral-target`), the Fourier transform of the finite
measure `G ν`; for a scalar density `•` is the product. -/
def spectralTarget (ν : Measure H) (G : H → Y) (x : H) : Y :=
  ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ ∂ν

/-- The frequency window fixed before Definition `def:ray-regular`: a symmetric compact set
`I ⊆ ℝ ∖ {0}` containing the support of `ρ̂`. -/
structure IsFrequencyWindow (ρ : ℝ → ℝ) (I : Set ℝ) : Prop where
  /-- `I` is compact. -/
  isCompact : IsCompact I
  /-- `I` stays away from the origin. -/
  zero_notMem : (0 : ℝ) ∉ I
  /-- `I` is symmetric. -/
  neg_mem : ∀ ω ∈ I, -ω ∈ I
  /-- `I` contains the support of `ρ̂`. -/
  tsupport_subset : tsupport (filterFourier ρ) ⊆ I

/-- The ray-derivative bound `max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖` of a density `G` at the
direction `a`, in `ℝ≥0∞`. -/
def rayDerivBound (I : Set ℝ) (G : H → Y) (m : ℕ) (a : H) : ℝ≥0∞ :=
  ⨆ k : Fin (m + 1), ⨆ ω ∈ I, ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ₑ

/-- The ray moment `M_m(G) = ∫ (1+‖a‖)^{m+2} max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖ ν(da)`
(`eq:ray-regularity`), in `ℝ≥0∞`. -/
def rayMoment (ν : Measure H) (I : Set ℝ) (G : H → Y) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I G m a ∂ν

/-- **Definition [def:ray-regular]** A bounded Borel density `G` is regular along rays (with
respect to the direction measure `ν` and the frequency window `I`) if for every direction `a`
the map `ω ↦ G(ωa)` is `C^∞` on a neighbourhood of `I` and every ray moment `M_m(G)` is
finite. -/
structure IsRegularAlongRays (ν : Measure H) (I : Set ℝ) (G : H → Y) : Prop where
  /-- `G` is Borel. -/
  stronglyMeasurable : StronglyMeasurable G
  /-- `G` is bounded. -/
  bounded : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M
  /-- `ω ↦ G(ωa)` is `C^∞` on an open neighbourhood of `I`, for every direction `a`. -/
  contDiffOn : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U
  /-- `M_m(G) < ∞` for every `m`. -/
  rayMoment_lt_top : ∀ m : ℕ, rayMoment ν I G m < ⊤

end SpectralTarget

/-! ### Tempered activations that are continuous functions of polynomial growth -/

/-- `β ∈ 𝒮'(ℝ)` is the continuous function `b` of polynomial growth: `b` is continuous,
`|b(t)| ≤ C (1+|t|)^p`, and `β` acts on test functions by integration against `b`. -/
structure IsTemperedFunction (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) : Prop where
  /-- `b` is continuous. -/
  continuous : Continuous b
  /-- `b` has polynomial growth. -/
  polynomialGrowth : HasPolynomialGrowth b
  /-- `β` is integration against `b`. -/
  apply_eq : ∀ φ : SchwartzMap ℝ ℂ, β φ = ∫ t, (b t : ℂ) * φ t

/-! ### The extended transform, the anti-dual, the frame operator, and synthesis -/

section AntiDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The continuous linear functional `g ↦ conj (F g)` of a continuous conjugate-linear
functional `F`. -/
def antiDualConj (F : E →L⋆[ℂ] ℂ) : E →L[ℂ] ℂ where
  toFun g := (starRingEnd ℂ) (F g)
  map_add' g h := by simp
  map_smul' c g := by simp
  cont := Complex.continuous_conj.comp F.continuous

@[simp]
theorem antiDualConj_apply (F : E →L⋆[ℂ] ℂ) (g : E) :
    antiDualConj F g = (starRingEnd ℂ) (F g) :=
  rfl

end AntiDual

section Extension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- `𝒦 = spectralRange μ ν` is a closed subspace of the Hilbert space `L²(ν)`, hence complete. -/
instance instCompleteSpaceSpectralRange (μ ν : Measure H) [IsFiniteMeasure μ] :
    CompleteSpace (spectralRange μ ν) :=
  Submodule.topologicalClosure.completeSpace _

open Classical in
/-- The bounded extension `R_ρ : 𝓔 → L²(λ)` of Theorem `thm:B`(ii), represented on `𝒦`: the
continuous linear map that agrees `λ`-almost everywhere with `f ↦ R_ρ f` on `U(𝒟)`, when one
exists, and `0` otherwise. -/
def ridgeletExtension (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) :
    spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν) :=
  if h : ∃ R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f
  then h.choose else 0

/-- The range `Ran R_ρ ⊆ L²(λ)` of the extended transform. -/
def ridgeletRange (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) :
    Submodule ℂ (Lp ℂ 2 (parameterMeasure ν)) :=
  LinearMap.range (ridgeletExtension μ ν ρ).toLinearMap

/-- The continuous anti-dual `𝓔' = 𝒦 →L⋆[ℂ] ℂ` of `𝓔` (represented by `𝒦`): continuous
conjugate-linear functionals. -/
abbrev SpectralAntiDual (μ ν : Measure H) [IsFiniteMeasure μ] : Type _ :=
  spectralRange μ ν →L⋆[ℂ] ℂ

/-- The Riesz map `J : 𝓔 → 𝓔'`, `J f [g] = ⟨f, g⟩_𝓔` (`eq:riesz-map`), linear in `f` and
conjugate linear in `g`. -/
def rieszMap (μ ν : Measure H) [IsFiniteMeasure μ] :
    spectralRange μ ν →L[ℂ] SpectralAntiDual μ ν :=
  innerSLFlip ℂ

/-- The inverse Riesz map `J⁻¹ : 𝓔' → 𝓔`: the vector representing a continuous conjugate-linear
functional (Riesz representation theorem, through `InnerProductSpace.toDual`). -/
def rieszInv (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDual μ ν) :
    spectralRange μ ν :=
  (InnerProductSpace.toDual ℂ (spectralRange μ ν)).symm (antiDualConj F)

/-- The anti-dual transpose `U' : L²(ν) → 𝓔'` of the unitary `U : 𝓔 → 𝒦 ⊆ L²(ν)`,
`U' F [g] = ⟨F, U g⟩_{L²(ν)}` (`eq:transpose-analysis`). -/
def transposeEmbed (μ ν : Measure H) [IsFiniteMeasure μ] (F : Lp ℂ 2 ν) :
    SpectralAntiDual μ ν :=
  (innerSLFlip ℂ F).comp (spectralRange μ ν).subtypeL

/-- The frame operator `T = U' U : 𝓔 → 𝓔'`. -/
def frameOperator (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralRange μ ν) :
    SpectralAntiDual μ ν :=
  transposeEmbed μ ν (f : Lp ℂ 2 ν)

/-- The synthesis operator `S_ρ = R_ρ' : L²(λ) → 𝓔'`, the anti-dual transpose of the extended
transform: `(S_ρ γ)[g] = ⟨γ, R_ρ g⟩_{L²(λ)}` (`eq:weak-synthesis`). -/
def synthesis (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)
    (γ : Lp ℂ 2 (parameterMeasure ν)) : SpectralAntiDual μ ν :=
  (innerSLFlip ℂ γ).comp (ridgeletExtension μ ν ρ)

end Extension

/-! ### Backprojection and the coefficient projection -/

section Backprojection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The backprojection (ray average, `eq:ray-average`) of a partial bias-Fourier representative
`Φ` of a coefficient: `Λ_ρ Φ (ξ) = (2π)⁻¹ ∫ conj(ρ̂(ω)) |ω|^{-α} Φ(-ξ/ω, ω) dω`. -/
def backprojectionOf (α : ℝ) (ρ : ℝ → ℝ) (Φ : H → ℝ → ℂ) (ξ : H) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) * Φ (-(ω⁻¹ • ξ)) ω

open Classical in
/-- The backprojection `Λ_ρ γ` of a coefficient `γ`, computed from a jointly measurable partial
bias-Fourier representative of `γ` (`HasBiasFourier`), and `0` if there is none.

`HasBiasFourier` requires the representative to be square integrable along `ν`-almost every
ray, which pins it down up to a null set on almost every ray (`HasBiasFourier.ae_ae_eq`), and
the ray substitution `(a, ω) ↦ (-ωa, ω)` preserves null sets by homogeneity; hence the ray
average does not depend on the chosen representative as an element of `L²(ν)`
(`prop_coefficient_projection_ii`).  For `γ ∈ L²(λ)` a jointly measurable representative exists
(`exists_measurable_hasBiasFourier`), so the junk value is never taken on `L²(λ)`. -/
def backprojection (α : ℝ) (ν : Measure H) (ρ : ℝ → ℝ) (γ : H × ℝ → ℂ) : H → ℂ :=
  if h : ∃ Φ : H → ℝ → ℂ, Measurable (Function.uncurry Φ) ∧ HasBiasFourier ν γ Φ then
    backprojectionOf α ρ h.choose
  else 0

open Classical in
/-- The backprojection `Λ_ρ γ` as an element of `L²(ν)` (`0` if it is not square
integrable). -/
def backprojectionLp (α : ℝ) (ν : Measure H) (ρ : ℝ → ℝ) (γ : H × ℝ → ℂ) : Lp ℂ 2 ν :=
  if h : MemLp (backprojection α ν ρ γ) 2 ν then h.toLp _ else 0

variable [OpensMeasurableSpace H]

/-- The coefficient projection `Π_ρ = C⁻¹ W_ρ P_𝒦 Λ_ρ` (`eq:coefficient-projection`), with
`P_𝒦` the orthogonal projection of `L²(ν)` onto `𝒦`. -/
def coefficientProjection (α : ℝ) (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)
    (γ : H × ℝ → ℂ) : Lp ℂ 2 (parameterMeasure ν) :=
  (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
    spectralCoefficient ν ρ
      (((spectralRange μ ν).starProjection (backprojectionLp α ν ρ γ) : Lp ℂ 2 ν) : H → ℂ)

end Backprojection

/-! ### The Hermite inverse of the weighted Fourier transform -/

section Hermite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The analytic continuation `z ↦ 𝒢_μ f(zξ) = ∫ f(x) e^{-iz⟪x,ξ⟫} μ(dx)` of the weighted Fourier
transform along the ray through `ξ` to complex `z`. -/
def gaussFourierLine (μ : Measure H) (f : H → ℂ) (ξ : H) (z : ℂ) : ℂ :=
  ∫ x, f x * Complex.exp (-(z * (⟪x, ξ⟫ : ℝ) * Complex.I)) ∂μ

/-- The entire function `G_f(zξ) = e^{z²τ(ξ)²/2} 𝒢_μ f(zξ)` of Lemma `lem:hermite-totality`,
with `τ(ξ)² = ⟪Qξ,ξ⟫`. -/
def hermiteExtension (μ : Measure H) (Q : H →L[ℝ] H) (f : H → ℂ) (ξ : H) (z : ℂ) : ℂ :=
  Complex.exp (z ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) / 2) * gaussFourierLine μ f ξ z

/-- The Hermite coefficient `E_μ[f(x) He_n(⟪x,ξ⟫/τ(ξ))]`, `τ(ξ) = ⟪Qξ,ξ⟫^{1/2}`, with the
probabilists' Hermite polynomials `Polynomial.hermite`. -/
def hermiteCoefficient (μ : Measure H) (Q : H →L[ℝ] H) (f : H → ℂ) (ξ : H) (n : ℕ) : ℂ :=
  ∫ x, f x * ((Polynomial.aeval (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) (Polynomial.hermite n) : ℝ) : ℂ)
    ∂μ

variable [OpensMeasurableSpace H]

open Classical in
/-- The inverse `Δ_Q` of `𝒢_μ` on its range on `𝒟`: the element `f ∈ 𝒟` with `𝒢_μ f = G` when
one exists (it is unique by Theorem `thm:C`(iv)), and `0` otherwise. -/
def gaussFourierInv (μ ν : Measure H) [IsFiniteMeasure μ] (G : H → ℂ) : Lp ℂ 2 μ :=
  if h : ∃ f : Lp ℂ 2 μ, f ∈ spectralCore μ ν ∧ gaussFourier μ f = G then h.choose else 0

end Hermite

/-! ### Vector-valued targets -/

section VectorValued

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The `Y`-valued weighted Fourier transform `𝒢_μ f(ξ) = ∫ e^{-i⟪x,ξ⟫} f(x) μ(dx)`, a Bochner
integral. -/
def gaussFourierVec (μ : Measure H) (f : H → Y) (ξ : H) : Y :=
  ∫ x, character ξ x • f x ∂μ

/-- The `Y`-valued ridgelet transform `R_ρ f(a,c) = ∫ ρ(⟪a,x⟫+c) f(x) μ(dx)`. -/
def ridgeletVec (μ : Measure H) (ρ : ℝ → ℝ) (f : H → Y) (p : H × ℝ) : Y :=
  ∫ x, (ρ (⟪p.1, x⟫ + p.2) : ℂ) • f x ∂μ

/-- The explicit `Y`-valued coefficient `γ_G(a,c) = (2π)⁻¹ ∫ ρ̂(ω) e^{iωc} G(-ωa) dω`. -/
def coefficientFormulaVec (ρ : ℝ → ℝ) (G : H → Y) (p : H × ℝ) : Y :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ ω : ℝ, (filterFourier ρ ω * Complex.exp ((ω * p.2 : ℝ) * Complex.I)) • G (-(ω • p.1))

/-- The partial Fourier transform in the bias of a `Y`-valued coefficient,
`γ̂(a,ω) = ∫ e^{-iωc} γ(a,c) dc`. -/
def biasFourierVec (γ : H × ℝ → Y) (a : H) (ω : ℝ) : Y :=
  ∫ c : ℝ, Complex.exp (-((ω * c : ℝ) * Complex.I)) • γ (a, c)

/-- `HasBiasFourierVec ν γ Φ`: the partial Fourier transform in the bias of the `Y`-valued
coefficient `γ` is `Φ`: for `ν`-almost every direction the ray function `Φ(a,·)` is square
integrable and Parseval's identity against Schwartz test functions holds (the `Y`-valued form
of `HasBiasFourier`, whose docstring explains the square-integrability clause). -/
structure HasBiasFourierVec (ν : Measure H) (γ : H × ℝ → Y) (Φ : H → ℝ → Y) : Prop where
  /-- `Φ(a,·) ∈ L²(ℝ; Y)` for `ν`-almost every direction `a`. -/
  memLp : ∀ᵐ a ∂ν, MemLp (Φ a) 2 volume
  /-- Parseval's identity against Schwartz test functions, for `ν`-almost every direction. -/
  parseval : ∀ᵐ a ∂ν, ∀ φ : SchwartzMap ℝ ℂ,
    ∫ c : ℝ, (starRingEnd ℂ) (φ c) • γ (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω : ℝ, (starRingEnd ℂ) (lineFourier φ ω) • Φ a ω

open Classical in
/-- The `Y`-valued coefficient operator `W_ρ G ∈ L²(λ; Y)`: the element whose partial Fourier
transform in the bias is `(a,ω) ↦ ρ̂(ω) G(-ωa)`, and `0` if there is none. -/
def spectralCoefficientVec (ν : Measure H) (ρ : ℝ → ℝ) (G : H → Y) :
    Lp Y 2 (parameterMeasure ν) :=
  if h : ∃ γ : Lp Y 2 (parameterMeasure ν),
      HasBiasFourierVec ν γ (fun a ω => filterFourier ρ ω • G (-(ω • a))) then
    h.choose
  else 0

/-- The analytic continuation `z ↦ 𝒢_μ f(zξ)` of the `Y`-valued weighted Fourier transform along
the ray through `ξ`. -/
def gaussFourierLineVec (μ : Measure H) (f : H → Y) (ξ : H) (z : ℂ) : Y :=
  ∫ x, Complex.exp (-(z * (⟪x, ξ⟫ : ℝ) * Complex.I)) • f x ∂μ

/-- The `Y`-valued entire function `G_f(zξ) = e^{z²τ(ξ)²/2} 𝒢_μ f(zξ)`. -/
def hermiteExtensionVec (μ : Measure H) (Q : H →L[ℝ] H) (f : H → Y) (ξ : H) (z : ℂ) : Y :=
  Complex.exp (z ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) / 2) • gaussFourierLineVec μ f ξ z

/-- The `Y`-valued Hermite coefficient `E_μ[He_n(⟪x,ξ⟫/τ(ξ)) f(x)]`. -/
def hermiteCoefficientVec (μ : Measure H) (Q : H →L[ℝ] H) (f : H → Y) (ξ : H) (n : ℕ) : Y :=
  ∫ x, ((Polynomial.aeval (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) (Polynomial.hermite n) : ℝ) : ℂ) • f x
    ∂μ

/-- The `Y`-valued backprojection of a partial bias-Fourier representative `Φ`:
`Λ_ρ Φ (ξ) = (2π)⁻¹ ∫ conj(ρ̂(ω)) |ω|^{-α} Φ(-ξ/ω, ω) dω`. -/
def backprojectionOfVec (α : ℝ) (ρ : ℝ → ℝ) (Φ : H → ℝ → Y) (ξ : H) : Y :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ ω : ℝ, ((starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) • Φ (-(ω⁻¹ • ξ)) ω

open Classical in
/-- The `Y`-valued backprojection `Λ_ρ γ`, computed from a jointly strongly measurable partial
bias-Fourier representative of `γ`, and `0` if there is none. -/
def backprojectionVec (α : ℝ) (ν : Measure H) (ρ : ℝ → ℝ) (γ : H × ℝ → Y) : H → Y :=
  if h : ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧ HasBiasFourierVec ν γ Φ then
    backprojectionOfVec α ρ h.choose
  else 0

open Classical in
/-- The `Y`-valued backprojection `Λ_ρ γ` as an element of `L²(ν; Y)`. -/
def backprojectionLpVec (α : ℝ) (ν : Measure H) (ρ : ℝ → ℝ) (γ : H × ℝ → Y) : Lp Y 2 ν :=
  if h : MemLp (backprojectionVec α ν ρ γ) 2 ν then h.toLp _ else 0

theorem gaussFourierVec_smul (μ : Measure H) (c : ℂ) (f : Lp Y 2 μ) :
    gaussFourierVec μ ((c • f : Lp Y 2 μ) : H → Y) = c • gaussFourierVec μ f := by
  funext ξ
  simp only [gaussFourierVec, Pi.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx, Pi.smul_apply, smul_comm]

theorem gaussFourierVec_zero' (μ : Measure H) :
    gaussFourierVec μ ((0 : Lp Y 2 μ) : H → Y) = 0 := by
  funext ξ
  simp only [gaussFourierVec, Pi.zero_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero Y 2 μ] with x hx
  rw [hx]
  simp

variable [OpensMeasurableSpace H]

theorem integrable_character_smul (μ : Measure H) [IsFiniteMeasure μ] (f : Lp Y 2 μ) (ξ : H) :
    Integrable (fun x => character ξ x • (f : H → Y) x) μ := by
  have hf : Integrable (f : H → Y) μ := (Lp.memLp f).integrable one_le_two
  have hc : MemLp (character ξ) ⊤ μ :=
    memLp_top_of_bound (continuous_character ξ).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => (norm_character ξ x).le)
  exact hf.smul_of_top_right hc

theorem gaussFourierVec_add (μ : Measure H) [IsFiniteMeasure μ] (f g : Lp Y 2 μ) :
    gaussFourierVec μ ((f + g : Lp Y 2 μ) : H → Y) =
      gaussFourierVec μ f + gaussFourierVec μ g := by
  funext ξ
  simp only [gaussFourierVec, Pi.add_apply]
  rw [← integral_add (integrable_character_smul μ f ξ) (integrable_character_smul μ g ξ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx, Pi.add_apply, smul_add]

variable (Y) in
/-- The `Y`-valued core `𝒟(Y) = {f ∈ L²(μ; Y) : 𝒢_μ f ∈ L²(ν; Y)}`. -/
def spectralCoreVec (μ ν : Measure H) [IsFiniteMeasure μ] : Submodule ℂ (Lp Y 2 μ) where
  carrier := {f | MemLp (gaussFourierVec μ f) 2 ν}
  add_mem' {f g} hf hg := by
    change MemLp (gaussFourierVec μ ((f + g : Lp Y 2 μ) : H → Y)) 2 ν
    rw [gaussFourierVec_add]
    exact MemLp.add hf hg
  zero_mem' := by
    change MemLp (gaussFourierVec μ ((0 : Lp Y 2 μ) : H → Y)) 2 ν
    rw [gaussFourierVec_zero']
    exact MemLp.zero
  smul_mem' c {f} hf := by
    change MemLp (gaussFourierVec μ ((c • f : Lp Y 2 μ) : H → Y)) 2 ν
    rw [gaussFourierVec_smul]
    exact MemLp.const_smul hf c

theorem mem_spectralCoreVec_iff (μ ν : Measure H) [IsFiniteMeasure μ] (f : Lp Y 2 μ) :
    f ∈ spectralCoreVec Y μ ν ↔ MemLp (gaussFourierVec μ f) 2 ν :=
  Iff.rfl

/-- `𝒢_μ f` as an element of `L²(ν; Y)`, for `f ∈ 𝒟(Y)`. -/
def gaussFourierLpVec (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralCoreVec Y μ ν) :
    Lp Y 2 ν :=
  MemLp.toLp (gaussFourierVec μ f) f.2

variable (Y) in
/-- The closed subspace `𝒦(Y) = closure (𝒢_μ 𝒟(Y)) ⊆ L²(ν; Y)`, which represents `𝓔_α(Y)`. -/
def spectralRangeVec (μ ν : Measure H) [IsFiniteMeasure μ] : Submodule ℂ (Lp Y 2 ν) :=
  (Submodule.span ℂ (Set.range (gaussFourierLpVec μ ν))).topologicalClosure

/-- The map `U : 𝒟(Y) → 𝒦(Y)`, `f ↦ 𝒢_μ f`. -/
def spectralEmbedVec (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralCoreVec Y μ ν) :
    spectralRangeVec Y μ ν :=
  ⟨gaussFourierLpVec μ ν f,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)⟩

variable (Y) in
open Classical in
/-- The bounded extension `R_ρ : 𝓔(Y) → L²(λ; Y)`, represented on `𝒦(Y)`: the continuous linear
map agreeing almost everywhere with `f ↦ R_ρ f` on `U(𝒟(Y))`, when one exists, and `0`
otherwise. -/
def ridgeletExtensionVec (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) :
    spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν) :=
  if h : ∃ R : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      ∀ f : spectralCoreVec Y μ ν,
        (R (spectralEmbedVec μ ν f) : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f
  then h.choose else 0

variable (Y) in
/-- The range `Ran R_ρ ⊆ L²(λ; Y)` of the extended `Y`-valued transform. -/
def ridgeletRangeVec (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ) :
    Submodule ℂ (Lp Y 2 (parameterMeasure ν)) :=
  LinearMap.range (ridgeletExtensionVec Y μ ν ρ).toLinearMap

open Classical in
/-- The inverse `Δ_Q` of the `Y`-valued `𝒢_μ` on its range on `𝒟(Y)`. -/
def gaussFourierInvVec (μ ν : Measure H) [IsFiniteMeasure μ] (G : H → Y) : Lp Y 2 μ :=
  if h : ∃ f : Lp Y 2 μ, f ∈ spectralCoreVec Y μ ν ∧ gaussFourierVec μ f = G then h.choose
  else 0

end VectorValued

section VectorValuedHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The `Y`-valued spectral inner product `⟨f,g⟩_{𝓔(Y)} = ∫ ⟨𝒢_μ f, 𝒢_μ g⟩_Y dν`, linear in the
first argument as in the manuscript (Mathlib's `inner` is conjugate linear in the first). -/
def spectralInnerVec (μ ν : Measure H) (f g : H → Y) : ℂ :=
  ∫ ξ, inner ℂ (gaussFourierVec μ g ξ) (gaussFourierVec μ f ξ) ∂ν

variable [OpensMeasurableSpace H]

/-- `𝒦(Y)` is a closed subspace of the Hilbert space `L²(ν; Y)`, hence complete. -/
instance instCompleteSpaceSpectralRangeVec (μ ν : Measure H) [IsFiniteMeasure μ] :
    CompleteSpace (spectralRangeVec Y μ ν) :=
  Submodule.topologicalClosure.completeSpace _

variable (Y) in
/-- The continuous anti-dual `𝓔(Y)' = 𝒦(Y) →L⋆[ℂ] ℂ`. -/
abbrev SpectralAntiDualVec (μ ν : Measure H) [IsFiniteMeasure μ] : Type _ :=
  spectralRangeVec Y μ ν →L⋆[ℂ] ℂ

variable (Y) in
/-- The `Y`-valued Riesz map `J : 𝓔(Y) → 𝓔(Y)'`, `J f [g] = ⟨f, g⟩_{𝓔(Y)}`. -/
def rieszMapVec (μ ν : Measure H) [IsFiniteMeasure μ] :
    spectralRangeVec Y μ ν →L[ℂ] SpectralAntiDualVec Y μ ν :=
  innerSLFlip ℂ

/-- The `Y`-valued inverse Riesz map `J⁻¹ : 𝓔(Y)' → 𝓔(Y)`. -/
def rieszInvVec (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDualVec Y μ ν) :
    spectralRangeVec Y μ ν :=
  (InnerProductSpace.toDual ℂ (spectralRangeVec Y μ ν)).symm (antiDualConj F)

/-- The `Y`-valued transpose `U' : L²(ν; Y) → 𝓔(Y)'`, `U' F [g] = ⟨F, U g⟩_{L²(ν;Y)}`. -/
def transposeEmbedVec (μ ν : Measure H) [IsFiniteMeasure μ] (F : Lp Y 2 ν) :
    SpectralAntiDualVec Y μ ν :=
  (innerSLFlip ℂ F).comp (spectralRangeVec Y μ ν).subtypeL

/-- The `Y`-valued frame operator `T = U' U : 𝓔(Y) → 𝓔(Y)'`. -/
def frameOperatorVec (μ ν : Measure H) [IsFiniteMeasure μ] (f : spectralRangeVec Y μ ν) :
    SpectralAntiDualVec Y μ ν :=
  transposeEmbedVec μ ν (f : Lp Y 2 ν)

/-- The `Y`-valued synthesis operator `S_ρ = R_ρ' : L²(λ; Y) → 𝓔(Y)'`,
`(S_ρ γ)[g] = ⟨γ, R_ρ g⟩_{L²(λ;Y)}`. -/
def synthesisVec (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)
    (γ : Lp Y 2 (parameterMeasure ν)) : SpectralAntiDualVec Y μ ν :=
  (innerSLFlip ℂ γ).comp (ridgeletExtensionVec Y μ ν ρ)

/-- The `Y`-valued coefficient projection `Π_ρ = C⁻¹ W_ρ P_{𝒦(Y)} Λ_ρ`. -/
def coefficientProjectionVec (α : ℝ) (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)
    (γ : H × ℝ → Y) : Lp Y 2 (parameterMeasure ν) :=
  (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
    spectralCoefficientVec ν ρ
      (((spectralRangeVec Y μ ν).starProjection (backprojectionLpVec α ν ρ γ) : Lp Y 2 ν) :
        H → Y)

end VectorValuedHilbert

end OperatorRidgelet
