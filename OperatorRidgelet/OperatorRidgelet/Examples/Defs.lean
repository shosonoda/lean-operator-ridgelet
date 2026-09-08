import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Definitions for Section 7 (genuinely infinite-dimensional examples) and Appendix E

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.  They build on the Section 2–4 objects (`gaussFourier`, `ridgelet`, `spectralCore`,
`spectralTarget`, `IsRegularAlongRays`, `integralNetwork`, ...) and record the following design
choices.

## Cylindrical functions

The manuscript calls `f` cylindrical if `f = f̃ ∘ L` for a finite-rank linear map `L`.
`IsCylindrical f` takes `L : H →ₗ[ℝ] (Fin m → ℝ)` linear but not necessarily continuous; the
non-cylindricity claims of Section 7 are therefore slightly stronger than the manuscript's
(their proofs only use that `ker L` has finite codimension).  `HasInfiniteRank L` says that the
range of a linear map is not finite dimensional.

## Trace, square roots, resolvents, and the Fredholm determinant

Mathlib v4.32.0 has neither trace-class operators nor Fredholm determinants.

* `traceOf P = ∑ ⟪P e_i, e_i⟫` along a Hilbert basis for which the sum converges
  (`HasSummableTrace`; `0` if there is none).  For a positive operator the value is basis
  independent; this is a later proof obligation, not part of the definition.
* `IsPositiveTraceClass P` is the covariance hypothesis without injectivity (positive,
  self-adjoint, summable trace), used by Lemma `lem:gaussian-quadratic`.
* Square roots such as `Q^{1/2}` are data `S` with `IsPositiveSqrt S Q` (`S` positive
  self-adjoint and `S * S = Q`).
* `(I + M)⁻¹` is `Ring.inverse (1 + M)` in the ring `H →L[ℝ] H` (`0` if `1 + M` is not a unit;
  for positive `M` it always is), and `resolventForm S M x = ⟪S (I+M)⁻¹ S x, x⟫`.
* `det(I + M)` is `fredholmDet M = ∏' i, (1 + ⟪M e_i, e_i⟫)` computed along an orthonormal
  eigenbasis of `M` (`HasEigenbasis M e w`, chosen through `Classical.choose`; `1` if `M` has no
  orthonormal eigenbasis).  Along an eigenbasis this is literally the product of `1 + m_i` over
  the eigenvalues; that the value does not depend on the eigenbasis is again a proof
  obligation, not hidden in the definition (`fredholmDetAlong` is the product along a given
  basis).

## Gaussian functions

`gaussianAct u = e^{-u²/2}` is the Gaussian activation `Φ = φ` of Section 7 (this is the
function the manuscript denotes `Φ` there; it is not the distribution function),
`gaussianActDeriv2 b = (b² - 1) e^{-b²/2}` is `φ''`, `gaussianSmooth ρ v c = (ρ * φ_v)(c)` is
the convolution with the centred Gaussian of variance `v` (Mathlib's `gaussianReal 0 v`, which
is `δ_0` for `v = 0`), `gaussianTarget W x = e^{-⟨Wx,x⟩/2}` is `f_W`, and
`gaussianKappa S W ξ = ⟨S (I+M)⁻¹ S ξ, ξ⟩` is `κ_W` for `S = Q^{1/2}` and `M = S W S`.
`MemSpectralCore μ ν f` is `f ∈ 𝒟_α` for a function `f` (`f ∈ L²(μ)` and `𝒢_μ f ∈ L²(ν)`);
`toLp_mem_spectralCore_iff` relates it to the submodule `spectralCore`.

## Gaussian-parameter networks and the neural-operator layer

`gaussianParameterReLU μ = F_Q` and `gaussianParameterGauss μ = Φ_Q` are the integral networks
with parameter law `μ = 𝒩(0,Q)`.  The neural-operator layer of `eq:operator-layer` is
`operatorLayer m a b β x = ∫ β(⟨a_y,x⟩) b_y m(dy)`, with observable `layerObservable`
(`F_φ = ⟨ℱ(·), φ⟩_Y`, linear in the first argument as in the manuscript, so it is Mathlib's
`inner ℂ φ (ℱ x)`), weight `layerWeight b φ y = ⟨b_y, φ⟩_Y`, the operator `A`
(`layerA m a : H →ₗ[ℝ] (Ω →ₘ[m] ℝ)`, `(Ax)(y) = ⟨a_y, x⟩` as an a.e.-class; its rank and kernel
are those of the bounded operator into `L²(m)`), `‖A‖_∞ = layerSupNorm a`, the coefficient
measure `layerMeasure m a b = ι_#(b_y m(dy))`, the covariances `layerCovariance Q a y = S_y`,
and the hinge coefficient measure `layerHingeMeasure` of the ReLU form.  The standing
hypotheses on `(a, b)` are `IsLayerData m a b`.

## Local sampling definitions (to be reconciled with `OperatorRidgelet.Sampling.Defs`)

The sampling claims inside the examples are stated with the local definitions of
`OperatorRidgelet.Examples`: `supNormOn K f = ‖f‖_{C(K)}`, `compactRadius K = R_K`,
`gaussianReLUSample a x = F_{Q,N}(x)`, `normalizedLaw m w = ‖w‖ m / ∫‖w‖ dm`,
`polarSample β λ γ θ x = f_N(x)` (the polar sampled network `eq:polar-network` of `γ λ`),
`secondMoment p = M₂²`, and the pushforward samples `layerSampleScalar`, `layerSampleVec` of a
layer.  Expectations are integrals over `Measure.pi (fun _ : Fin N => law)`.

## The periodic convolution layer and the Dirichlet solution operator

`Torus d = (ℝ/2πℤ)^d` with the normalized Haar measure `torusHaar d`, `TorusL2 d = L²(𝕋^d;ℝ)`,
`TorusL2C d = L²(𝕋^d)`, translations `torusTranslate d z` (`(τ_z x)(t) = x(t - z)`),
`convDirection k y = k(y - ·)`, `convOutput ψ y = ψ(· - y)`, Fourier coefficients
`torusFourierCoeff` with the characters `torusCharacter n`, and the Bessel operator
`besselOperator d s = (I - Δ)^{-s}`, defined as the bounded operator multiplying the `n`-th
Fourier coefficient by `(1 + |n|²)^{-s}` (chosen through `Classical.choose`; `0` if there is
none).  `dirichletOperator = 𝖦` is the integral operator on `L²(0,1)` with kernel
`dirichletKernel`, again chosen through its defining property (`integralOperator`), with the
eigenpairs `dirichletEigenvalue`, `dirichletEigenfunction` and the `2N`-neuron truncation
`dirichletReLUTruncation` built from `spectralReLUNetwork`; the parameter space `Ω = (0,1)` is
the subtype `UnitOpenInterval` with its Lebesgue measure `volume`, so that `‖A‖_∞` is the
supremum over `y ∈ (0,1)` only.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet
open scoped ENNReal RealInnerProductSpace

/-! ### Cylindrical functions and infinite rank -/

section Cylindrical

variable {H Y : Type*} [AddCommGroup H] [Module ℝ H]

/-- A function `f` on `H` is cylindrical if `f = f̃ ∘ L` for a finite-rank linear map `L`, here
a linear map `L : H → ℝ^m` (not assumed continuous). -/
def IsCylindrical (f : H → Y) : Prop :=
  ∃ (m : ℕ) (L : H →ₗ[ℝ] (Fin m → ℝ)), FactorsThrough f L

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- A linear map has infinite rank when its range is not finite dimensional. -/
def HasInfiniteRank (L : H →ₗ[ℝ] F) : Prop :=
  ¬ FiniteDimensional ℝ (LinearMap.range L)

end Cylindrical

/-! ### Trace, positivity, square roots, resolvents, and the Fredholm determinant -/

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The trace `∑ ⟪P e_i, e_i⟫` of `P` along the Hilbert basis `b`. -/
def traceAlong {ι : Type*} (b : HilbertBasis ι ℝ H) (P : H →L[ℝ] H) : ℝ :=
  ∑' i, ⟪P (b i), b i⟫

/-- `P` has a summable trace along some Hilbert basis. -/
def HasSummableTrace (P : H →L[ℝ] H) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι ℝ H), Summable fun i => ⟪P (b i), b i⟫

open Classical in
/-- The trace `tr P = ∑ ⟪P e_i, e_i⟫`, along a Hilbert basis for which the sum converges (`0`
if there is none); for a positive operator the value does not depend on the basis. -/
def traceOf (P : H →L[ℝ] H) : ℝ :=
  if h : HasSummableTrace P then traceAlong h.choose_spec.choose P else 0

/-- A positive, self-adjoint, trace-class operator (the covariance hypothesis
`IsTraceClassCovariance` without injectivity). -/
structure IsPositiveTraceClass (P : H →L[ℝ] H) : Prop where
  /-- `P` is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint P
  /-- `P` is positive. -/
  inner_nonneg : ∀ x, 0 ≤ ⟪P x, x⟫
  /-- `P` is trace class. -/
  hasSummableTrace : HasSummableTrace P

theorem IsTraceClassCovariance.isPositiveTraceClass {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) : IsPositiveTraceClass P :=
  ⟨hP.isSelfAdjoint, hP.inner_nonneg, hP.summable_trace⟩

/-- `S` is the positive square root of `Q`: `S` is positive self-adjoint and `S² = Q`. -/
structure IsPositiveSqrt (S Q : H →L[ℝ] H) : Prop where
  /-- `S` is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint S
  /-- `S` is positive. -/
  inner_nonneg : ∀ x, 0 ≤ ⟪S x, x⟫
  /-- `S * S = Q`. -/
  mul_self : S * S = Q

/-- `e` is an orthonormal eigenbasis of `M` with eigenvalues `w`: `M e_i = w_i e_i`. -/
def HasEigenbasis {ι : Type*} (M : H →L[ℝ] H) (e : HilbertBasis ι ℝ H) (w : ι → ℝ) : Prop :=
  ∀ i, M (e i) = w i • e i

/-- The product `∏ (1 + ⟪M e_i, e_i⟫)` along the Hilbert basis `e`. -/
def fredholmDetAlong {ι : Type*} (e : HilbertBasis ι ℝ H) (M : H →L[ℝ] H) : ℝ :=
  ∏' i, (1 + ⟪M (e i), e i⟫)

open Classical in
/-- The Fredholm determinant `det(I + M)` of a (positive trace-class) operator `M`: the product
`∏ (1 + m_i)` over the eigenvalues, computed along an orthonormal eigenbasis of `M` (`1` if `M`
has none). -/
def fredholmDet (M : H →L[ℝ] H) : ℝ :=
  if h : ∃ (ι : Type) (e : HilbertBasis ι ℝ H) (w : ι → ℝ), HasEigenbasis M e w then
    fredholmDetAlong h.choose_spec.choose M
  else 1

/-- The quadratic form `⟪S (I + M)⁻¹ S x, x⟫`, with `(I + M)⁻¹ = Ring.inverse (1 + M)`. -/
def resolventForm (S M : H →L[ℝ] H) (x : H) : ℝ :=
  ⟪(S * Ring.inverse (1 + M) * S) x, x⟫

end Operators

/-! ### Gaussian functions -/

section GaussianFunctions

/-- The Gaussian activation `Φ(u) = φ(u) = e^{-u²/2}`. -/
def gaussianAct (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / 2)

/-- The second derivative `φ''(b) = (b² - 1) e^{-b²/2}` of the Gaussian activation. -/
def gaussianActDeriv2 (b : ℝ) : ℝ :=
  (b ^ 2 - 1) * Real.exp (-b ^ 2 / 2)

/-- The convolution `(ρ * φ_v)(c) = ∫ ρ(c - t) 𝒩(0,v)(dt)` of a filter with the centred
one-dimensional Gaussian of variance `v ≥ 0` (`φ_0 = δ_0`). -/
def gaussianSmooth (ρ : ℝ → ℝ) (v : ℝ) (c : ℝ) : ℝ :=
  ∫ t, ρ (c - t) ∂(ProbabilityTheory.gaussianReal 0 (Real.toNNReal v))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Gaussian target `f_W(x) = e^{-⟨Wx,x⟩/2}` (`eq:gaussian-target`). -/
def gaussianTarget (W : H →L[ℝ] H) (x : H) : ℂ :=
  ((Real.exp (-⟪W x, x⟫ / 2) : ℝ) : ℂ)

/-- `κ_W(ξ) = ⟨Q^{1/2} (I + M)⁻¹ Q^{1/2} ξ, ξ⟩` with `M = Q^{1/2} W Q^{1/2}`, for `S = Q^{1/2}`
(`eq:gaussian-target`). -/
def gaussianKappa (S W : H →L[ℝ] H) (ξ : H) : ℝ :=
  resolventForm S (S * W * S) ξ

/-- `S_W = Q^{1/2} (I + M)⁻¹ Q^{1/2}`, `M = Q^{1/2} W Q^{1/2}`, for `S = Q^{1/2}`
(`eq:filtered-gaussian-target`). -/
def gaussianTargetResolvent (S W : H →L[ℝ] H) : H →L[ℝ] H :=
  S * Ring.inverse (1 + S * W * S) * S

/-- `Σ_s = 2s P^{1/2} (I + 2s P^{1/2} T P^{1/2})⁻¹ P^{1/2}` for `R = P^{1/2}` and `T = S_W`
(`eq:filtered-gaussian-target`). -/
def mixtureLayerCovariance (R T : H →L[ℝ] H) (s : ℝ) : H →L[ℝ] H :=
  (2 * s) • (R * Ring.inverse (1 + (2 * s) • (R * T * R)) * R)

variable [MeasurableSpace H]

omit [CompleteSpace H] in
theorem gaussFourier_congr_ae {μ : Measure H} {f g : H → ℂ} (h : f =ᵐ[μ] g) :
    gaussFourier μ f = gaussFourier μ g := by
  funext ξ
  simp only [gaussFourier]
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

variable [OpensMeasurableSpace H]

/-- `f ∈ 𝒟_α` for a function `f`: `f ∈ L²(μ)` and `𝒢_μ f ∈ L²(ν)`. -/
def MemSpectralCore (μ ν : Measure H) (f : H → ℂ) : Prop :=
  MemLp f 2 μ ∧ MemLp (gaussFourier μ f) 2 ν

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- `f ∈ 𝒟_α(Y)` for a `Y`-valued function `f`: `f ∈ L²(μ;Y)` and `𝒢_μ f ∈ L²(ν;Y)`. -/
def MemSpectralCoreVec (μ ν : Measure H) (f : H → Y) : Prop :=
  MemLp f 2 μ ∧ MemLp (gaussFourierVec μ f) 2 ν

omit [CompleteSpace H] in
theorem toLp_mem_spectralCore_iff {μ ν : Measure H} [IsFiniteMeasure μ] {f : H → ℂ}
    (hf : MemLp f 2 μ) :
    hf.toLp f ∈ spectralCore μ ν ↔ MemLp (gaussFourier μ f) 2 ν := by
  rw [mem_spectralCore_iff, gaussFourier_congr_ae hf.coeFn_toLp]

omit [CompleteSpace H] in
theorem memSpectralCore_iff {μ ν : Measure H} [IsFiniteMeasure μ] {f : H → ℂ} :
    MemSpectralCore μ ν f ↔ ∃ hf : MemLp f 2 μ, hf.toLp f ∈ spectralCore μ ν := by
  constructor
  · rintro ⟨hf, hG⟩
    exact ⟨hf, (toLp_mem_spectralCore_iff hf).2 hG⟩
  · rintro ⟨hf, hG⟩
    exact ⟨hf, (toLp_mem_spectralCore_iff hf).1 hG⟩

end GaussianFunctions

open Classical in
/-- The element of `L^p(μ)` represented by `f`, and `0` when `f ∉ L^p(μ)`. -/
def toLpOrZero {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α) (f : α → E) : Lp E p μ :=
  if h : MemLp f p μ then h.toLp f else 0

/-! ### Gaussian-parameter networks -/

section GaussianParameter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The ReLU network with Gaussian parameters, `F_Q(x) = ∫ ReLU(⟨a,x⟩) 𝒩(0,Q)(da)`, for the
parameter law `μ = 𝒩(0,Q)` (`eq:gaussian-parameter-networks`). -/
def gaussianParameterReLU (μ : Measure H) (x : H) : ℝ :=
  ∫ a, relu ⟪a, x⟫ ∂μ

/-- The Gaussian-activation network with Gaussian parameters,
`Φ_Q(x) = ∫ Φ(⟨a,x⟩) 𝒩(0,Q)(da)` (`eq:gaussian-parameter-networks`). -/
def gaussianParameterGauss (μ : Measure H) (x : H) : ℝ :=
  ∫ a, gaussianAct ⟪a, x⟫ ∂μ

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The ReLU coefficient measure of a Gaussian-activation network with coefficient density `γ`
with respect to `λ`: the pushforward of `φ''(b) γ(a,c) λ(da,dc) db` under
`(a,c,b) ↦ (a, c - b)`. -/
def hingeCoefficientMeasure (lam : Measure (H × ℝ)) (γ : H × ℝ → Y) : VectorMeasure (H × ℝ) Y :=
  ((lam.prod volume).withDensityᵥ fun p : (H × ℝ) × ℝ => gaussianActDeriv2 p.2 • γ p.1).map
    fun p => (p.1.1, p.1.2 - p.2)

end GaussianParameter

/-! ### Local sampling definitions -/

namespace Examples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The norm `‖f‖_{C(K)} = sup_{x ∈ K} ‖f x‖` (junk if `f` is unbounded on `K`). -/
def supNormOn {Y : Type*} [Norm Y] (K : Set H) (f : H → Y) : ℝ :=
  ⨆ x ∈ K, ‖f x‖

/-- `R_K = sup_{x ∈ K} √(‖x‖² + 1)`. -/
def compactRadius (K : Set H) : ℝ :=
  ⨆ x ∈ K, Real.sqrt (‖x‖ ^ 2 + 1)

/-- The discretized Gaussian-parameter ReLU network `F_{Q,N}(x) = N⁻¹ ∑_j ReLU(⟨a_j,x⟩)`. -/
def gaussianReLUSample {N : ℕ} (a : Fin N → H) (x : H) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, relu ⟪a j, x⟫

/-- The second parameter moment `M₂² = ∫ (‖a‖² + |c|²) p(da,dc)` of a law `p` on `H × ℝ`
(`eq:second-moment`). -/
def secondMoment [MeasurableSpace H] (p : Measure (H × ℝ)) : ℝ :=
  ∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂p

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- The probability law `‖w‖ m / ∫ ‖w‖ dm` of a nonzero integrable weight `w` (`0` otherwise):
the sampling law `p = |Γ|/V` of `eq:polar-decomposition` for `Γ = w m`. -/
def normalizedLaw {E : Type*} [NormedAddCommGroup E] (m : Measure Ω) (w : Ω → E) : Measure Ω :=
  if Integrable w m ∧ 0 < ∫ y, ‖w y‖ ∂m then
    (ENNReal.ofReal (∫ y, ‖w y‖ ∂m))⁻¹ • m.withDensity fun y => ‖w y‖ₑ
  else 0

instance {E : Type*} [NormedAddCommGroup E] (m : Measure Ω) (w : Ω → E) :
    IsFiniteMeasure (normalizedLaw m w) := by
  unfold normalizedLaw
  split_ifs with h
  · have hw : (∫⁻ y, ‖w y‖ₑ ∂m) < ⊤ := h.1.hasFiniteIntegral
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 h.2)) hw
  · infer_instance

/-- The polar sampled network `f_N(x) = (V/N) ∑_j h(θ_j) β(⟨a_j,x⟩ + c_j)` of the coefficient
measure `γ λ` (`eq:polar-network`), with `V = ∫ |γ| dλ` and `h = γ/|γ|`. -/
def polarSample {N : ℕ} [MeasurableSpace H] (β : ℝ → ℝ) (lam : Measure (H × ℝ))
    (γ : H × ℝ → ℂ) (θ : Fin N → H × ℝ) (x : H) : ℂ :=
  (((∫ p, ‖γ p‖ ∂lam) / N : ℝ) : ℂ) *
    ∑ j, γ (θ j) / (‖γ (θ j)‖ : ℂ) * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ)

/-- The sampled scalar observable of a layer, `F_{φ,N}(x) = (V/N) ∑_j h(y_j) β(⟨a_{y_j},x⟩)`
with `V = ∫ |w_φ| dm` and `h = w_φ/|w_φ|`, for a sample `y_j` of the law `|w_φ| m / V`. -/
def layerSampleScalar {N : ℕ} (m : Measure Ω) (a : Ω → H) (w : Ω → ℂ) (β : ℝ → ℝ)
    (y : Fin N → Ω) (x : H) : ℂ :=
  (((∫ y, ‖w y‖ ∂m) / N : ℝ) : ℂ) * ∑ j, w (y j) / (‖w (y j)‖ : ℂ) * (β ⟪a (y j), x⟫ : ℂ)

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The sampled `Y`-valued layer, `f_N(x) = (V/N) ∑_j β(⟨a_{y_j},x⟩) b_{y_j}/‖b_{y_j}‖` with
`V = ∫ ‖b_y‖ dm`, for a sample `y_j` of the law `‖b‖ m / V`. -/
def layerSampleVec {N : ℕ} (m : Measure Ω) (a : Ω → H) (b : Ω → Y) (β : ℝ → ℝ)
    (y : Fin N → Ω) (x : H) : Y :=
  (((∫ y, ‖b y‖ ∂m) / N : ℝ) : ℂ) • ∑ j, ((β ⟪a (y j), x⟫ / ‖b (y j)‖ : ℝ) : ℂ) • b (y j)

end Examples

/-! ### The neural-operator layer -/

section OperatorLayer

/-- `β` has polynomial growth: `|β(t)| ≤ C (1 + |t|)^p`. -/
def HasPolynomialGrowth (β : ℝ → ℝ) : Prop :=
  ∃ C p : ℝ, ∀ t, |β t| ≤ C * (1 + |t|) ^ p

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standing hypotheses of the neural-operator layer: `y ↦ a_y ∈ H` is Borel and bounded,
`y ↦ b_y ∈ Y` is Borel with `∫ ‖b_y‖ m(dy) < ∞`. -/
structure IsLayerData (m : Measure Ω) (a : Ω → H) (b : Ω → Y) : Prop where
  /-- `y ↦ a_y` is Borel. -/
  stronglyMeasurable_a : StronglyMeasurable a
  /-- `y ↦ a_y` is bounded. -/
  bounded_a : ∃ C : ℝ, ∀ y, ‖a y‖ ≤ C
  /-- `y ↦ b_y` is Borel. -/
  stronglyMeasurable_b : StronglyMeasurable b
  /-- `∫ ‖b_y‖ m(dy) < ∞`. -/
  integrable_b : Integrable b m

/-- `‖A‖_∞ = sup_y ‖a_y‖`. -/
def layerSupNorm (a : Ω → H) : ℝ :=
  ⨆ y, ‖a y‖

/-- The neural-operator layer `ℱ(x) = B β(Ax) = ∫ β(⟨a_y,x⟩) b_y m(dy)` (`eq:operator-layer`). -/
def operatorLayer (m : Measure Ω) (a : Ω → H) (b : Ω → Y) (β : ℝ → ℝ) (x : H) : Y :=
  ∫ y, ((β ⟪a y, x⟫ : ℝ) : ℂ) • b y ∂m

/-- The weight `w_φ(y) = ⟨b_y, φ⟩_Y` of the scalar observable. -/
def layerWeight (b : Ω → Y) (φ : Y) (y : Ω) : ℂ :=
  inner ℂ φ (b y)

/-- The scalar observable `F_φ(x) = ⟨ℱ(x), φ⟩_Y` of the layer. -/
def layerObservable (m : Measure Ω) (a : Ω → H) (b : Ω → Y) (β : ℝ → ℝ) (φ : Y) (x : H) :
    ℂ :=
  inner ℂ φ (operatorLayer m a b β x)

open Classical in
/-- The operator `A : H → L²(m)`, `(Ax)(y) = ⟨a_y, x⟩`, as a linear map into the a.e.-classes
`Ω →ₘ[m] ℝ` (`0` if `a` is not measurable). -/
def layerA (m : Measure Ω) (a : Ω → H) : H →ₗ[ℝ] (Ω →ₘ[m] ℝ) where
  toFun x :=
    if h : AEStronglyMeasurable a m then
      AEEqFun.mk (fun y => ⟪a y, x⟫) (h.inner aestronglyMeasurable_const)
    else 0
  map_add' x y := by
    by_cases h : AEStronglyMeasurable a m
    · simp only [dif_pos h]
      rw [AEEqFun.mk_add_mk]
      exact AEEqFun.mk_eq_mk.2 (Filter.Eventually.of_forall fun z => by simp [inner_add_right])
    · simp only [dif_neg h, add_zero]
  map_smul' c x := by
    by_cases h : AEStronglyMeasurable a m
    · simp only [dif_pos h, RingHom.id_apply]
      rw [AEEqFun.smul_mk]
      exact AEEqFun.mk_eq_mk.2 (Filter.Eventually.of_forall fun z => by
        simp [inner_smul_right])
    · simp only [dif_neg h, smul_zero]

/-- The covariance `S_y = Q - (1 + σ_y²)⁻¹ (Qa_y) ⊗ (Qa_y)`, `σ_y² = ⟨Qa_y, a_y⟩`, of
Example `ex:operator-layer`(ii). -/
def layerCovariance (Q : H →L[ℝ] H) (a : Ω → H) (y : Ω) : H →L[ℝ] H :=
  Q - (1 + ⟪Q (a y), a y⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q (a y)) (Q (a y))

variable [MeasurableSpace H]

/-- The `Y`-valued coefficient measure `Γ = ι_#(b_y m(dy))`, `ι(y) = (a_y, 0)`, of the layer. -/
def layerMeasure (m : Measure Ω) (a : Ω → H) (b : Ω → Y) : VectorMeasure (H × ℝ) Y :=
  (m.withDensityᵥ b).map fun y => (a y, 0)

/-- The coefficient measure of the ReLU form of the Gaussian-activation layer: the pushforward
of `φ''(b) b_y m(dy) db` under `(y, b) ↦ (a_y, -b)`. -/
def layerHingeMeasure (m : Measure Ω) (a : Ω → H) (b : Ω → Y) : VectorMeasure (H × ℝ) Y :=
  ((m.prod volume).withDensityᵥ fun p : Ω × ℝ => gaussianActDeriv2 p.2 • b p.1).map
    fun p => (a p.1, -p.2)

end OperatorLayer

/-! ### The periodic convolution layer on the torus -/

section Torus

instance instFactTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

/-- The torus `𝕋^d = (ℝ/2πℤ)^d`. -/
abbrev Torus (d : ℕ) : Type :=
  Fin d → AddCircle (2 * Real.pi)

/-- The normalized Haar (probability) measure on `𝕋^d`. -/
def torusHaar (d : ℕ) : Measure (Torus d) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

instance (d : ℕ) : IsProbabilityMeasure (torusHaar d) :=
  Measure.pi.instIsProbabilityMeasure _

instance instRegularHaarAddCircle : (AddCircle.haarAddCircle (T := 2 * Real.pi)).Regular := by
  unfold AddCircle.haarAddCircle
  infer_instance

instance (d : ℕ) : (torusHaar d).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance (d : ℕ) : (torusHaar d).IsNegInvariant :=
  Measure.pi.isNegInvariant _

/-- `L²(𝕋^d; ℝ)`, the input space of the convolution layer. -/
abbrev TorusL2 (d : ℕ) : Type :=
  Lp ℝ 2 (torusHaar d)

/-- `L²(𝕋^d)`, the output space of the convolution layer. -/
abbrev TorusL2C (d : ℕ) : Type :=
  Lp ℂ 2 (torusHaar d)

/-- The translation `(τ_z x)(t) = x(t - z)` on `L²(𝕋^d; ℝ)`, a linear isometry. -/
def torusTranslate (d : ℕ) (z : Torus d) : TorusL2 d →ₗᵢ[ℝ] TorusL2 d :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun t => t - z) (measurePreserving_sub_right (torusHaar d) z)

/-- The translation `(τ_z u)(t) = u(t - z)` on `L²(𝕋^d)`, a linear isometry. -/
def torusTranslateC (d : ℕ) (z : Torus d) : TorusL2C d →ₗᵢ[ℂ] TorusL2C d :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t => t - z) (measurePreserving_sub_right (torusHaar d) z)

/-- The direction `a_y = k(y - ·)` of the convolution layer. -/
def convDirection {d : ℕ} (k : TorusL2 d) (y : Torus d) : TorusL2 d :=
  Lp.compMeasurePreserving (fun t => y - t) (Measure.measurePreserving_sub_left (torusHaar d) y) k

/-- The output `b_y = ψ(· - y)` of the convolution layer, as an element of `L²(𝕋^d)`. -/
def convOutput {d : ℕ} (ψ : TorusL2 d) (y : Torus d) : TorusL2C d :=
  Complex.ofRealCLM.compLp (torusTranslate d y ψ)

/-- The constant function `1` in `L²(𝕋^d)`. -/
def torusOne (d : ℕ) : TorusL2C d :=
  toLpOrZero 2 (torusHaar d) fun _ => (1 : ℂ)

/-- The character `e_n(t) = e^{i⟨n,t⟩}` of `𝕋^d`, `n ∈ ℤ^d`. -/
def torusCharacter {d : ℕ} (n : Fin d → ℤ) (t : Torus d) : ℂ :=
  ∏ j, fourier (n j) (t j)

/-- The Fourier coefficient `f̂(n) = ∫ f(t) e^{-i⟨n,t⟩} dt` of a function on `𝕋^d` (normalized
Haar measure). -/
def torusFourierCoeff {d : ℕ} (f : Torus d → ℂ) (n : Fin d → ℤ) : ℂ :=
  ∫ t, (starRingEnd ℂ) (torusCharacter n t) * f t ∂torusHaar d

/-- `|n|² = ∑ n_j²` for a frequency `n ∈ ℤ^d`. -/
def torusFreqNormSq {d : ℕ} (n : Fin d → ℤ) : ℝ :=
  ∑ j, ((n j : ℝ)) ^ 2

open Classical in
/-- The Bessel operator `(I - Δ)^{-s}` on `L²(𝕋^d; ℝ)`: the bounded operator that multiplies the
`n`-th Fourier coefficient by `(1 + |n|²)^{-s}` (chosen among the operators with this
property, which determines it; `0` if there is none). -/
def besselOperator (d : ℕ) (s : ℝ) : TorusL2 d →L[ℝ] TorusL2 d :=
  if h : ∃ Q : TorusL2 d →L[ℝ] TorusL2 d, ∀ (x : TorusL2 d) (n : Fin d → ℤ),
      torusFourierCoeff (fun t => ((Q x) t : ℂ)) n =
        (((1 + torusFreqNormSq n) ^ (-s) : ℝ) : ℂ) * torusFourierCoeff (fun t => (x t : ℂ)) n
  then h.choose else 0

end Torus

/-! ### The Dirichlet solution operator -/

section Dirichlet

/-- The open interval `(0,1)` as a measure space (Lebesgue measure). -/
abbrev UnitOpenInterval : Type :=
  Set.Ioo (0 : ℝ) 1

instance instMeasureSpaceUnitOpenInterval : MeasureSpace UnitOpenInterval :=
  Measure.Subtype.measureSpace

instance : IsProbabilityMeasure (volume : Measure UnitOpenInterval) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  simp

/-- `L²(0,1)`, real valued: the input space of the Dirichlet example. -/
abbrev UnitL2 : Type :=
  Lp ℝ 2 (volume : Measure UnitOpenInterval)

/-- `L²(0,1)`, complex valued: the output space of the Dirichlet example. -/
abbrev UnitL2C : Type :=
  Lp ℂ 2 (volume : Measure UnitOpenInterval)

/-- The Green kernel `g(y,t) = sinh(min(y,t)) sinh(1 - max(y,t)) / sinh 1` of
`(I - ∂_t²)^{-1}` with Dirichlet boundary conditions. -/
def dirichletKernel (y t : ℝ) : ℝ :=
  Real.sinh (min y t) * Real.sinh (1 - max y t) / Real.sinh 1

/-- `g(y, ·)` as an element of `L²(0,1)`. -/
def dirichletKernelFn (y : ℝ) : UnitL2 :=
  toLpOrZero 2 volume fun t : UnitOpenInterval => dirichletKernel y t

/-- The direction `a_y = g(y,·)` of the Dirichlet layer, `y ∈ (0,1)`. -/
def dirichletDirection (y : UnitOpenInterval) : UnitL2 :=
  dirichletKernelFn y

/-- The output `b_y = g(y,·)` of the Dirichlet layer, as an element of `L²(0,1)` (complex). -/
def dirichletOutput (y : UnitOpenInterval) : UnitL2C :=
  Complex.ofRealCLM.compLp (dirichletKernelFn y)

/-- The solution `u(y) = ∫₀¹ g(y,t) x(t) dt` of `-u'' + u = x`, `u(0) = u(1) = 0`, for a
function `x`. -/
def dirichletSolution (x : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t : UnitOpenInterval, dirichletKernel y t * x t

open Classical in
/-- The integral operator on `L²(m)` with kernel `k`: the bounded operator `T` with
`(Tx)(y) = ∫ k(y,t) x(t) m(dt)` a.e. (which determines it; `0` if there is none). -/
def integralOperator {α : Type*} [MeasurableSpace α] (m : Measure α) (k : α → α → ℝ) :
    Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  if h : ∃ T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m, ∀ x : Lp ℝ 2 m,
      (T x : α → ℝ) =ᵐ[m] fun y => ∫ t, k y t * x t ∂m
  then h.choose else 0

/-- The Dirichlet solution operator `𝖦 = (I - ∂_t²)^{-1}` on `L²(0,1)`, the integral operator
with kernel `g`. -/
def dirichletOperator : UnitL2 →L[ℝ] UnitL2 :=
  integralOperator volume fun y t : UnitOpenInterval => dirichletKernel y t

/-- The eigenvalues `λ_n = (1 + π²n²)⁻¹` of `𝖦`. -/
def dirichletEigenvalue (n : ℕ) : ℝ :=
  (1 + Real.pi ^ 2 * (n : ℝ) ^ 2)⁻¹

/-- The eigenfunctions `e_n(t) = √2 sin(nπt)` of `𝖦`, as elements of `L²(0,1)` (`e_0 = 0`). -/
def dirichletEigenfunction (n : ℕ) : UnitL2 :=
  toLpOrZero 2 volume fun t : UnitOpenInterval => Real.sqrt 2 * Real.sin (n * Real.pi * t)

/-- The `2N`-neuron ReLU truncation
`𝖦_N x = ∑_{n=1}^N λ_n [ReLU(⟨e_n,x⟩) - ReLU(-⟨e_n,x⟩)] e_n` of the exact ReLU network of
`𝖦`. -/
def dirichletReLUTruncation (N : ℕ) (x : UnitL2) : UnitL2 :=
  spectralReLUNetwork (Finset.Icc 1 N) dirichletEigenvalue
    (fun n => ⟪dirichletEigenfunction n, x⟫) dirichletEigenfunction

end Dirichlet

end OperatorRidgelet
