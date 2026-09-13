import OperatorRidgelet.Sobolev.Defs
import LeanRidgelet.Fourier.AngularDistribution
import OperatorRidgelet.ToMathlib.PolynomialGaussianSchwartz
import OperatorRidgelet.ToMathlib.SchwartzFourier

/-!
# Definitions for Appendix I.3, the Gaussian-derivative filters

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.  The filter of `prop:nonbandpass-sobolev` is the real Schwartz function whose Fourier
transform is `ρ̂_k(ω) = ω^{2k} e^{-ω²}`: it is built as the inverse angular transform of that
symbol, which is real because the symbol is real and even.

The target `g(ξ) = e^{-‖ξ‖²} v` gives the rays `h_a(ω) = ρ̂_k(-ω) g(ωa) = ω^{2k} e^{-A²ω²} v`
at the scale `A(a) = (1+‖a‖²)^{1/2}`, whose coefficients are the dilates
`A^{-2k-1} ρ_k(b/A) v` of the filter, and the Sobolev test `q_{α,ρ_k}` is the subordination
superposition of the same dilates over the scales `(1+u)^{1/2}`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Set Complex LeanRidgelet LeanRidgelet.Fourier
open scoped Polynomial FourierTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The Fourier transform `ρ̂(ω) = ω^{2k} e^{-ω²}` of the Gaussian-derivative filter of order
`k`, as a real Schwartz function. -/
def gaussDerivHat (k : ℕ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (realDilationCLE (Real.sqrt 2) (by positivity))
    (Real.polynomialGaussianSchwartz (Polynomial.C (((2 : ℝ) ^ k)⁻¹) * Polynomial.X ^ (2 * k)))

/-- The Fourier transform of the filter, read in Mathlib's frequency variable:
`ξ ↦ ρ̂(2πξ)`. -/
def gaussDerivDilatedHat (k : ℕ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (realDilationCLE (2 * Real.pi) (by positivity)) (gaussDerivHat k)

/-- The Gaussian-derivative filter of order `k`, as a complex Schwartz function; it is
real-valued (`gaussDerivFilterC_conj`). -/
def gaussDerivFilterC (k : ℕ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.ofReal (gaussDerivDilatedHat k))

/-- The Gaussian-derivative filter `ρ_k ∈ 𝒮(ℝ;ℝ)` of order `k` of `prop:nonbandpass-sobolev`. -/
def gaussDerivFilter (k : ℕ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM (gaussDerivFilterC k)

/-- The scale `A(a) = (1 + ‖a‖²)^{1/2}` of the ray in direction `a`. -/
def rayScale (a : H) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)

/-- The Gaussian target `g(ξ) = e^{-‖ξ‖²} v` of `prop:nonbandpass-sobolev`. -/
def gaussTarget (v : Y) (ξ : H) : Y := (Real.exp (-‖ξ‖ ^ 2) : ℝ) • v

/-- The scalar ray `A^{-2k-1} ρ_k(b/A)` of the Gaussian-derivative filter at scale `A`. -/
def gaussRayFun (k : ℕ) (A b : ℝ) : ℂ :=
  (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) • gaussDerivFilterC k (b / A)

/-- The coefficient of the Gaussian-derivative ray: the dilate `A^{-2k-1} ρ_k(b/A) v` of the
filter. -/
def gaussRayCoefficient (k : ℕ) (v : Y) (q : H × ℝ) : Y :=
  gaussRayFun k (rayScale q.1) q.2 • v

/-- The subordination scale `B(u) = (1+u)^{1/2}`. -/
def subScale (u : ℝ) : ℝ := Real.sqrt (1 + u)

/-- The coefficient of `q_{α,ρ_k}`: the subordination superposition of the dilated filters. -/
def gaussSobolevRay (k : ℕ) (α : ℝ) (b : ℝ) : ℂ :=
  (Real.Gamma (α / 2))⁻¹ • ∫ u in Ioi (0 : ℝ),
    (u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b

end OperatorRidgelet
