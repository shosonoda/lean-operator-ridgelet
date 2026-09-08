import OperatorRidgelet.Transform.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Definitions for Appendix G (the finite-dimensional case)

Definitions only, free of `sorry`.  On `H = ℝ^m` (`EuclideanSpace ℝ (Fin m)`) with `P = I` and
`0 < α < m`, the homogeneous Gaussian mixture is the explicit measure
`ν_α(da) = c_{m,α} ‖a‖^{α-m} da` (manuscript equation `eq:finite-density`); this module records
that reference measure, the Fourier transform on `ℝ^m` in the manuscript's convention, the
representative `t_f` of the frame operator, and the fractional Laplacian as a Fourier
multiplier, which is what the manuscript's `(-Δ)^{s}` means on the Fourier side.
-/

noncomputable section

namespace OperatorRidgelet.FiniteDim

open MeasureTheory Complex
open scoped ENNReal RealInnerProductSpace

/-- The Euclidean space `ℝ^m`. -/
abbrev Euclid (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The constant `c_{m,α} = 2^{-α} π^{-m/2} Γ((m-α)/2)` of the finite-dimensional density. -/
def mixtureConst (m : ℕ) (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (-α) * Real.pi ^ (-(m : ℝ) / 2) * Real.Gamma ((m - α) / 2)

/-- The finite-dimensional reference measure `ν_α(da) = c_{m,α} ‖a‖^{α-m} da` on `ℝ^m`. -/
def directionMeasure (m : ℕ) (α : ℝ) : Measure (Euclid m) :=
  volume.withDensity fun a => ENNReal.ofReal (mixtureConst m α * ‖a‖ ^ (α - m))

/-- The constant `k_{m,α} = (2π)^m c_{m,α}` of the filtered backprojection. -/
def frameConst (m : ℕ) (α : ℝ) : ℝ :=
  (2 * Real.pi) ^ m * mixtureConst m α

/-- The Fourier transform `ĝ(ξ) = ∫ g(x) exp(-i⟪x,ξ⟫) dx` on `ℝ^m`. -/
def fourier {m : ℕ} (g : Euclid m → ℂ) (ξ : Euclid m) : ℂ :=
  LeanRidgelet.Fourier.angularFourierIntegralInner g ξ

/-- The measure `p dx` with a nonnegative density `p` (the pivot measure of Appendix G). -/
def densityMeasure {m : ℕ} (p : Euclid m → ℝ) : Measure (Euclid m) :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

/-- The representative `t_f(x) = ∫ exp(i⟪x,ξ⟫) ĝ(ξ) ν(dξ)` of the frame operator against the
pivot measure, for `g = f p`. -/
def frameRepresentative {m : ℕ} (ν : Measure (Euclid m)) (g : Euclid m → ℂ) (x : Euclid m) : ℂ :=
  ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * fourier g ξ ∂ν

/-- The fractional Laplacian `(-Δ)^s g` as the Fourier multiplier `‖ξ‖^{2s}` in the
manuscript's convention:
`(-Δ)^s g (x) = (2π)^{-m} ∫ exp(i⟪x,ξ⟫) ‖ξ‖^{2s} ĝ(ξ) dξ`.  For `s = -(m-α)/2` it is the
Riesz potential `(-Δ)^{-(m-α)/2}`. -/
def fracLaplacian {m : ℕ} (s : ℝ) (g : Euclid m → ℂ) (x : Euclid m) : ℂ :=
  (((2 * Real.pi) ^ m)⁻¹ : ℝ) *
    ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * ((‖ξ‖ ^ (2 * s) : ℝ) : ℂ) * fourier g ξ

end OperatorRidgelet.FiniteDim
