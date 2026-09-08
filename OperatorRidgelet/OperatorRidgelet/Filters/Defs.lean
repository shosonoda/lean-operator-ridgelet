import OperatorRidgelet.Transform.Defs

/-!
# Definitions for Appendix I (explicit admissible filters)

Definitions only, free of `sorry`.  The band-pass filter `ρ_bp` is defined through its Fourier
transform `ρ̂_bp(ω) = -η(2|ω| - 3)` with the bump `η(u) = exp(-1/(1-u²))` on `|u| < 1`, and the
Mexican hat is `ρ_MH(t) = (1 - t²) exp(-t²/2)`.  Both are real Schwartz functions; since the
Schwartz estimates are theorems, the `SchwartzMap` structures are obtained by choice from the
explicit functions (with junk value `0` should the explicit function fail to be Schwartz), and
the examples assert that the chosen Schwartz maps have the explicit values.
-/

noncomputable section

namespace OperatorRidgelet.Filters

open MeasureTheory Complex

/-- The bump `η(u) = exp(-1/(1-u²))` for `|u| < 1` and `η(u) = 0` otherwise. -/
def bump (u : ℝ) : ℝ :=
  if |u| < 1 then Real.exp (-1 / (1 - u ^ 2)) else 0

/-- The Fourier transform `ρ̂_bp(ω) = -η(2|ω| - 3)` of the band-pass filter, supported in
`{1 ≤ |ω| ≤ 2}`. -/
def bandPassHat (ω : ℝ) : ℝ :=
  -bump (2 * |ω| - 3)

/-- The band-pass filter as a function: the Fourier inversion
`ρ_bp(t) = (2π)⁻¹ ∫ ρ̂_bp(ω) exp(itω) dω`, which is real because `ρ̂_bp` is real and even. -/
def bandPassFun (t : ℝ) : ℝ :=
  (((2 * Real.pi)⁻¹ : ℝ) *
    ∫ ω : ℝ, (bandPassHat ω : ℂ) * Complex.exp ((t * ω : ℝ) * Complex.I)).re

open Classical in
/-- The band-pass filter `ρ_bp ∈ 𝒮(ℝ)` (junk value `0` if `bandPassFun` were not Schwartz). -/
def bandPass : SchwartzMap ℝ ℝ :=
  if h : ∃ ρ : SchwartzMap ℝ ℝ, ⇑ρ = bandPassFun then h.choose else 0

/-- The Mexican hat `ρ_MH(t) = (1 - t²) exp(-t²/2)` as a function. -/
def mexicanHatFun (t : ℝ) : ℝ :=
  (1 - t ^ 2) * Real.exp (-t ^ 2 / 2)

open Classical in
/-- The Mexican hat `ρ_MH ∈ 𝒮(ℝ)` (junk value `0` if `mexicanHatFun` were not Schwartz). -/
def mexicanHat : SchwartzMap ℝ ℝ :=
  if h : ∃ ρ : SchwartzMap ℝ ℝ, ⇑ρ = mexicanHatFun then h.choose else 0

end OperatorRidgelet.Filters
