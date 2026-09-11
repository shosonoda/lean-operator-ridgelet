import OperatorRidgelet.Transform.Defs
import LeanRidgelet.Fourier.AngularDistribution

/-!
# The distributional admissibility constant

The manuscript pairs the Fourier transform of a tempered synthesis activation `β ∈ 𝒮'(ℝ)` with
the band-pass analysis filter:
`C^{(α)}_{β,ρ} = (2π)⁻¹ ⟨β̂, ρ̂(-·) |·|^{-α}⟩` (Theorem A(iii); the "distributional
admissibility" displayed at the start of Section 5).  The test function `ω ↦ ρ̂(-ω) |ω|^{-α}` is
Schwartz exactly when `ρ̂` vanishes near the origin, which is the band-pass condition; below it
is taken as a `SchwartzMap` whenever one with these values exists, and as `0` otherwise, so that
the constant is defined for every `ρ` and every `α` without a proof obligation inside the
definition.  Tempered distributions are Mathlib's `TemperedDistribution ℝ ℂ`, and the Fourier
transform on them is the manuscript-convention `angularFourierDistribution` of the vendored
`LeanRidgelet` files.

This module is shared by Section 4 (Theorem A(iii)) and Section 5; do not restate the constant
elsewhere.
-/

noncomputable section

namespace OperatorRidgelet

open LeanRidgelet.Fourier

open Classical in
/-- The test filter `ω ↦ ρ̂(-ω) |ω|^{-α}` as a Schwartz function, when one with these values
exists (in particular when `ρ` is band-pass); `0` otherwise. -/
def temperedTestFilter (α : ℝ) (ρ : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  if h : ∃ φ : SchwartzMap ℝ ℂ, ∀ ω : ℝ, φ ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ)
  then h.choose else 0

/-- The tempered test filter has the prescribed weighted Fourier values when they are Schwartz. -/
theorem temperedTestFilter_apply {α : ℝ} {ρ : SchwartzMap ℝ ℝ}
    (h : ∃ φ : SchwartzMap ℝ ℂ, ∀ ω : ℝ, φ ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ))
    (ω : ℝ) :
    temperedTestFilter α ρ ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
  classical
  rw [temperedTestFilter, dif_pos h]
  exact h.choose_spec ω

/-- The distributional admissibility constant
`C^{(α)}_{β,ρ} = (2π)⁻¹ ⟨β̂, ρ̂(-·) |·|^{-α}⟩` of a tempered activation `β` and a filter `ρ`. -/
def temperedAdmissibilityConst (α : ℝ) (β : TemperedDistribution ℝ ℂ) (ρ : SchwartzMap ℝ ℝ) :
    ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β (temperedTestFilter α ρ)

end OperatorRidgelet
