import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Real Schwartz functions and the injectivity of the Fourier transform

A real Schwartz function `ρ : 𝓢(ℝ, ℝ)` is a complex Schwartz function `SchwartzMap.ofReal ρ`
through `Complex.ofRealCLM`, and the Fourier transform (Mathlib's `𝓕`) of `t ↦ (ρ t : ℂ)`
vanishes identically only if `ρ = 0`, by Fourier inversion on Schwartz space.
-/

open scoped FourierTransform

namespace SchwartzMap

/-- A real Schwartz function, viewed as a complex Schwartz function. -/
noncomputable def ofReal (ρ : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM ρ

/-- The complexification of a real Schwartz function evaluates by the scalar inclusion. -/
@[simp]
theorem ofReal_apply (ρ : SchwartzMap ℝ ℝ) (t : ℝ) : ofReal ρ t = (ρ t : ℂ) := rfl

/-- A real Schwartz function whose Fourier transform vanishes identically is zero. -/
theorem eq_zero_of_fourier_ofReal_eq_zero {ρ : SchwartzMap ℝ ℝ}
    (h : ∀ ω : ℝ, 𝓕 (fun t => (ρ t : ℂ)) ω = 0) : ρ = 0 := by
  have hc : 𝓕 (ofReal ρ) = 0 := by
    ext ω
    rw [SchwartzMap.fourier_coe, FunLike.coe_zero, Pi.zero_apply]
    exact h ω
  have h0 : ofReal ρ = 0 :=
    (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).injective (by simpa using hc)
  ext t
  have := DFunLike.congr_fun h0 t
  simpa using this

end SchwartzMap
