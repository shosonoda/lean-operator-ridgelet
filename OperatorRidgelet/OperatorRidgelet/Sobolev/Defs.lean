import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Definitions for the weak Sobolev synthesis of Section 5 and Appendix C

Definitions only, free of `sorry`; both `Challenge` and `OperatorRidgelet.Paper` import this
module.

## The Sobolev space along a ray

The manuscript works with the frequency profile `h : ℝ → Y` of a ray and its inverse Fourier
transform `γ = ȟ`, the coefficient in the bias variable, in the angular convention
`ĥ(ω) = ∫ h(b) e^{-iωb} db`.  The Sobolev norm of order `s` is normalized by

`‖h‖²_{H^s_ω} = 2π ∫ ⟨t⟩^{2s} ‖γ(t)‖² dt`,   `⟨t⟩ = (1 + t²)^{1/2}`,

so that `‖h‖_{H^0_ω} = ‖h‖_{L²}`.  Rather than construct the space, the statements carry the
pair `(h, γ)`: `MemRaySobolev s γ` is the square integrability of `γ` against the weight
`⟨t⟩^{2s}` and `raySobolevNorm s γ` is the displayed norm.  For `s > 1/2` the coefficient is
integrable (Lemma `lem:sobolev-tools`), so the profile is the ordinary Fourier integral
`rayProfile γ`, and no `L²` extension of the transform is needed.

`sobolevMomentConst s r` is the constant `A_{s,r} = (2π)^{-1/2}(∫ (1+t²)^{-(s-r)} dt)^{1/2}`
of Lemma `lem:sobolev-tools`, and `sobolevPairingConst σ s` is `b_{σ,s} = ‖⟨·⟩^{-s} σ‖_2` of
Lemma `lem:sobolev-pairing`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The Japanese bracket `⟨t⟩ = (1 + t²)^{1/2}` on the line. -/
def bracket (t : ℝ) : ℝ := (1 + t ^ 2) ^ ((1 : ℝ) / 2)

/-- The coefficient `γ` of a ray is square integrable against the Sobolev weight `⟨t⟩^{2s}`. -/
def MemRaySobolev (s : ℝ) (γ : ℝ → Y) : Prop :=
  MemLp (fun t => (bracket t ^ s : ℝ) • γ t) 2 volume

/-- The Sobolev norm `‖h‖_{H^s_ω} = (2π ∫ ⟨t⟩^{2s} ‖γ(t)‖² dt)^{1/2}` of the profile whose
inverse Fourier transform is `γ` (`eq:sobolev-norm`). -/
def raySobolevNorm (s : ℝ) (γ : ℝ → Y) : ℝ :=
  Real.sqrt (2 * Real.pi * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2)

/-- The frequency profile `γ̂(ω) = ∫ γ(b) e^{-iωb} db` of a ray coefficient, in the angular
convention of the manuscript. -/
def rayProfile (γ : ℝ → Y) (ω : ℝ) : Y :=
  ∫ b : ℝ, Complex.exp ((-(ω * b) : ℝ) * Complex.I) • γ b

/-- The constant `A_{s,r} = (2π)^{-1/2}(∫_ℝ (1+t²)^{-(s-r)} dt)^{1/2}` of Lemma
`lem:sobolev-tools`, finite exactly when `s - r > 1/2`. -/
def sobolevMomentConst (s r : ℝ) : ℝ :=
  Real.sqrt (∫ t : ℝ, ((1 + t ^ 2) ^ (-(s - r)) : ℝ)) / Real.sqrt (2 * Real.pi)

/-- The Sobolev pairing `L_σ^Y(h) = ∫ σ(t) • γ(-t) dt` of an activation `σ` of polynomial
growth with the profile `h` whose inverse Fourier transform is `γ` (`eq:sobolev-pairing`). -/
def sobolevPairing (σ : ℝ → ℂ) (γ : ℝ → Y) : Y := ∫ t : ℝ, σ t • γ (-t)

/-- The constant `b_{σ,s} = ‖⟨·⟩^{-s} σ‖_2` of Lemma `lem:sobolev-pairing`. -/
def sobolevPairingConst (σ : ℝ → ℂ) (s : ℝ) : ℝ :=
  Real.sqrt (∫ t : ℝ, ‖(bracket t ^ (-s) : ℝ) • σ t‖ ^ 2)

end OperatorRidgelet
