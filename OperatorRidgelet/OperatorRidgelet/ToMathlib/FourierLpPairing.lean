import Mathlib.Analysis.Fourier.LpSpace

/-! # Vector-valued L² Parseval against scalar Schwartz tests -/

noncomputable section
open MeasureTheory Complex Filter Topology
open scoped FourierTransform ComplexConjugate
namespace MeasureTheory
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Inverse Fourier transformation of the conjugate of a Schwartz function. -/
theorem fourierInv_conj_schwartz (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕⁻ (fun t => conj (φ t)) x = conj (𝓕 (φ : ℝ → ℂ) x) := by
  rw [Real.fourierInv_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2
  push_cast
  ring

/-- Vector-valued L² Parseval against a scalar Schwartz test function. -/
theorem integral_fourier_toLp_conj_smul_fourier_schwartz {u : ℝ → Y}
    (hu : MemLp u 2 volume) (φ : SchwartzMap ℝ ℂ) :
    (∫ x, conj (𝓕 (φ : ℝ → ℂ) x) • (𝓕 (hu.toLp u) : Lp Y 2 volume) x) =
      ∫ x, conj (φ x) • u x := by
  let ψ : SchwartzMap ℝ ℂ :=
    SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ
  have he := congrArg (fun T : TemperedDistribution ℝ Y => T (𝓕⁻ ψ))
    (Lp.fourier_toTemperedDistribution_eq (hu.toLp u))
  rw [TemperedDistribution.fourier_apply, FourierTransform.fourier_fourierInv_eq,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at he
  calc
    _ = ∫ x, (𝓕⁻ ψ) x • (𝓕 (hu.toLp u) : Lp Y 2 volume) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [SchwartzMap.fourierInv_coe]
      exact congrArg (fun c => c • (𝓕 (hu.toLp u) : Lp Y 2 volume) x)
        (fourierInv_conj_schwartz φ x).symm
    _ = ∫ x, ψ x • (hu.toLp u) x := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx]
      rfl


end MeasureTheory
