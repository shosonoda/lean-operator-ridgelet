import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The complexification of a real `Lp` function is isometric

`Complex.ofRealCLM.compLp f` has the same `Lp` norm as the real function `f`
(`MeasureTheory.norm_ofRealCLM_compLp`).
-/

open MeasureTheory

namespace MeasureTheory

/-- The complexification `f ↦ (f : ℂ)` of an `Lp` function is isometric. -/
theorem norm_ofRealCLM_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal}
    (f : Lp ℝ p μ) : ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' f] with t ht
  rw [ht, Complex.ofRealCLM_apply, Complex.norm_real]

end MeasureTheory

namespace MeasureTheory

/-- The complexification of real `L²` functions preserves their inner product. -/
theorem inner_ofRealCLM_compLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f g : Lp ℝ 2 μ) :
    inner ℂ (Complex.ofRealCLM.compLp f) (Complex.ofRealCLM.compLp g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' f,
    Complex.ofRealCLM.coeFn_compLp' g] with t h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, Complex.ofRealCLM_apply]

end MeasureTheory
