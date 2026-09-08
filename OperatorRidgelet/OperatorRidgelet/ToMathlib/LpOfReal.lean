import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

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
