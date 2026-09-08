import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Characteristic functions of coordinate maps

For a finite measure `μ` on a real inner product space `E` and vectors `v, w ∈ E`, the
characteristic function of the law of the coordinate `x ↦ ⟪x, v⟫` is `s ↦ charFun μ (s • v)`,
and the characteristic function of the joint law of `x ↦ (⟪x, v⟫, ⟪x, w⟫)` (as a random
variable in the Hilbert space `WithLp 2 (ℝ × ℝ)`) is `t ↦ charFun μ (t₁ • v + t₂ • w)`.  Together
with `ProbabilityTheory.indepFun_iff_charFun_prod` this reduces the independence of two
coordinates to a computation with the characteristic function of `μ`.
-/

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- The characteristic function of the law of the coordinate `x ↦ ⟪x, v⟫` under `μ` is
`s ↦ charFun μ (s • v)`. -/
theorem charFun_map_inner_right (μ : Measure E) (v : E) (s : ℝ) :
    charFun (μ.map fun x => ⟪x, v⟫) s = charFun μ (s • v) := by
  have hmeas : Measurable fun x : E => ⟪x, v⟫ := (continuous_id.inner continuous_const).measurable
  rw [charFun_apply_real, charFun_apply,
    integral_map hmeas.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  funext x
  rw [real_inner_smul_right, Complex.ofReal_mul]

/-- The characteristic function of the joint law of the coordinates `x ↦ (⟪x, v⟫, ⟪x, w⟫)`,
taken in the Hilbert space `WithLp 2 (ℝ × ℝ)`, is `t ↦ charFun μ (t₁ • v + t₂ • w)`. -/
theorem charFun_map_inner_pair (μ : Measure E) (v w : E) (t : WithLp 2 (ℝ × ℝ)) :
    charFun (μ.map fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) t =
      charFun μ ((WithLp.ofLp t).1 • v + (WithLp.ofLp t).2 • w) := by
  have hv : Measurable fun x : E => ⟪x, v⟫ := (continuous_id.inner continuous_const).measurable
  have hw : Measurable fun x : E => ⟪x, w⟫ := (continuous_id.inner continuous_const).measurable
  have hmeas : Measurable fun x : E => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫) := by fun_prop
  rw [charFun_apply, charFun_apply,
    integral_map hmeas.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  funext x
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial, inner_add_right,
    real_inner_smul_right]

end MeasureTheory
