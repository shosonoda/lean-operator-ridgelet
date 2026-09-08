import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Glue between `L²` norms, Bochner integrals of squared norms, and `lintegral`s

Small general facts used to move between the three descriptions of square integrability:
`MemLp f 2 μ`, `∫ ‖f‖² < ∞`, and `∫⁻ ‖f‖ₑ² < ∞`; the squared norm of an `L²` element as a
Bochner integral; `∫ f conj f = ∫ ‖f‖²`; and two elementary inequalities, `ab ≤ a² + b²` in
`ℝ≥0∞` and the weighted arithmetic–geometric mean inequality `ab ≤ a² w⁻¹ + b² w` in `ℝ`.
-/

open scoped ENNReal ComplexConjugate

/-- `ab ≤ a² + b²` in `ℝ≥0∞`. -/
theorem ENNReal.mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- The weighted arithmetic–geometric mean inequality `AB ≤ A² w⁻¹ + B² w` for `w > 0`. -/
theorem Real.mul_le_sq_mul_inv_add_sq_mul {A B w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : 0 < w) :
    A * B ≤ A ^ 2 * w⁻¹ + B ^ 2 * w := by
  have h1 : A * B * w ≤ A ^ 2 + B ^ 2 * w ^ 2 := by
    nlinarith [sq_nonneg (A - B * w), mul_nonneg (mul_nonneg hA hB) hw.le]
  calc A * B = (A * B * w) * w⁻¹ := by field_simp
    _ ≤ (A ^ 2 + B ^ 2 * w ^ 2) * w⁻¹ := by gcongr
    _ = A ^ 2 * w⁻¹ + B ^ 2 * w := by field_simp

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : Type*} [NormedAddCommGroup E]

/-- The square of the `L²` seminorm is the lower Lebesgue integral of the squared enorm. -/
theorem eLpNorm_two_sq_eq_lintegral_enorm_sq' (g : X → E) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num [ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A square-integrable function has finite `∫⁻ ‖g‖ₑ²`. -/
theorem MemLp.lintegral_enorm_sq_lt_top {g : X → E} (hg : MemLp g 2 μ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ < ⊤ := by
  rw [← eLpNorm_two_sq_eq_lintegral_enorm_sq']
  exact ENNReal.pow_lt_top hg.eLpNorm_lt_top

/-- A measurable function with finite `∫⁻ ‖g‖ₑ²` is square integrable. -/
theorem memLp_two_of_lintegral_enorm_sq_lt_top {g : X → E} (hg : AEStronglyMeasurable g μ)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ < ⊤) : MemLp g 2 μ := by
  refine ⟨hg, ?_⟩
  have h2 : eLpNorm g 2 μ ^ 2 < ⊤ := by rwa [eLpNorm_two_sq_eq_lintegral_enorm_sq']
  exact (ENNReal.pow_lt_top_iff.mp h2).resolve_right two_ne_zero

/-- The Bochner integral of a squared norm is the `toReal` of the corresponding `lintegral`. -/
theorem integral_norm_sq_eq_toReal_lintegral' {v : X → E} (hv : AEStronglyMeasurable v μ) :
    ∫ x, ‖v x‖ ^ 2 ∂μ = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖v x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) (hv.norm.pow 2)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The squared `L²` norm of an `L²` element is the integral of its squared norm. -/
theorem Lp.norm_sq_eq_integral_norm_sq (u : Lp E 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, integral_norm_sq_eq_toReal_lintegral' (Lp.aestronglyMeasurable u),
    ← eLpNorm_two_sq_eq_lintegral_enorm_sq', ENNReal.toReal_pow]

/-- The squared `L²` norm of `MemLp.toLp g` is `∫ ‖g‖²`. -/
theorem MemLp.norm_toLp_two_sq {g : X → E} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [Lp.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

/-- `∫ g conj g = ∫ ‖g‖²` as complex numbers. -/
theorem integral_mul_conj_self (g : X → ℂ) :
    ∫ x, g x * conj (g x) ∂μ = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have h := integral_ofReal (𝕜 := ℂ) (μ := μ) (f := fun x => ‖g x‖ ^ 2)
  refine Eq.trans ?_ h
  congr 1
  funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- The enorm of `‖z‖² t` for `t ≥ 0`. -/
theorem enorm_norm_sq_mul_ofReal (z : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖‖z‖ ^ 2 * t‖ₑ = ‖z‖ₑ ^ 2 * ENNReal.ofReal t := by
  rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end MeasureTheory
