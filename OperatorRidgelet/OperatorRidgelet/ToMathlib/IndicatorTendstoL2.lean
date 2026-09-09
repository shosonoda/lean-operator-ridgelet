import OperatorRidgelet.ToMathlib.L2Glue
import LeanRidgelet.ToMathlib.L2Duality
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Truncations converge in `L²`

If `g ∈ L²(μ)` and `S n` are measurable sets such that every point eventually lies in `S n`,
then the truncations `1_{S n} g` converge to `g` in `L²(μ)` (dominated convergence).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

/-- `∫⁻ ‖1_{S n} g - g‖ₑ² dμ → 0` for `g ∈ L²(μ)` and an exhausting sequence of measurable
sets `S n`. -/
theorem tendsto_lintegral_enorm_indicator_sub_sq {g : α → E} (hg : MemLp g 2 μ) {S : ℕ → Set α}
    (hS : ∀ n, MeasurableSet (S n)) (hmem : ∀ x, ∀ᶠ n in atTop, x ∈ S n) :
    Tendsto (fun n => ∫⁻ x, ‖(S n).indicator g x - g x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
    (F := fun n x => ‖(S n).indicator g x - g x‖ₑ ^ 2) (f := fun _ => 0) (fun x => ‖g x‖ₑ ^ 2)
    (fun n => ((hg.1.indicator (hS n)).sub hg.1).enorm.pow_const 2) ?_
    hg.lintegral_enorm_sq_lt_top.ne ?_
  · simpa using h
  · intro n
    filter_upwards with x
    by_cases hx : x ∈ S n
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · filter_upwards with x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem x] with n hn
    simp [Set.indicator_of_mem hn]

/-- `1_{S n} g → g` in the `L²` seminorm for `g ∈ L²(μ)` and an exhausting sequence of
measurable sets `S n`. -/
theorem tendsto_eLpNorm_indicator_sub {g : α → E} (hg : MemLp g 2 μ) {S : ℕ → Set α}
    (hS : ∀ n, MeasurableSet (S n)) (hmem : ∀ x, ∀ᶠ n in atTop, x ∈ S n) :
    Tendsto (fun n => eLpNorm ((S n).indicator g - g) 2 μ) atTop (𝓝 0) := by
  have h := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp
    (tendsto_lintegral_enorm_indicator_sub_sq hg hS hmem)
  rw [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h.congr fun n => ?_
  rw [eLpNorm_two_eq_lintegral_enorm_sq]
  rfl

end MeasureTheory
