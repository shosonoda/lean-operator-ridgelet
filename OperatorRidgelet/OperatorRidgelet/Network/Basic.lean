import OperatorRidgelet.Network.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Lipschitz estimates for scalar ridge networks

These envelopes give integrability of scalar ridge features under a first parameter moment.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Topology
open scoped ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A globally Lipschitz function has a linear growth envelope based at zero. -/
theorem norm_le_of_lipschitzWith {E : Type*} [NormedAddCommGroup E] {β : ℝ → E} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (t : ℝ) : ‖β t‖ ≤ ‖β 0‖ + L * |t| := by
  have h := hβ.dist_le_mul t 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero, Real.norm_eq_abs] at h
  calc ‖β t‖ = ‖β 0 + (β t - β 0)‖ := by congr 1; abel
    _ ≤ ‖β 0‖ + ‖β t - β 0‖ := norm_add_le _ _
    _ ≤ ‖β 0‖ + L * |t| := by linarith

/-- The Lipschitz envelope of a scalar ridge: `‖β(⟪a, x⟫ + c)‖` is dominated by a multiple of
`1 + ‖a‖ + |c|`. -/
theorem norm_ridge_le {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β) (x : H) (θ : H × ℝ) :
    ‖β (inner ℝ θ.1 x + θ.2)‖ ≤ (‖β 0‖ + L * max ‖x‖ 1) * (1 + ‖θ.1‖ + |θ.2|) := by
  have h1 := norm_le_of_lipschitzWith hβ (inner ℝ θ.1 x + θ.2)
  have h2 : |inner ℝ θ.1 x + θ.2| ≤ ‖θ.1‖ * ‖x‖ + |θ.2| :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) le_rfl)
  have hM : ‖x‖ ≤ max ‖x‖ 1 := le_max_left _ _
  have hM1 : (1 : ℝ) ≤ max ‖x‖ 1 := le_max_right _ _
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have h3 : ‖θ.1‖ * ‖x‖ + |θ.2| ≤ max ‖x‖ 1 * (‖θ.1‖ + |θ.2|) := by
    nlinarith [mul_le_mul_of_nonneg_left hM (norm_nonneg θ.1),
      mul_le_mul_of_nonneg_left hM1 (abs_nonneg θ.2)]
  have h4 : (L : ℝ) * |inner ℝ θ.1 x + θ.2| ≤ L * (max ‖x‖ 1 * (‖θ.1‖ + |θ.2|)) :=
    mul_le_mul_of_nonneg_left (h2.trans h3) hL
  nlinarith [norm_nonneg (β 0), norm_nonneg θ.1, abs_nonneg θ.2,
    mul_nonneg hL (zero_le_one.trans hM1),
    mul_nonneg (norm_nonneg (β 0)) (add_nonneg (norm_nonneg θ.1) (abs_nonneg θ.2))]

/-- Under the first-moment condition, a globally Lipschitz activation gives an integrable
ridge: the Bochner integral defining `S_β[Γ](x)` exists. -/
theorem integrable_ridge_of_lipschitz [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (Γ : VectorMeasure (H × ℝ) Y)
    (hmom : Integrable (fun θ : H × ℝ => 1 + ‖θ.1‖ + |θ.2|) Γ.variation) (x : H) :
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) := by
  refine Integrable.mono' (hmom.const_mul (‖β 0‖ + L * max ‖x‖ 1)) ?_
    (Filter.Eventually.of_forall fun θ => norm_ridge_le hβ x θ)
  exact (hβ.continuous.comp
    (by fun_prop : Continuous fun θ : H × ℝ => inner ℝ θ.1 x + θ.2)).aestronglyMeasurable

end OperatorRidgelet
