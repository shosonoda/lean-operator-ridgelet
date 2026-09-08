import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import OperatorRidgelet.ToMathlib.TemperateGrowthInv

/-!
# Schwartz functions supported away from the origin

A Schwartz function `φ : 𝓢(ℝ, ℂ)` whose support stays away from `0` may be multiplied by
`ω ↦ ω⁻²` or by `ω ↦ |ω| ^ r` and remains a Schwartz function.  The multiplier is not of
temperate growth on `ℝ` (it is singular at the origin), so it is replaced on a neighbourhood of
`0`, disjoint from the support of `φ`, by a smooth positive function: with a smooth bump `b`
equal to one near `0`, the function `ω ↦ ω² + b ω` is smooth, of temperate growth, and bounded
below by a positive constant, so `Function.HasTemperateGrowth.inv_of_le` applies.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace SchwartzMap

/-- A function supported away from the origin vanishes on a punctured neighbourhood: there is
`δ > 0` with `δ ≤ |ω|` on the support. -/
theorem exists_pos_le_abs_of_zero_notMem_tsupport {g : ℝ → ℂ} (hg : (0 : ℝ) ∉ tsupport g) :
    ∃ δ > (0 : ℝ), ∀ ω ∈ tsupport g, δ ≤ |ω| := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0 hg
  refine ⟨δ, hδ, fun ω hω => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hball (by simpa [Real.dist_eq] using hlt) hω

/-- The smooth bump equal to one on `[-δ/2, δ/2]` and supported in `(-δ, δ)`. -/
private def bumpAt (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  { rIn := δ / 2, rOut := δ, rIn_pos := by positivity, rIn_lt_rOut := by linarith }

/-- The smooth positive function `ω ↦ ω² + b ω`. -/
private def sqPlusBump (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  fun ω => ω ^ 2 + bumpAt δ hδ ω

private theorem sqPlusBump_eq_of_le {δ : ℝ} (hδ : 0 < δ) {ω : ℝ} (hω : δ ≤ |ω|) :
    sqPlusBump δ hδ ω = ω ^ 2 := by
  unfold sqPlusBump
  have h : bumpAt δ hδ ω = 0 := (bumpAt δ hδ).zero_of_le_dist (by
    change δ ≤ dist ω 0
    rwa [Real.dist_eq, sub_zero])
  rw [h, add_zero]

private theorem le_sqPlusBump {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) :
    min 1 (δ ^ 2 / 4) ≤ sqPlusBump δ hδ ω := by
  unfold sqPlusBump
  by_cases hω : |ω| ≤ δ / 2
  · have h : bumpAt δ hδ ω = 1 := (bumpAt δ hδ).one_of_mem_closedBall (by
      change ω ∈ Metric.closedBall (0 : ℝ) (δ / 2)
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero])
    rw [h]
    exact (min_le_left _ _).trans (by nlinarith [sq_nonneg ω])
  · rw [not_le] at hω
    have h1 : δ ^ 2 / 4 ≤ ω ^ 2 := by
      rw [← sq_abs ω]
      nlinarith [abs_nonneg ω]
    have h2 : 0 ≤ bumpAt δ hδ ω := (bumpAt δ hδ).nonneg' ω
    exact (min_le_right _ _).trans (by linarith)

private theorem hasTemperateGrowth_sqPlusBump {δ : ℝ} (hδ : 0 < δ) :
    Function.HasTemperateGrowth (sqPlusBump δ hδ) := by
  unfold sqPlusBump
  exact (Function.HasTemperateGrowth.id'.pow 2).add
    ((bumpAt δ hδ).hasCompactSupport.hasTemperateGrowth (bumpAt δ hδ).contDiff)

private theorem hasTemperateGrowth_inv_sqPlusBump {δ : ℝ} (hδ : 0 < δ) :
    Function.HasTemperateGrowth (fun ω => (sqPlusBump δ hδ ω)⁻¹) :=
  (hasTemperateGrowth_sqPlusBump hδ).inv_of_le (c := min 1 (δ ^ 2 / 4)) (by positivity)
    (le_sqPlusBump hδ)

/-- A Schwartz function supported away from the origin, divided by `ω²`, is Schwartz. -/
theorem exists_eq_inv_sq_mul (φ : SchwartzMap ℝ ℂ) (hφ : (0 : ℝ) ∉ tsupport φ) :
    ∃ ψ : SchwartzMap ℝ ℂ, ∀ ω : ℝ, ψ ω = ((ω : ℂ) ^ 2)⁻¹ * φ ω := by
  obtain ⟨δ, hδ, hδφ⟩ := exists_pos_le_abs_of_zero_notMem_tsupport hφ
  have hg : Function.HasTemperateGrowth fun ω : ℝ => (((sqPlusBump δ hδ ω)⁻¹ : ℝ) : ℂ) :=
    Function.Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_inv_sqPlusBump hδ)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun ω : ℝ => (((sqPlusBump δ hδ ω)⁻¹ : ℝ) : ℂ)) φ,
    fun ω => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  by_cases hω : ω ∈ tsupport φ
  · rw [sqPlusBump_eq_of_le hδ (hδφ ω hω)]
    push_cast
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hω, mul_zero, mul_zero]

/-- A Schwartz function supported away from the origin, multiplied by `|ω| ^ r`, is Schwartz. -/
theorem exists_eq_abs_rpow_mul (φ : SchwartzMap ℝ ℂ) (hφ : (0 : ℝ) ∉ tsupport φ) (r : ℝ) :
    ∃ ψ : SchwartzMap ℝ ℂ, ∀ ω : ℝ, ψ ω = ((|ω| ^ r : ℝ) : ℂ) * φ ω := by
  obtain ⟨δ, hδ, hδφ⟩ := exists_pos_le_abs_of_zero_notMem_tsupport hφ
  -- the smooth multiplier `(1 + ω²)^(r/2) (1 + (ω / (ω² + b))²)^(-r/2)`, equal to `|ω|^r` on
  -- the support of `φ`
  set u : ℝ → ℝ := fun ω => ω * (sqPlusBump δ hδ ω)⁻¹ with hu
  set g : ℝ → ℝ := fun ω => (1 + ‖ω‖ ^ 2) ^ (r / 2) * (1 + ‖u ω‖ ^ 2) ^ (-r / 2) with hg_def
  have hu_temp : Function.HasTemperateGrowth u :=
    Function.HasTemperateGrowth.id'.mul (hasTemperateGrowth_inv_sqPlusBump hδ)
  have hg : Function.HasTemperateGrowth g := by
    apply Function.HasTemperateGrowth.mul
    · exact Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (r / 2)
    · exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-r / 2)).comp hu_temp
  have hgC : Function.HasTemperateGrowth fun ω : ℝ => ((g ω : ℝ) : ℂ) :=
    Function.Complex.hasTemperateGrowth_ofReal.comp hg
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun ω : ℝ => ((g ω : ℝ) : ℂ)) φ, fun ω => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hgC, smul_eq_mul]
  by_cases hω : ω ∈ tsupport φ
  · congr 2
    have hω0 : ω ≠ 0 := by
      intro h
      have := hδφ ω hω
      rw [h, abs_zero] at this
      linarith
    have hωpos : 0 < ω ^ 2 := by positivity
    simp only [hg_def, hu, sqPlusBump_eq_of_le hδ (hδφ ω hω), Real.norm_eq_abs, sq_abs]
    have h1 : ω * (ω ^ 2)⁻¹ = ω⁻¹ := by field_simp
    rw [h1, inv_pow, neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← Real.div_rpow
      (by positivity) (by positivity)]
    have h2 : (1 + ω ^ 2) / (1 + (ω ^ 2)⁻¹) = ω ^ 2 := by
      field_simp
      ring
    rw [h2, ← sq_abs ω, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg ω)]
    congr 1
    push_cast
    ring
  · rw [image_eq_zero_of_notMem_tsupport hω, mul_zero, mul_zero]

end SchwartzMap

end
