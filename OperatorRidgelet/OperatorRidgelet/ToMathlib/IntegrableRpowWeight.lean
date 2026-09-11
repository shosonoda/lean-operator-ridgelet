import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set Metric

/-- A bounded integrable function remains integrable after multiplication by a locally integrable
negative power of the norm. -/
theorem MeasureTheory.Integrable.norm_rpow_smul_of_bounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} (hf : Integrable f μ)
    {C β : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hβ : -(Module.finrank ℝ E : ℝ) < β)
    (hβ0 : β < 0) : Integrable (fun x => ‖x‖ ^ β • f x) μ := by
  have hdim : 1 ≤ Module.finrank ℝ E := by
    have : (0 : ℝ) < Module.finrank ℝ E := by linarith
    exact_mod_cast this
  have hm : AEStronglyMeasurable (fun x => ‖x‖ ^ β • f x) μ :=
    (measurable_norm.pow_const β).aestronglyMeasurable.smul hf.aestronglyMeasurable
  have hball : IntegrableOn (fun x => ‖x‖ ^ β • f x) (ball 0 1) μ := by
    apply integrableOn_ball_of_norm_le_rpow hdim (α := -β) (C := C) (by linarith) _ hm
    filter_upwards with x
    rw [neg_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _)]
    nlinarith [Real.rpow_nonneg (norm_nonneg x) β, hbound x]
  have hcompl : IntegrableOn (fun x => ‖x‖ ^ β • f x) (ball 0 1)ᶜ μ := by
    apply hf.norm.integrableOn.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hx1 hβ0.le)
  rw [← integrableOn_univ, ← union_compl_self (ball (0 : E) 1), integrableOn_union]
  exact ⟨hball, hcompl⟩
