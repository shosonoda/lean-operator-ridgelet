import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrability of `u^a (1+u)^c` on the positive half-line

The Beta-type weight `u ↦ u^a (1+u)^c` is integrable on `(0,∞)` exactly when it is integrable at
both ends, `-1 < a` at the origin and `a + c < -1` at infinity.  Only the sufficiency is proved
here, which is all that the subordination formula `|ω|^{-α} = Γ(α/2)^{-1} ∫ u^{α/2-1}
e^{-uω²} du` of Appendix I needs.
-/

open MeasureTheory Set Real

namespace Real

/-- The Beta-type weight `u^a (1+u)^c` is integrable on `(0,∞)` when `-1 < a` and `a + c < -1`. -/
theorem integrableOn_rpow_mul_one_add_rpow {a c : ℝ} (ha : -1 < a) (hac : a + c < -1) :
    IntegrableOn (fun u : ℝ => u ^ a * (1 + u) ^ c) (Ioi 0) := by
  have hc : c < 0 := by linarith
  have hmeas : ∀ S : Set ℝ, AEStronglyMeasurable (fun u : ℝ => u ^ a * (1 + u) ^ c)
      (volume.restrict S) := fun _ => Measurable.aestronglyMeasurable (by fun_prop)
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro hu
      rcases lt_or_ge u 1 with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr h
    · rintro (⟨hu, -⟩ | hu)
      · exact hu
      · linarith
  rw [IntegrableOn, hsplit, ← IntegrableOn, integrableOn_union]
  constructor
  · -- near the origin the second factor is bounded by one
    refine Integrable.mono'
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (t := 1) one_pos).2 ha) (hmeas _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have h1 : (1 + u) ^ c ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hc.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    calc u ^ a * (1 + u) ^ c ≤ u ^ a * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hu0.le _)
      _ = u ^ a := mul_one _
  · -- at infinity the second factor is dominated by `u ^ c`
    have hIoi : IntegrableOn (fun u : ℝ => u ^ (a + c)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hac one_pos
    have hIci : IntegrableOn (fun u : ℝ => u ^ (a + c)) (Ici 1) := by
      rwa [← Ioi_union_left, integrableOn_union, and_iff_left (by simp)]
    refine Integrable.mono' hIci (hmeas _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
    have h1 : (1 + u) ^ c ≤ u ^ c := Real.rpow_le_rpow_of_nonpos hu0 (by linarith) hc.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_add hu0]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hu0.le _)

end Real
