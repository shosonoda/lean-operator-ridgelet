import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian integrals against an even homogeneous weight

Mathlib's `integrable_rpow_mul_exp_neg_mul_sq` uses the real power `x ^ c`, which for `x < 0` is
not the even weight `|x| ^ c` of a homogeneous measure.  This module records the even version,
`|ω| ^ c e^{-bω²}`, in the range `c > -1` where it is
integrable at the origin.
-/

open MeasureTheory Set Real

namespace Real

/-- The even Gaussian weight `|ω|^c e^{-bω²}` is integrable exactly in the range `c > -1`
that makes it integrable at the origin. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_sq {b c : ℝ} (hb : 0 < b) (hc : -1 < c) :
    Integrable fun ω : ℝ => |ω| ^ c * Real.exp (-b * ω ^ 2) := by
  have hIoi : IntegrableOn (fun ω : ℝ => |ω| ^ c * Real.exp (-b * ω ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hc).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    rw [abs_of_pos hx]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hIoi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero, abs_neg] using hIoi

end Real
