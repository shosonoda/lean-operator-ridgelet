import OperatorRidgelet.Sobolev.Dilation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz rays

A Schwartz coefficient lies in every Sobolev class of `lem:sobolev-tools`: the weight `⟨t⟩^s`
has temperate growth, so `⟨·⟩^s γ` is again a Schwartz function, hence square integrable.  This
is what makes the concrete rays of Appendix I available at every order `s`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

/-- The Sobolev weight has temperate growth. -/
theorem hasTemperateGrowth_bracket_rpow (s : ℝ) :
    Function.HasTemperateGrowth fun t : ℝ => ((bracket t ^ s : ℝ) : ℂ) := by
  have hr : Function.HasTemperateGrowth fun t : ℝ => ((1 + ‖t‖ ^ 2) ^ (s / 2) : ℝ) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 2)
  have heq : (fun t : ℝ => ((bracket t ^ s : ℝ) : ℂ)) =
      fun t : ℝ => (((1 + ‖t‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by
    funext t
    congr 1
    rw [Real.norm_eq_abs, sq_abs, ← bracket_rpow_two_mul t (s / 2)]
    congr 1
    ring
  rw [heq]
  exact Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal hr

/-- A Schwartz coefficient lies in every Sobolev class. -/
theorem memRaySobolev_schwartz (s : ℝ) (φ : SchwartzMap ℝ ℂ) : MemRaySobolev s ⇑φ := by
  have hg := hasTemperateGrowth_bracket_rpow s
  have hmem := (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => ((bracket t ^ s : ℝ) : ℂ)) φ).memLp 2
    (volume : Measure ℝ)
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 hmem
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [Complex.real_smul, smul_eq_mul]

end OperatorRidgelet
