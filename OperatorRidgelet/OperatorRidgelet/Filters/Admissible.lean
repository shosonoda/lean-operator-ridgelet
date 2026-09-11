import OperatorRidgelet.Transform.Basic

/-! # Admissibility of band-pass filters -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal

/-! ### Band-pass filters are admissible -/

/-- A band-pass filter is `α`-admissible for every `α`. -/
theorem IsBandPass.isAdmissible {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (α : ℝ) :
    IsAdmissible α ρ := by
  have hcont : Continuous (filterFourier ρ) := hρ.contDiff.continuous
  have hev : filterFourier ρ =ᶠ[𝓝 0] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hρ.zero_notMem_tsupport
  have hg_cont : Continuous fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) := by
    rw [continuous_iff_continuousAt]
    intro ω
    by_cases hω : ω = 0
    · subst hω
      have : (fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)) =ᶠ[𝓝 (0 : ℝ)]
          fun _ => (0 : ℝ) := by
        filter_upwards [hev] with ω hω
        simp [hω]
      exact this.continuousAt
    · exact ((hcont.norm.pow 2).continuousAt).mul
        ((Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.mpr hω))).comp
          continuous_abs.continuousAt)
  have hg_supp : HasCompactSupport fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) :=
    (hρ.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_right
  have hint : Integrable fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) :=
    hg_cont.integrable_of_hasCompactSupport hg_supp
  refine ⟨hint, ?_⟩
  unfold admissibilityConst
  refine mul_pos (inv_pos.mpr (by positivity)) ?_
  rw [integral_pos_iff_support_of_nonneg (fun ω => by positivity) hint]
  have hsub : Function.support (filterFourier ρ) ⊆
      Function.support fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) := by
    intro ω hω
    have hω0 : ω ≠ 0 := fun h => hρ.zero_notMem_tsupport (h ▸ subset_tsupport _ hω)
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hω))
      (Real.rpow_pos_of_pos (abs_pos.mpr hω0) _).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  exact hcont.isOpen_support.measure_pos volume
    (Function.support_nonempty_iff.mpr (filterFourier_ne_zero hρ.ne_zero))

end OperatorRidgelet
