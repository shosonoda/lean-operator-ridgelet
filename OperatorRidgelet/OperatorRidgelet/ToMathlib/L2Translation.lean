import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OperatorRidgelet.ToMathlib.L2Glue

/-!
# Continuity of translation in `L²(ℝ)`

`tendsto_integral_norm_translate_sub_sq`: for a square-integrable `F : ℝ → Y`,
`∫ ‖F(t + v) − F(t)‖² dt → 0` as `v → 0`.  This is the strong continuity of the translation
action on `L²`, which Mathlib provides as the continuity of the action of `ℝᵈᵃᵃ` on
`MeasureTheory.Lp`, transported to the Bochner integral of the squared norm.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Strong continuity of translation in `L²(ℝ)`**: for a square-integrable `F`, the integral
`∫ ‖F(t + v) − F(t)‖² dt` tends to zero as `v → 0`. -/
theorem tendsto_integral_norm_translate_sub_sq {Y : Type*} [NormedAddCommGroup Y]
    {F : ℝ → Y} (hF : MemLp F 2 (volume : Measure ℝ)) :
    Tendsto (fun v : ℝ => ∫ t : ℝ, ‖F (t + v) - F t‖ ^ 2) (𝓝 0) (𝓝 0) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  set u : Lp Y 2 (volume : Measure ℝ) := hF.toLp F with hu
  have hact : Continuous fun v : ℝ => (DomAddAct.mk v : ℝᵈᵃᵃ) +ᵥ u :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have h0 : (DomAddAct.mk (0 : ℝ) : ℝᵈᵃᵃ) +ᵥ u = u := by
    simp
  have hsub : Continuous fun v : ℝ => ((DomAddAct.mk v : ℝᵈᵃᵃ) +ᵥ u) - u :=
    hact.sub continuous_const
  have htend := hsub.tendsto 0
  rw [h0, sub_self] at htend
  have hnorm : Tendsto (fun v : ℝ => ‖((DomAddAct.mk v : ℝᵈᵃᵃ) +ᵥ u) - u‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (htend.norm).pow 2
  refine hnorm.congr fun v => ?_
  have hae1 : (fun t : ℝ => ((DomAddAct.mk v : ℝᵈᵃᵃ) +ᵥ u) t) =ᵐ[volume]
      fun t : ℝ => F (v + t) := by
    have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk v) u
    have h2 : (fun t : ℝ => (u : ℝ → Y) (v + t)) =ᵐ[volume] fun t : ℝ => F (v + t) :=
      (measurePreserving_add_left volume v).quasiMeasurePreserving.ae hF.coeFn_toLp
    exact h1.trans h2
  rw [Lp.norm_sq_eq_integral_norm_sq]
  refine (integral_congr_ae ?_).symm
  filter_upwards [Lp.coeFn_sub ((DomAddAct.mk v : ℝᵈᵃᵃ) +ᵥ u) u, hae1, hF.coeFn_toLp]
    with t h3 h1 h2
  rw [h3, Pi.sub_apply, h1, h2, add_comm v t]
