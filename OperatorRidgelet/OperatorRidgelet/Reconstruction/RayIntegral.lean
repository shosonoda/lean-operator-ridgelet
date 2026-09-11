import OperatorRidgelet.Reconstruction.Basic
import OperatorRidgelet.ToMathlib.ContDiffOnParametricIntegral

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- A finite Bochner integral preserves ray regularity under finite derivative bounds on a
common open neighbourhood of the frequency window. -/
theorem isRegularAlongRays_integral (ν : Measure H) (I U : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] (G : Ω → H → ℂ)
    (hGm : Measurable (Function.uncurry G)) (hGb : ∃ M : ℝ, ∀ y ξ, ‖G y ξ‖ ≤ M)
    (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ≥0,
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * (h a : ℝ≥0∞) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ h a) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  have hmeas : ∀ a k t, t ∈ U →
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m := by
    intro a k t ht
    exact (measurable_iteratedDeriv_of_forall_contDiffOn
      (fun ω => hGm.comp (measurable_id.prodMk measurable_const))
      (fun y => ⟨U, hU, ht, hsmooth y a⟩) k).aestronglyMeasurable
  have hbound : ∀ a k, ∃ B : Ω → ℝ, Integrable B m ∧
      ∀ y, ∀ t ∈ U, ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ ≤ B y := by
    intro a k
    obtain ⟨h, _, hh⟩ := hunif k
    refine ⟨fun _ => h a, integrable_const _, fun y t ht => ?_⟩
    have he₀ : ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ₑ ≤
        rayDerivBound U (G y) k a := by
      exact le_iSup_of_le (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
        (le_iSup₂_of_le t ht le_rfl)
    have he := he₀.trans (hh y a)
    exact_mod_cast he
  have hderiv : ∀ a k t, t ∈ U →
      iteratedDeriv k (fun ω : ℝ => ∫ y, G y (ω • a) ∂m) t =
        ∫ y, iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t ∂m := by
    intro a k t ht
    exact iteratedDeriv_integral_eq hU (fun y => hsmooth y a) (hmeas a) (hbound a) k ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hGm.stronglyMeasurable.integral_prod_left
  · obtain ⟨M, hM⟩ := hGb
    refine ⟨m.real Set.univ * M, fun ξ => ?_⟩
    exact (norm_integral_le_integral_norm _).trans
      ((integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
        (integrable_const M) (Eventually.of_forall fun y => hM y ξ)).trans_eq
          (by simp [mul_comm]))
  · intro a
    exact ⟨U, hU, hIU, contDiffOn_integral_of_dominated hU
      (fun y => hsmooth y a) (hmeas a) (hbound a)⟩
  · intro k
    obtain ⟨h, hhfin, hh⟩ := hunif k
    have hray : ∀ a, rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ≤
        m Set.univ * (h a : ℝ≥0∞) := by
      intro a
      refine iSup_le fun j => iSup_le fun t => iSup_le fun ht => ?_
      rw [hderiv a j t (hIU ht)]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      calc
        _ ≤ ∫⁻ y, (h a : ℝ≥0∞) ∂m := lintegral_mono fun y => by
          apply le_trans (b := rayDerivBound U (G y) k a) _ (hh y a)
          exact le_iSup_of_le j (le_iSup₂_of_le t (hIU ht) le_rfl)
        _ = _ := by simp [mul_comm]
    unfold rayMoment
    refine lt_of_le_of_lt (lintegral_mono fun a => mul_le_mul_left' (hray a) _) ?_
    simp_rw [← mul_assoc, mul_comm _ (m Set.univ), mul_assoc]
    rw [lintegral_const_mul' _ _ (measure_ne_top m Set.univ)]
    exact ENNReal.mul_lt_top (measure_lt_top m Set.univ) hhfin

end OperatorRidgelet
