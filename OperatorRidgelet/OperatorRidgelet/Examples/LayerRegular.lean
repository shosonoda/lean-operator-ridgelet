import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.Reconstruction.Basic

/-!
# Ray regularity of the transform of a neural-operator layer

The transform of the scalar observable of a neural-operator layer with Gaussian activation is a
Bochner integral
`𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} m(dy)`
of Gaussian-type densities whose covariances `S_y` obey the two-sided bound
`θ Q ≤ S_y`, `‖S_y‖ ≤ ‖Q‖ (1 + ‖Q‖ ‖A‖_∞²)` uniformly in `y`.  The weight `w_φ` is only
integrable, not bounded, so Lemma `lem:ray-regular-examples`(c) (`IsRegularAlongRays.integral`)
is applied here in the weighted form `IsRegularAlongRays.integral_weighted`, in which the
family is dominated by `W y` with `W ∈ L¹(m)` — the manuscript's device of running the argument
for the finite measure `|w_φ| m` and the family `(w_φ/|w_φ|) G_y`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### The weighted form of Lemma `lem:ray-regular-examples`(c) -/

section Weighted

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- **Lemma `lem:ray-regular-examples`(c), weighted form.**  For a measurable family `G y` of
densities dominated by an integrable weight `W ∈ L¹(m)`, smooth along rays on a common open
neighbourhood `U` of `I`, and with ray-derivative bounds of the product form `h(a) W(y)` whose
`h` is `ν`-integrable against `(1+‖a‖)^{k+2}`, the Bochner integral `ξ ↦ ∫ G y ξ ∂m` is regular
along rays. -/
omit [OpensMeasurableSpace H] in
theorem IsRegularAlongRays.integral_weighted {ν : Measure H} {I : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] {G : Ω → H → ℂ}
    (hGm : Measurable (Function.uncurry G)) {W : Ω → ℝ} (hW : Integrable W m)
    (hW0 : ∀ y, 0 ≤ W y) (hGb : ∀ y ξ, ‖G y ξ‖ ≤ W y) {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ, (∀ a, 0 ≤ h a) ∧
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ ENNReal.ofReal (h a * W y)) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  have hc : (∫⁻ y, ENNReal.ofReal (W y) ∂m) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hW.hasFiniteIntegral.ne (lintegral_mono fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hmeas : ∀ (a : H) (k : ℕ), ∀ t ∈ U,
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m :=
    fun a k t ht => (measurable_iteratedDeriv_of_forall_contDiffOn (f := fun y ω => G y (ω • a))
      (fun t => hGm.comp (measurable_id.prodMk measurable_const))
      (fun y => ⟨U, hU, ht, hsmooth y a⟩) k).aestronglyMeasurable
  have hbound : ∀ (a : H) (k : ℕ), ∃ B : Ω → ℝ, Integrable B m ∧
      ∀ y, ∀ t ∈ U, ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ ≤ B y := by
    intro a k
    obtain ⟨h, hh0, -, hh⟩ := hunif k
    refine ⟨fun y => h a * W y, hW.const_mul _, fun y t ht => ?_⟩
    have h1 : ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ₑ ≤
        ENNReal.ofReal (h a * W y) :=
      (enorm_iteratedDeriv_le_rayDerivBound U (G y) le_rfl a ht).trans (hh y a)
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hh0 a) (hW0 y))).mp h1
  refine ⟨hGm.stronglyMeasurable.integral_prod_left', ⟨∫ y, W y ∂m, fun ξ => ?_⟩,
    fun a => ⟨U, hU, hIU, ?_⟩, ?_⟩
  · exact norm_integral_le_of_norm_le hW (Eventually.of_forall fun y => hGb y ξ)
  · exact contDiffOn_integral_of_dominated hU (fun y => hsmooth y a) (hmeas a) (hbound a)
  · intro k
    obtain ⟨h, hh0, hint, hh⟩ := hunif k
    have hray : ∀ a, rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ≤
        ENNReal.ofReal (h a) * ∫⁻ y, ENNReal.ofReal (W y) ∂m := by
      intro a
      refine iSup_le fun j => iSup₂_le fun ω hω => ?_
      have hωU : ω ∈ U := hIU hω
      change ‖iteratedDeriv (j : ℕ) (fun ω : ℝ => ∫ y, G y (ω • a) ∂m) ω‖ₑ ≤ _
      rw [iteratedDeriv_integral_eq hU (fun y => hsmooth y a) (hmeas a) (hbound a) j hωU,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
      refine ((enorm_iteratedDeriv_le_rayDerivBound U (G y) (Nat.lt_succ_iff.mp j.2) a hωU).trans
        (hh y a)).trans ?_
      rw [ENNReal.ofReal_mul (hh0 a)]
    unfold rayMoment
    calc ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) *
          rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ∂ν
        ≤ ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) *
            (∫⁻ y, ENNReal.ofReal (W y) ∂m) ∂ν :=
          lintegral_mono fun a => by
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (hray a)
      _ = (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) *
            ∫⁻ y, ENNReal.ofReal (W y) ∂m := lintegral_mul_const' _ _ hc
      _ < ⊤ := ENNReal.mul_lt_top hint (lt_top_iff_ne_top.mpr hc)

end Weighted

end OperatorRidgelet
