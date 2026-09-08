import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The pairing integral against a measure with a density

For a positive measure `μ`, an integrable density `γ : X → F`, and a continuous bilinear pairing
`B : E →L[ℝ] F →L[ℝ] G`, the integral of `f` against the vector measure `μ.withDensityᵥ γ` is
the Bochner integral of `x ↦ B (f x) (γ x)` against `μ`:

`∫ᵛ x, f x ∂[B; μ.withDensityᵥ γ] = ∫ x, B (f x) (γ x) ∂μ`

whenever `f` is integrable against the variation `μ.withDensity ‖γ‖ₑ`.  The proof is the
standard induction on integrable functions (indicators, additivity, closure in `L¹`, and
almost-everywhere congruence).
-/

open scoped ENNReal NNReal
open MeasureTheory Set Filter

namespace MeasureTheory.VectorMeasure

variable {X E F G : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure X} {γ : X → F} {B : E →L[ℝ] F →L[ℝ] G}

/-- `x ↦ B (f x) (γ x)` is a.e.-strongly measurable against `μ` when `f` is a.e.-strongly
measurable against the density measure `μ.withDensity ‖γ‖ₑ`. -/
theorem aestronglyMeasurable_apply_of_withDensity (hγ : AEStronglyMeasurable γ μ) {f : X → E}
    (hf : AEStronglyMeasurable f (μ.withDensity fun x => ‖γ x‖ₑ)) :
    AEStronglyMeasurable (fun x => B (f x) (γ x)) μ := by
  have hγe := hγ.enorm
  obtain ⟨f', hf'm, hff'⟩ := hf
  obtain ⟨γ', hγ'm, hγγ'⟩ := hγ
  refine ⟨fun x => B (f' x) (γ' x), ?_, ?_⟩
  · exact (B.continuous₂.comp_stronglyMeasurable (hf'm.prodMk hγ'm))
  · have h1 := (ae_withDensity_iff' hγe).mp hff'
    filter_upwards [h1, hγγ'] with x hx hγx
    rcases eq_or_ne (γ x) 0 with h0 | h0
    · rw [h0, ← hγx, h0]
      simp
    · rw [hx (by simpa using h0), hγx]

/-- `x ↦ B (f x) (γ x)` is integrable against `μ` when `f` is integrable against the density
measure `μ.withDensity ‖γ‖ₑ`. -/
theorem integrable_apply_of_withDensity (hγ : AEStronglyMeasurable γ μ) {f : X → E}
    (hf : Integrable f (μ.withDensity fun x => ‖γ x‖ₑ)) :
    Integrable (fun x => B (f x) (γ x)) μ := by
  have h1 : Integrable (fun x => (‖γ x‖₊ : ℝ) • f x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul₀ hγ.nnnorm.aemeasurable).mp hf
  refine (h1.norm.const_mul ‖B‖).mono' (aestronglyMeasurable_apply_of_withDensity hγ hf.1)
    (Eventually.of_forall fun x => ?_)
  calc ‖B (f x) (γ x)‖ ≤ ‖B‖ * ‖f x‖ * ‖γ x‖ := B.le_opNorm₂ _ _
    _ = ‖B‖ * ‖(‖γ x‖₊ : ℝ) • f x‖ := by
        rw [norm_smul, coe_nnnorm, Real.norm_eq_abs, abs_norm]
        ring

/-- The `L¹`-norm bound for the Bochner side. -/
theorem norm_integral_apply_le (hγ : AEStronglyMeasurable γ μ) {f : X → E}
    (hf : Integrable f (μ.withDensity fun x => ‖γ x‖ₑ)) :
    ‖∫ x, B (f x) (γ x) ∂μ‖ ≤ ‖B‖ * ∫ x, ‖f x‖ ∂(μ.withDensity fun x => ‖γ x‖ₑ) := by
  have h1 : Integrable (fun x => (‖γ x‖₊ : ℝ) • f x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul₀ hγ.nnnorm.aemeasurable).mp hf
  have h1' : Integrable (fun x => ‖γ x‖ * ‖f x‖) μ := by
    refine h1.norm.congr (Eventually.of_forall fun x => ?_)
    simp [norm_smul]
  have h2 : ∫ x, ‖f x‖ ∂(μ.withDensity fun x => ‖γ x‖ₑ) = ∫ x, ‖γ x‖ * ‖f x‖ ∂μ := by
    refine (integral_withDensity_eq_integral_smul₀ hγ.nnnorm.aemeasurable
      (fun x => ‖f x‖)).trans ?_
    simp [NNReal.smul_def]
  rw [h2, ← _root_.MeasureTheory.integral_const_mul]
  refine (_root_.MeasureTheory.norm_integral_le_integral_norm _).trans
    (_root_.MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) (h1'.const_mul ‖B‖)
    (Eventually.of_forall fun x => ?_))
  calc ‖B (f x) (γ x)‖ ≤ ‖B‖ * ‖f x‖ * ‖γ x‖ := B.le_opNorm₂ _ _
    _ = ‖B‖ * (‖γ x‖ * ‖f x‖) := by ring

variable [CompleteSpace F] [CompleteSpace G]

/-- The pairing integral against `μ.withDensityᵥ γ` is the Bochner integral of
`x ↦ B (f x) (γ x)` against `μ`. -/
theorem integral_withDensityᵥ (hγ : Integrable γ μ) {f : X → E}
    (hf : Integrable f (μ.withDensity fun x => ‖γ x‖ₑ)) :
    ∫ᵛ x, f x ∂[B; μ.withDensityᵥ γ] = ∫ x, B (f x) (γ x) ∂μ := by
  have hvar : (μ.withDensityᵥ γ).variation = μ.withDensity fun x => ‖γ x‖ₑ :=
    Measure.variation_withDensityᵥ hγ
  have hint : ∀ g : X → E, Integrable g (μ.withDensity fun x => ‖γ x‖ₑ) →
      (μ.withDensityᵥ γ).Integrable g := fun g hg => by
    show Integrable g (μ.withDensityᵥ γ).variation
    rw [hvar]
    exact hg
  refine Integrable.induction
    (P := fun g => ∫ᵛ x, g x ∂[B; μ.withDensityᵥ γ] = ∫ x, B (g x) (γ x) ∂μ) ?_ ?_ ?_ ?_ hf
  · intro c s hs hμs
    rw [integral_eq_setToFun, setToFun_indicator_const _ hs (by rw [hvar]; exact hμs.ne)]
    have hR : (fun x => B (s.indicator (fun _ => c) x) (γ x)) =
        s.indicator (fun x => B c (γ x)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hR, _root_.MeasureTheory.integral_indicator hs,
      (B c).integral_comp_comm hγ.integrableOn, ← withDensityᵥ_apply hγ hs]
    rfl
  · intro u v _ hu hv hPu hPv
    have hu' := integrable_apply_of_withDensity (B := B) hγ.aestronglyMeasurable hu
    have hv' := integrable_apply_of_withDensity (B := B) hγ.aestronglyMeasurable hv
    rw [integral_add (hint u hu) (hint v hv), hPu, hPv, ← _root_.MeasureTheory.integral_add hu' hv']
    congr 1
    funext x
    simp
  · have hL : ∀ u v : X →₁[μ.withDensity fun x => ‖γ x‖ₑ] E,
        dist (∫ᵛ x, u x ∂[B; μ.withDensityᵥ γ]) (∫ᵛ x, v x ∂[B; μ.withDensityᵥ γ]) ≤
          ‖B‖₊ * dist u v ∧
        dist (∫ x, B (u x) (γ x) ∂μ) (∫ x, B (v x) (γ x) ∂μ) ≤ ‖B‖₊ * dist u v := by
      intro u v
      have hu := L1.integrable_coeFn u
      have hv := L1.integrable_coeFn v
      have hdist : dist u v = ∫ x, ‖(u : X → E) x - (v : X → E) x‖
          ∂(μ.withDensity fun x => ‖γ x‖ₑ) := by
        rw [dist_eq_norm, L1.norm_eq_integral_norm]
        refine _root_.MeasureTheory.integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub u v] with x hx
        rw [hx, Pi.sub_apply]
      constructor
      · rw [dist_eq_norm, ← integral_sub (hint u hu) (hint v hv), hdist, coe_nnnorm]
        refine (norm_integral_le_integral_norm).trans (le_of_eq ?_)
        rw [hvar]
        rfl
      · rw [dist_eq_norm, ← _root_.MeasureTheory.integral_sub
          (integrable_apply_of_withDensity hγ.aestronglyMeasurable hu)
          (integrable_apply_of_withDensity hγ.aestronglyMeasurable hv), hdist, coe_nnnorm]
        have := norm_integral_apply_le (B := B) hγ.aestronglyMeasurable (hu.sub hv)
        refine le_trans (le_of_eq ?_) this
        congr 1
        refine _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp
    exact isClosed_eq
      (LipschitzWith.continuous (LipschitzWith.of_dist_le_mul fun u v => (hL u v).1))
      (LipschitzWith.continuous (LipschitzWith.of_dist_le_mul fun u v => (hL u v).2))
  · intro u v huv hu hPu
    have huv' : u =ᵐ[(μ.withDensityᵥ γ).variation] v := by
      rw [hvar]
      exact huv
    rw [← integral_congr_ae huv', hPu]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [(ae_withDensity_iff' hγ.aestronglyMeasurable.enorm).mp huv] with x hx
    rcases eq_or_ne (γ x) 0 with h0 | h0
    · simp [h0]
    · rw [hx (by simpa using h0)]

end MeasureTheory.VectorMeasure
