import Mathlib.Probability.StrongLaw
import Mathlib.Probability.HasLawExists

/-! # Convergence in mean of finite product sample averages -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The expected norm of a centered empirical average tends to zero in a Banach space. -/
theorem tendsto_integral_norm_sampleMean (p : Measure Ω) [IsProbabilityMeasure p]
    {Φ : Ω → E} (hΦ : StronglyMeasurable Φ) (hint : Integrable Φ p) :
    Tendsto (fun N : ℕ => ∫ ω : Fin N → Ω,
      ‖(N : ℝ)⁻¹ • ∑ j, Φ (ω j) - ∫ θ, Φ θ ∂p‖ ∂Measure.pi (fun _ : Fin N => p))
      atTop (𝓝 0) := by
  let μ := p.map Φ
  have hmp : MeasurePreserving Φ p μ := ⟨hΦ.measurable, rfl⟩
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hΦ.measurable.aemeasurable
  obtain ⟨Ω', mΩ', P, X, hXm, hXlaw, hXi, hP⟩ := exists_iid ℕ μ
  letI := mΩ'
  letI := hP
  have hd (i : ℕ) : IdentDistrib (X i) Φ P p :=
    ⟨(hXm i).aemeasurable, hΦ.measurable.aemeasurable, (hXlaw i).map_eq⟩
  have hXint : Integrable (X 0) P := (hd 0).integrable_iff.mpr hint
  have ht := strong_law_Lp (p := 1) le_rfl ENNReal.one_ne_top X
    (memLp_one_iff_integrable.mpr hXint) (fun i j hij => hXi.indepFun hij)
    (fun i => (hd i).trans (hd 0).symm)
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  have he (N : ℕ) :
      (eLpNorm (fun ω => (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, X i ω - ∫ ω, X 0 ω ∂P) 1 P).toReal =
      ∫ ω : Fin N → Ω,
        ‖(N : ℝ)⁻¹ • ∑ j, Φ (ω j) - ∫ θ, Φ θ ∂p‖ ∂Measure.pi (fun _ : Fin N => p) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm]
    · have hfin : HasLaw (fun ω (j : Fin N) => X j ω) (Measure.pi fun _ : Fin N => μ) P :=
        (hXi.precomp Fin.val_injective).hasLaw_pi (fun j => hXlaw j)
      have hpfin := measurePreserving_pi (fun _ : Fin N => p) (fun _ : Fin N => μ)
        (fun _ => hmp)
      let F : (Fin N → E) → ℝ := fun y => ‖(N : ℝ)⁻¹ • ∑ j, y j - ∫ θ, Φ θ ∂p‖
      have hFm : AEStronglyMeasurable F (Measure.pi fun _ : Fin N => μ) :=
        (by fun_prop : Continuous F).aestronglyMeasurable
      calc
        _ = ∫ ω, F (fun j => X j ω) ∂P := by
          apply integral_congr_ae
          exact Eventually.of_forall fun ω => by
            dsimp [F]
            rw [(hd 0).integral_eq]
            exact congrArg (fun z : E => ‖(N : ℝ)⁻¹ • z - ∫ θ, Φ θ ∂p‖)
              (Fin.sum_univ_eq_sum_range (fun i => X i ω) N).symm
        _ = ∫ y, F y ∂Measure.pi (fun _ : Fin N => μ) := hfin.integral_comp hFm
        _ = _ := (hpfin.hasLaw.integral_comp hFm).symm
    · apply AEStronglyMeasurable.sub _ aestronglyMeasurable_const
      have hm : AEStronglyMeasurable (∑ i ∈ Finset.range N, X i) P :=
        Finset.aestronglyMeasurable_sum _ fun i _ => (hXm i).aestronglyMeasurable
      exact (hm.const_smul (N : ℝ)⁻¹).congr
        (Eventually.of_forall fun x => by simp only [Pi.smul_apply, Finset.sum_apply])
  exact htr.congr he

/-- The same convergence theorem for an almost-everywhere strongly measurable atom map. -/
theorem tendsto_integral_norm_sampleMean_ae (p : Measure Ω) [IsProbabilityMeasure p]
    {Φ : Ω → E} (hint : Integrable Φ p) :
    Tendsto (fun N : ℕ => ∫ ω : Fin N → Ω,
      ‖(N : ℝ)⁻¹ • ∑ j, Φ (ω j) - ∫ θ, Φ θ ∂p‖ ∂Measure.pi (fun _ : Fin N => p))
      atTop (𝓝 0) := by
  let Ψ := hint.1.mk Φ
  have he : Φ =ᵐ[p] Ψ := hint.1.ae_eq_mk
  have ht := tendsto_integral_norm_sampleMean p hint.1.stronglyMeasurable_mk (hint.congr he)
  apply ht.congr
  intro N
  apply integral_congr_ae
  filter_upwards [Measure.ae_pi_le_pi (Filter.eventually_pi fun _ : Fin N => he)] with ω hω
  rw [integral_congr_ae he]
  congr 3
  exact Finset.sum_congr rfl fun j _ => (hω j).symm
