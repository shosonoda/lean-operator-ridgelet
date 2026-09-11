import OperatorRidgelet.Sampling.Basic
import OperatorRidgelet.ToMathlib.IntegratedSampling

/-! # Second-moment estimates for vector-valued sampling -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Lipschitz ridge atom has quadratic growth controlled by the parameter moment. -/
theorem norm_ridge_sq_le {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (a x : H) (c : ℝ) :
    ‖β (⟪a, x⟫ + c)‖ ^ 2 ≤
      2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ‖x‖ ^ 2) * (‖a‖ ^ 2 + |c| ^ 2)) := by
  have ht : |⟪a, x⟫ + c| ≤ ‖a‖ * ‖x‖ + |c| :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm a x) le_rfl)
  have hb : ‖β (⟪a, x⟫ + c)‖ ≤ ‖β 0‖ + (L : ℝ) * (‖a‖ * ‖x‖ + |c|) := by
    calc
      _ ≤ ‖β (⟪a, x⟫ + c) - β 0‖ + ‖β 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * |⟪a, x⟫ + c| + ‖β 0‖ := by
        gcongr
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hβ.dist_le_mul (⟪a, x⟫ + c) 0
      _ ≤ _ := by nlinarith [L.coe_nonneg]
  have hsq : (‖a‖ * ‖x‖ + |c|) ^ 2 ≤
      (1 + ‖x‖ ^ 2) * (‖a‖ ^ 2 + |c| ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖x‖ * |c|)]
  have hb' := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hb
  have hsq' := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L : ℝ))
  nlinarith [sq_nonneg (‖β 0‖ - (L : ℝ) * (‖a‖ * ‖x‖ + |c|))]

/-- Integrating a Lipschitz ridge atom in the input and parameter variables gives the
explicit second-moment bound used in the vector-valued sampling rate. -/
theorem integral_integral_norm_ridge_sq_le [MeasurableSpace H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) p)
    (ζ : Measure H) [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) :
    ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂p ≤
      2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * secondMoment p) := by
  have hθ (θ : H × ℝ) :
      ∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ ≤
        2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 *
          (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * (‖θ.1‖ ^ 2 + |θ.2| ^ 2)) := by
    calc
      _ ≤ ∫ x, 2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 *
          (1 + ‖x‖ ^ 2) * (‖θ.1‖ ^ 2 + |θ.2| ^ 2)) ∂ζ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          (((integrable_const _).add
            (((integrable_const _).add hζ).const_mul _ |>.mul_const _)).const_mul _)
          (Eventually.of_forall fun x => norm_ridge_sq_le hβ θ.1 x θ.2)
      _ = _ := by
        rw [integral_const_mul]
        have hi : Integrable (fun x : H => (L : ℝ) ^ 2 *
            (1 + ‖x‖ ^ 2) * (‖θ.1‖ ^ 2 + |θ.2| ^ 2)) ζ :=
          (((integrable_const _).add hζ).const_mul _).mul_const _
        rw [integral_add (integrable_const _) hi, integral_mul_const,
          integral_const_mul, integral_add (integrable_const _) hζ]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  calc
    _ ≤ ∫ θ, 2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 *
        (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * (‖θ.1‖ ^ 2 + |θ.2| ^ 2)) ∂p :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        (((integrable_const _).add (hM.const_mul _)).const_mul _)
        (Eventually.of_forall hθ)
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const _) (hM.const_mul _),
        integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
      rfl

variable [MeasurableSpace H] [BorelSpace H]

/-- Each Lipschitz ridge atom is square-integrable under a finite second parameter moment. -/
theorem memLp_ridge_complex {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) p) (x : H) :
    MemLp (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) 2 p := by
  have hm : AEStronglyMeasurable (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) p :=
    (hβ.continuous.comp
      ((continuous_fst.inner continuous_const).add continuous_snd)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : Integrable (fun θ : H × ℝ =>
      2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * (1 + ‖x‖ ^ 2) * (‖θ.1‖ ^ 2 + |θ.2| ^ 2))) p :=
    ((integrable_const _).add (hM.const_mul _)).const_mul _
  apply hi.mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_ridge_sq_le hβ θ.1 x θ.2

/-- A Lipschitz ridge family is jointly square-integrable under second moments in both
the input and parameter variables. -/
theorem memLp_ridge_complex_prod [SecondCountableTopology H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β)
    (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) p)
    (ζ : Measure H) [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) :
    MemLp (fun z : H × (H × ℝ) => β (⟪z.2.1, z.1⟫ + z.2.2)) 2 (ζ.prod p) := by
  have hm : AEStronglyMeasurable (fun z : H × (H × ℝ) => β (⟪z.2.1, z.1⟫ + z.2.2))
      (ζ.prod p) := (hβ.continuous.comp
        (((continuous_fst.comp continuous_snd).inner continuous_fst).add
          (continuous_snd.comp continuous_snd))).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : Integrable (fun z : H × (H × ℝ) =>
      2 * (‖β 0‖ ^ 2 + (L : ℝ) ^ 2 * ((1 + ‖z.1‖ ^ 2) *
        (‖z.2.1‖ ^ 2 + |z.2.2| ^ 2)))) (ζ.prod p) :=
    ((integrable_const _).add ((((integrable_const _).add hζ).mul_prod hM).const_mul _)).const_mul _
  apply hi.mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_assoc, Pi.pow_apply] using norm_ridge_sq_le hβ z.2.1 z.1 z.2.2

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Multiplication by a measurable unit phase preserves square-integrability. -/
theorem memLp_smul_unit_phase {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    {f : Ω → ℂ} (hf : MemLp f 2 p) {h : Ω → Y} (hh : AEStronglyMeasurable h p)
    (hu : ∀ᵐ θ ∂p, ‖h θ‖ = 1) : MemLp (fun θ => f θ • h θ) 2 p := by
  apply hf.of_le (hf.1.smul hh)
  filter_upwards [hu] with θ hθ
  change ‖f θ • h θ‖ ≤ ‖f θ‖
  simp only [norm_smul, hθ, mul_one, le_refl]

/-- The integrated mean-square error of the polar sampled network. -/
theorem integral_polarSampledNetwork_sq_le [SecondCountableTopology H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ))
    (ζ : Measure H) [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ)
    {N : ℕ} (hN : 0 < N) :
    ∫ θ, (∫ x, ‖polarSampledNetwork β Γ θ x - integralNetwork β Γ x‖ ^ 2 ∂ζ)
        ∂sampleLaw N (polarLaw Γ) ≤
      polarWeight Γ ^ 2 / N * ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ := by
  by_cases h0 : totalVariation Γ = 0
  · simp [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0]
  letI := isProbabilityMeasure_polarLaw Γ h0
  letI := InnerProductSpace.rclikeToReal ℂ Y
  let p := polarLaw Γ
  let Φ : H → (H × ℝ) → Y := fun x θ => β (⟪θ.1, x⟫ + θ.2) • polarDensity Γ θ
  have hh := aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hu := ae_polarLaw_norm_polarDensity_eq_one Γ
  have hs : ∀ x, MemLp (Φ x) 2 p := fun x =>
    memLp_smul_unit_phase (memLp_ridge_complex hβ p hM x) hh hu
  have hj : MemLp (Function.uncurry Φ) 2 (ζ.prod p) := by
    apply memLp_smul_unit_phase (memLp_ridge_complex_prod hβ p hM ζ hζ)
    · exact hh.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    · exact Measure.quasiMeasurePreserving_snd.ae hu
  have h := integral_integral_norm_sq_sampleMean_le p ζ hj hs (polarWeight Γ) hN
  have he (θ : Fin N → H × ℝ) (x : H) :
      polarSampledNetwork β Γ θ x - integralNetwork β Γ x =
        (polarWeight Γ / N : ℝ) • ∑ j, Φ x (θ j) - polarWeight Γ • ∫ t, Φ x t ∂p := by
    rw [integralNetwork_eq_integral_polarLaw β Γ h0
      ((memLp_ridge_complex hβ p hM x).integrable (by norm_num))]
    congr 1
    unfold polarSampledNetwork sampledNetwork finiteNetwork
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change β (⟪(θ j).1, x⟫ + (θ j).2) •
      ((↑(polarWeight Γ / N) : ℂ) • polarDensity Γ (θ j)) =
      (polarWeight Γ / N : ℝ) • (β (⟪(θ j).1, x⟫ + (θ j).2) • polarDensity Γ (θ j))
    rw [Complex.coe_smul]
    exact smul_comm _ _ _
  simp_rw [he]
  apply h.trans_eq
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hu] with θ hθ
  congr 1
  ext x
  simp [Φ, norm_smul, hθ]

end OperatorRidgelet
