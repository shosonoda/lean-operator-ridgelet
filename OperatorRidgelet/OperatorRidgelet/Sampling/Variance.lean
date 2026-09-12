import OperatorRidgelet.Sampling.VectorRates

/-! # Exact integrated variance of polar sampled networks -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The integrated mean-square error of the polar sampled network. -/
theorem integral_polarSampledNetwork_sq_eq [SecondCountableTopology H] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ))
    (ζ : Measure H) [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ)
    {N : ℕ} (hN : 0 < N) :
    ∫ θ, (∫ x, ‖polarSampledNetwork β Γ θ x - integralNetwork β Γ x‖ ^ 2 ∂ζ)
        ∂sampleLaw N (polarLaw Γ) =
      (N : ℝ)⁻¹ * (polarWeight Γ ^ 2 *
        (∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ) -
          ∫ x, ‖integralNetwork β Γ x‖ ^ 2 ∂ζ) := by
  by_cases h0 : totalVariation Γ = 0
  · simp [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0,
      integralNetwork_eq_zero_of_totalVariation_eq_zero β h0]
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
  have h := integral_integral_norm_sq_sampleMean p ζ hj hs (polarWeight Γ) hN
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
  have hmoment :
      (∫ θ, (∫ x, ‖Φ x θ‖ ^ 2 ∂ζ) ∂p) =
        ∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂p := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hu] with θ hθ
    congr 1
    ext x
    simp [Φ, norm_smul, hθ]
  have hmean :
      (∫ x, ‖integralNetwork β Γ x‖ ^ 2 ∂ζ) =
        polarWeight Γ ^ 2 * ∫ x, ‖∫ θ, Φ x θ ∂p‖ ^ 2 ∂ζ := by
    have hemean (x : H) : integralNetwork β Γ x =
        polarWeight Γ • ∫ θ, Φ x θ ∂p := by
      exact integralNetwork_eq_integral_polarLaw β Γ h0
        ((memLp_ridge_complex hβ p hM x).integrable (by norm_num))
    simp_rw [hemean, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_const_mul]
  simp_rw [he]
  refine h.trans ?_
  rw [hmoment, hmean]
  dsimp only [p]
  ring

end OperatorRidgelet
