import OperatorRidgelet.Reconstruction.DecoderDefs
import OperatorRidgelet.Reconstruction.Representation

/-! # Reconstruction stability in the completed spectral norm -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The Hilbert adjoint agrees with the inverse Riesz map applied to weak synthesis. -/
theorem adjoint_ridgeletExtension_eq_rieszInv_synthesis (μ ν : Measure H)
    [IsFiniteMeasure μ] (ρ : ℝ → ℝ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    (ridgeletExtension μ ν ρ).adjoint γ = rieszInv μ ν (synthesis μ ν ρ γ) := by
  apply (InnerProductSpace.toDual ℂ (spectralRange μ ν)).injective
  ext f
  simp only [rieszInv, LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_apply_apply,
    antiDualConj_apply, synthesis_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, inner_conj_symm]

/-- The decoder is exactly C⁻¹ T⁻¹ S, since the frame operator is the Riesz map. -/
theorem coefficientDecoder_apply (α : ℝ) (μ ν : Measure H) [IsFiniteMeasure μ]
    (ρ : ℝ → ℝ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    coefficientDecoder α μ ν ρ γ =
      ((admissibilityConst α ρ : ℂ)⁻¹) • rieszInv μ ν (synthesis μ ν ρ γ) := by
  simp only [coefficientDecoder, _root_.smul_apply,
    adjoint_ridgeletExtension_eq_rieszInv_synthesis]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SigmaFinite ν]
  {α : ℝ} (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)

include hν hρ

/-- The decoder is a left inverse of the extended transform on the completed spectral space. -/
theorem coefficientDecoder_ridgeletExtension (f : spectralRange μ ν) :
    coefficientDecoder α μ ν ρ (ridgeletExtension μ ν ρ f) = f := by
  rw [coefficientDecoder_apply, synthesis_ridgeletExtension hν hρ]
  change ((admissibilityConst α ρ : ℂ)⁻¹) •
    rieszInv μ ν ((admissibilityConst α ρ : ℂ) • rieszMap μ ν f) = f
  rw [← map_smul, rieszInv_rieszMap, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast hρ.pos.ne'

/-- The decoder has operator norm at most the reciprocal square root of admissibility. -/
theorem norm_coefficientDecoder_le :
    ‖coefficientDecoder α μ ν ρ‖ ≤ (Real.sqrt (admissibilityConst α ρ))⁻¹ := by
  have hR : ‖ridgeletExtension μ ν ρ‖ ≤ Real.sqrt (admissibilityConst α ρ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    rw [ridgeletExtension_eq hν hρ, norm_ridgeletExtensionCLM hν hρ]
  have hC : admissibilityConst α ρ ≠ 0 := hρ.pos.ne'
  have hsq := Real.sq_sqrt hρ.pos.le
  have hs : Real.sqrt (admissibilityConst α ρ) ≠ 0 := (Real.sqrt_pos.mpr hρ.pos).ne'
  have hc : (admissibilityConst α ρ)⁻¹ * Real.sqrt (admissibilityConst α ρ) =
      (Real.sqrt (admissibilityConst α ρ))⁻¹ := by
    apply (mul_right_cancel₀ hs)
    field_simp
    nlinarith [hsq]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro γ
  rw [coefficientDecoder, _root_.smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hρ.pos.le]
  calc (admissibilityConst α ρ)⁻¹ * ‖(ridgeletExtension μ ν ρ).adjoint γ‖
      ≤ (admissibilityConst α ρ)⁻¹ *
          (Real.sqrt (admissibilityConst α ρ) * ‖γ‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hρ.pos.le)
        exact ((ridgeletExtension μ ν ρ).adjoint.le_opNorm γ).trans
          (mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.adjoint.norm_map _).le.trans hR) (norm_nonneg γ))
    _ = (Real.sqrt (admissibilityConst α ρ))⁻¹ * ‖γ‖ := by rw [← mul_assoc, hc]

/-- A perturbation of size δ in coefficient norm gives error at most δ divided by √C. -/
theorem norm_coefficientDecoder_sub_le (f : spectralRange μ ν)
    (γ : Lp ℂ 2 (parameterMeasure ν)) {δ : ℝ}
    (hδ : ‖γ - ridgeletExtension μ ν ρ f‖ ≤ δ) :
    ‖coefficientDecoder α μ ν ρ γ - f‖ ≤ δ / Real.sqrt (admissibilityConst α ρ) := by
  rw [← coefficientDecoder_ridgeletExtension hν hρ f, ← map_sub]
  calc ‖coefficientDecoder α μ ν ρ (γ - ridgeletExtension μ ν ρ f)‖
      ≤ ‖coefficientDecoder α μ ν ρ‖ * ‖γ - ridgeletExtension μ ν ρ f‖ :=
        (coefficientDecoder α μ ν ρ).le_opNorm _
    _ ≤ (Real.sqrt (admissibilityConst α ρ))⁻¹ * δ :=
      mul_le_mul (norm_coefficientDecoder_le hν hρ) hδ (norm_nonneg _) (by positivity)
    _ = δ / Real.sqrt (admissibilityConst α ρ) := by rw [div_eq_mul_inv, mul_comm]

end OperatorRidgelet
