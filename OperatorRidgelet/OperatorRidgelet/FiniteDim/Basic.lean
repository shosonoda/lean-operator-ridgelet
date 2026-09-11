import OperatorRidgelet.FiniteDim.Defs
import Mathlib.Analysis.Fourier.Inversion
import OperatorRidgelet.ToMathlib.IntegrableRpowWeight
import OperatorRidgelet.ToMathlib.WithDensityMap
import OperatorRidgelet.Reconstruction.Representation

noncomputable section

namespace OperatorRidgelet.FiniteDim

open MeasureTheory Complex
open scoped ENNReal RealInnerProductSpace FourierTransform

/-- The angular-frequency Fourier transform as a Schwartz function. -/
def fourierSchwartz {m : ℕ} (g : SchwartzMap (Euclid m) ℂ) : SchwartzMap (Euclid m) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (Euclid m) ((2 * Real.pi)⁻¹) (by positivity)).toContinuousLinearEquiv (𝓕 g)

@[simp]
theorem fourierSchwartz_apply {m : ℕ} (g : SchwartzMap (Euclid m) ℂ) (ξ : Euclid m) :
    fourierSchwartz g ξ = fourier g ξ := by
  rw [fourier, LeanRidgelet.Fourier.angularFourierIntegralInner_eq_mathlib]
  change 𝓕 g ((2 * Real.pi)⁻¹ • ξ) = 𝓕 (g : Euclid m → ℂ) ((2 * Real.pi)⁻¹ • ξ)
  rw [SchwartzMap.fourier_coe]

theorem gaussFourier_densityMeasure {m : ℕ} (p : Euclid m → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hpc : Continuous p) (f : Euclid m → ℂ) :
    gaussFourier (densityMeasure p) f = fourier (fun x => f x * p x) := by
  funext ξ
  unfold gaussFourier densityMeasure fourier LeanRidgelet.Fourier.angularFourierIntegralInner
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hp x), real_smul, character]
  have he : -Complex.I * (⟪x, ξ⟫ : ℂ) = -((⟪x, ξ⟫ : ℂ) * Complex.I) := by ring
  rw [he]
  ring

theorem mixtureConst_pos {m : ℕ} {α : ℝ} (hαm : α < m) : 0 < mixtureConst m α := by
  unfold mixtureConst
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos Real.pi_pos _)) (Real.Gamma_pos_of_pos (by linarith))

instance directionMeasure_sfinite (m : ℕ) (α : ℝ) : SFinite (directionMeasure m α) := by
  unfold directionMeasure
  infer_instance

theorem isHomogeneous_volume (m : ℕ) : IsHomogeneous m (volume : Measure (Euclid m)) := by
  intro ω hω
  rw [Measure.map_addHaar_smul volume hω]
  simp only [finrank_euclideanSpace_fin, abs_inv, abs_pow]
  rw [← Real.rpow_natCast, Real.rpow_neg (abs_nonneg ω)]

theorem isHomogeneous_directionMeasure (m : ℕ) (α : ℝ) :
    IsHomogeneous α (directionMeasure m α) := by
  intro ω hω
  let e : Euclid m ≃ᵐ Euclid m := (Homeomorph.smul (Units.mk0 ω hω)).toMeasurableEquiv
  change ((volume : Measure (Euclid m)).withDensity _).map e = _
  rw [e.map_withDensity _ (by fun_prop)]
  change ((volume : Measure (Euclid m)).map (ω • ·)).withDensity
    (fun x => ENNReal.ofReal (mixtureConst m α * ‖ω⁻¹ • x‖ ^ (α - m))) = _
  rw [Measure.map_addHaar_smul volume hω, withDensity_smul_measure]
  unfold directionMeasure
  rw [← withDensity_smul _ (by fun_prop), ← withDensity_smul _ (by fun_prop)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    finrank_euclideanSpace_fin]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _), abs_inv, abs_inv, abs_pow,
    Real.inv_rpow (abs_nonneg ω), ← Real.rpow_natCast, ← Real.rpow_neg (abs_nonneg ω),
    ← Real.rpow_neg (abs_nonneg ω)]
  have he : |ω| ^ (-(m : ℝ)) * |ω| ^ (-(α - m)) = |ω| ^ (-α) := by
    rw [← Real.rpow_add (abs_pos.mpr hω)]
    congr 1
    ring
  calc
    _ = (|ω| ^ (-(m : ℝ)) * |ω| ^ (-(α - m))) *
        (mixtureConst m α * ‖x‖ ^ (α - m)) := by ring
    _ = _ := by rw [he]

theorem memLp_fourier_directionMeasure {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (g : SchwartzMap (Euclid m) ℂ) : MemLp (fourier g) 2 (directionMeasure m α) := by
  have hfun : fourier g = fun ξ => fourierSchwartz g ξ := by ext ξ; simp
  rw [hfun, memLp_two_iff_integrable_sq_norm (fourierSchwartz g).continuous.aestronglyMeasurable]
  unfold directionMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (mixtureConst_pos hαm).le
    (Real.rpow_nonneg (norm_nonneg _) _)), smul_eq_mul, mul_assoc]
  apply Integrable.const_mul
  have hsq := (memLp_two_iff_integrable_sq_norm
    (fourierSchwartz g).continuous.aestronglyMeasurable).mp
      ((fourierSchwartz g).memLp (μ := volume) 2)
  have hw := hsq.norm_rpow_smul_of_bounded
    (C := (SchwartzMap.seminorm ℝ 0 0 (fourierSchwartz g)) ^ 2) (β := α - m) ?_ ?_ ?_
  · simpa only [smul_eq_mul] using hw
  · intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((fourierSchwartz g).norm_le_seminorm ℝ ξ) 2
  · simp only [finrank_euclideanSpace_fin]
    linarith
  · linarith

theorem integrable_fourier_directionMeasure {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (g : SchwartzMap (Euclid m) ℂ) : Integrable (fourier g) (directionMeasure m α) := by
  unfold directionMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (mixtureConst_pos hαm).le
    (Real.rpow_nonneg (norm_nonneg _) _)), mul_smul]
  refine Integrable.smul (mixtureConst m α) ?_
  have hfun : fourier g = fun ξ => fourierSchwartz g ξ := by ext ξ; simp
  rw [hfun]
  exact ((fourierSchwartz g).integrable).norm_rpow_smul_of_bounded
    ((fourierSchwartz g).norm_le_seminorm ℝ)
    (by simp only [finrank_euclideanSpace_fin]; linarith) (by linarith)

theorem integral_frameRepresentative_mul_conj {m : ℕ} (μ ν : Measure (Euclid m))
    [SFinite μ] [SFinite ν] {g : Euclid m → ℂ} (hg : Integrable (fourier g) ν)
    {h : Euclid m → ℂ} (hh : Integrable h μ) :
    ∫ x, frameRepresentative ν g x * (starRingEnd ℂ) (h x) ∂μ =
      ∫ ξ, fourier g ξ * (starRingEnd ℂ) (gaussFourier μ h ξ) ∂ν := by
  simpa only [frameRepresentative, spectralTarget, smul_eq_mul] using
    integral_spectralTarget_mul_conj μ ν hg hh

theorem frameRepresentative_eq_fracLaplacian {m : ℕ} {α : ℝ} (hαm : α < m)
    (g : Euclid m → ℂ) (x : Euclid m) :
    frameRepresentative (directionMeasure m α) g x =
      frameConst m α * fracLaplacian (-((m - α) / 2)) g x := by
  unfold frameRepresentative directionMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
  · simp_rw [ENNReal.toReal_ofReal (mul_nonneg (mixtureConst_pos hαm).le
      (Real.rpow_nonneg (norm_nonneg _) _)), real_smul, Complex.ofReal_mul]
    have he : 2 * (-(((m : ℝ) - α) / 2)) = α - m := by ring
    simp only [frameConst, fracLaplacian, he, Complex.ofReal_mul, Complex.ofReal_inv]
    simp_rw [← integral_const_mul]
    have hn : (((2 * Real.pi) ^ m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero m (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    apply integral_congr_ae
    filter_upwards with ξ
    field_simp
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem frameRepresentative_volume {m : ℕ} (g : SchwartzMap (Euclid m) ℂ) (x : Euclid m) :
    frameRepresentative volume g x = ((2 * Real.pi) ^ m : ℝ) * g x := by
  unfold frameRepresentative fourier
  simp_rw [LeanRidgelet.Fourier.angularFourierIntegralInner_eq_mathlib]
  change (∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) *
      𝓕 (g : Euclid m → ℂ) ((2 * Real.pi)⁻¹ • ξ)) = _
  have hphase : ∀ ξ : Euclid m,
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * 𝓕 (g : Euclid m → ℂ) ((2 * Real.pi)⁻¹ • ξ) =
      (fun y => Complex.exp (((2 * Real.pi * ⟪y, x⟫ : ℝ) : ℂ) * Complex.I) *
        𝓕 (g : Euclid m → ℂ) y) ((2 * Real.pi)⁻¹ • ξ) := by
    intro ξ
    simp only [real_inner_smul_left]
    congr 2
    rw [real_inner_comm x ξ]
    congr 1
    push_cast
    field_simp
  simp_rw [hphase]
  rw [Measure.integral_comp_inv_smul volume
    (fun y : Euclid m => Complex.exp (((2 * Real.pi * ⟪y, x⟫ : ℝ) : ℂ) * Complex.I) *
      𝓕 (g : Euclid m → ℂ) y) (2 * Real.pi)]
  have hi := g.integrable.fourierInv_fourier_eq (by simpa only [SchwartzMap.fourier_coe] using
    (𝓕 g).integrable) (g.continuous.continuousAt (x := x))
  rw [Real.fourierInv_eq'] at hi
  simp only [smul_eq_mul] at hi
  rw [hi]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg
    (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) m), real_smul]

end OperatorRidgelet.FiniteDim
