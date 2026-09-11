import OperatorRidgelet.FiniteDim.Basic
import OperatorRidgelet.Filters.Admissible
import OperatorRidgelet.ToMathlib.FractionalSchwartz

/-!
# Finite-dimensional distributional reconstruction

The fractional Laplacian of a Schwartz test function is integrable. Its Fourier
multiplier cancels the reciprocal multiplier of the frame representative under
Fubini, with the angular-frequency normalization preserved explicitly.
-/

noncomputable section
namespace OperatorRidgelet.FiniteDim
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace FourierTransform

/-- The fractional Laplacian is the normalized inverse Fourier transform of its multiplier. -/
theorem fracLaplacian_eq_fourierInv {m : ℕ} (β : ℝ) (φ : SchwartzMap (Euclid m) ℂ)
    (x : Euclid m) :
    fracLaplacian (β / 2) φ x = (((2 * Real.pi) ^ m)⁻¹ : ℝ) *
      𝓕⁻ (fun ξ : Euclid m => ((‖ξ‖ ^ β : ℝ) : ℂ) * fourierSchwartz φ ξ)
        ((2 * Real.pi)⁻¹ • x) := by
  rw [fracLaplacian, Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  rw [fourierSchwartz_apply, real_inner_smul_right]
  have hβ : 2 * (β / 2) = β := by ring
  rw [hβ, smul_eq_mul]
  have he : ((2 * Real.pi * ((2 * Real.pi)⁻¹ * ⟪ξ, x⟫) : ℝ) : ℂ) * I =
      (⟪x, ξ⟫ : ℝ) * I := by
    rw [real_inner_comm ξ x]
    push_cast
    field_simp
  rw [he]
  ring

/-- A positive fractional Laplacian of a Schwartz test function is integrable. -/
theorem integrable_fracLaplacian {m : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : SchwartzMap (Euclid m) ℂ) : Integrable (fracLaplacian (β / 2) φ) := by
  have h := ((fourierSchwartz φ).integrable_fourierInv_norm_rpow_mul hβ).comp_smul
    (by positivity : (2 * Real.pi)⁻¹ ≠ 0)
  convert! h.const_mul (((2 * Real.pi) ^ m)⁻¹ : ℂ) using 1
  ext x
  rw [fracLaplacian_eq_fourierInv]
  push_cast
  rfl

/-- The angular Fourier transform of a positive fractional Laplacian is its defining multiplier. -/
theorem fourier_fracLaplacian {m : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : SchwartzMap (Euclid m) ℂ) (ξ : Euclid m) :
    fourier (fracLaplacian (β / 2) φ) ξ = ((‖ξ‖ ^ β : ℝ) : ℂ) * fourier φ ξ := by
  let B : Euclid m → ℂ := fun ξ => ((‖ξ‖ ^ β : ℝ) : ℂ) * fourierSchwartz φ ξ
  have hB : Integrable B := (fourierSchwartz φ).integrable_norm_rpow_mul hβ.le
  have hBF : Integrable (𝓕 B) := (fourierSchwartz φ).integrable_fourier_norm_rpow_mul hβ
  have hβ0 := hβ.le
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hnorm : fracLaplacian (β / 2) φ =
      (((2 * Real.pi) ^ m)⁻¹ : ℂ) • (fun x => 𝓕⁻ B ((2 * Real.pi)⁻¹ • x)) := by
    funext x
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat] using fracLaplacian_eq_fourierInv β φ x
  rw [fourier, LeanRidgelet.Fourier.angularFourierIntegralInner_eq_mathlib, hnorm]
  have hs := VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (innerₗ (Euclid m)) (fun x => 𝓕⁻ B ((2 * Real.pi)⁻¹ • x))
    (((2 * Real.pi) ^ m)⁻¹ : ℂ)
  rw [hs, Pi.smul_apply]
  change (((2 * Real.pi) ^ m)⁻¹ : ℂ) •
    𝓕 (fun x => 𝓕⁻ B ((2 * Real.pi)⁻¹ • x)) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [Real.fourier_comp_smul _ (by positivity)]
  rw [inv_inv, smul_inv_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    hB.fourier_fourierInv_eq hBF hBc.continuousAt]
  simp only [B, fourierSchwartz_apply, finrank_euclideanSpace_fin, smul_eq_mul,
    Complex.real_smul, inv_pow, inv_inv]
  push_cast
  field_simp

/-- Fubini pairs the frame representative with a reflected angular Fourier transform. -/
theorem integral_frameRepresentative_mul {m : ℕ} (ν : Measure (Euclid m)) [SFinite ν]
    {g h : Euclid m → ℂ} (hg : Integrable (fourier g) ν) (hh : Integrable h) :
    (∫ x, frameRepresentative ν g x * h x) =
      ∫ ξ, fourier g ξ * fourier h (-ξ) ∂ν := by
  have hi : Integrable (fun z : Euclid m × Euclid m =>
      h z.1 * fourier g z.2 * exp ((⟪z.1, z.2⟫ : ℝ) * I)) (volume.prod ν) := by
    refine (hh.mul_prod hg).mul_unimodular ?_ (Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : Euclid m × Euclid m =>
        exp ((⟪z.1, z.2⟫ : ℝ) * I)).aestronglyMeasurable
    · exact (Complex.norm_exp_ofReal_mul_I _).le
  have hleft (x : Euclid m) : frameRepresentative ν g x * h x =
      ∫ ξ, h x * fourier g ξ * exp ((⟪x, ξ⟫ : ℝ) * I) ∂ν := by
    rw [frameRepresentative, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    ring
  simp_rw [hleft]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with ξ
  change _ = fourier g ξ * ∫ x : Euclid m, exp (-I * ((⟪x, -ξ⟫ : ℝ) : ℂ)) * h x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_right, Complex.ofReal_neg]
  have he : -I * -((⟪x, ξ⟫ : ℝ) : ℂ) = (⟪x, ξ⟫ : ℝ) * I := by ring
  rw [he]
  ring

/-- The bilinear Schwartz Fourier pairing in the angular-frequency normalization. -/
theorem integral_fourier_mul_neg {m : ℕ} (g φ : SchwartzMap (Euclid m) ℂ) :
    (∫ ξ, fourier g ξ * fourier φ (-ξ)) = ((2 * Real.pi) ^ m : ℝ) * ∫ x, g x * φ x := by
  have hg : Integrable (fourier g) := by
    exact (fourierSchwartz g).integrable.congr (Eventually.of_forall (fourierSchwartz_apply g))
  rw [← integral_frameRepresentative_mul volume hg φ.integrable]
  simp_rw [frameRepresentative_volume, mul_assoc]
  rw [integral_const_mul]

/-- The positive fractional Laplacian cancels the reciprocal frame multiplier in the distributional pairing. -/
theorem integral_frameRepresentative_fracLaplacian {m : ℕ} {α : ℝ}
    (hα : 0 < α) (hαm : α < m) (g φ : SchwartzMap (Euclid m) ℂ) :
    (∫ x, frameRepresentative (directionMeasure m α) g x * fracLaplacian ((m - α) / 2) φ x) =
      (frameConst m α : ℂ) * ∫ x, g x * φ x := by
  have hβ : 0 < (m : ℝ) - α := sub_pos.mpr hαm
  have hm : 0 < m := by exact_mod_cast lt_trans hα hαm
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rw [integral_frameRepresentative_mul (directionMeasure m α)
    (integrable_fourier_directionMeasure hα hαm g) (integrable_fracLaplacian hβ φ)]
  simp_rw [fourier_fracLaplacian hβ, norm_neg]
  rw [directionMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (mixtureConst_pos hαm).le
    (Real.rpow_nonneg (norm_nonneg _) _)), Complex.real_smul, Complex.ofReal_mul]
  have heq : (∫ ξ : Euclid m,
      (mixtureConst m α : ℂ) * ((‖ξ‖ ^ (α - m) : ℝ) : ℂ) *
        (fourier g ξ * (((‖ξ‖ ^ (m - α) : ℝ) : ℂ) * fourier φ (-ξ)))) =
      (mixtureConst m α : ℂ) * ∫ ξ : Euclid m, fourier g ξ * fourier φ (-ξ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0 : Euclid m)] with ξ hξ
    have hr : ‖ξ‖ ^ (α - m) * ‖ξ‖ ^ (m - α) = 1 := by
      rw [← Real.rpow_add (norm_pos_iff.mpr hξ)]
      simp
    have hc := congrArg Complex.ofReal hr
    push_cast at hc
    linear_combination (mixtureConst m α : ℂ) * fourier g ξ * fourier φ (-ξ) * hc
  rw [heq, integral_fourier_mul_neg]
  simp only [frameConst, Complex.ofReal_mul]
  ring

/-- Distributional reconstruction from the finite-dimensional frame representative against a positive pivot density. -/
theorem finite_backprojection_reconstruction {m : ℕ} {α : ℝ}
    (hα : 0 < α) (hαm : α < m) (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x)
    (hpc : Continuous p) (f : Euclid m → ℂ) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (φ : SchwartzMap (Euclid m) ℂ) :
    ∫ x, f x * φ x ∂densityMeasure p =
      ((frameConst m α * admissibilityConst α ρ)⁻¹ : ℝ) *
        ∫ x, (admissibilityConst α ρ * frameRepresentative (directionMeasure m α) g x) *
          fracLaplacian ((m - α) / 2) φ x := by
  have hL : (∫ x, f x * φ x ∂densityMeasure p) = ∫ x, g x * φ x := by
    rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul hpc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hp x).le, Complex.real_smul, hg]
    ring
  rw [hL]
  simp_rw [mul_assoc (admissibilityConst α ρ : ℂ)]
  rw [integral_const_mul, integral_frameRepresentative_fracLaplacian hα hαm]
  have hC : (admissibilityConst α ρ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hρ.isAdmissible α).pos.ne'
  have hk : (frameConst m α : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (mul_pos (pow_pos (by positivity : 0 < 2 * Real.pi) m) (mixtureConst_pos hαm))
  push_cast
  field_simp

end OperatorRidgelet.FiniteDim

