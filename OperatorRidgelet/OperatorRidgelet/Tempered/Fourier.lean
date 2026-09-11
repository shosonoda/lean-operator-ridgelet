import OperatorRidgelet.Tempered.Defs
import OperatorRidgelet.ToMathlib.FourierDilation

/-!
# The angular Fourier transform, the Bessel potential, and the weights

Complements to the vendored `LeanRidgelet.Fourier.AngularDistribution` and
`LeanRidgelet.Space.Activation`: the angular Schwartz transform in terms of Mathlib's `𝓕`
(`angularFourierSchwartz_eq_fourier`), the inversion identity `F(F φ) = 2π φ(-·)`, injectivity,
and the intertwining `F ∘ B^r = ⟨·⟩^r ∘ F` of the Bessel potential with the weight in the
direction not covered by the vendored `angularBesselPotential_angularFourierDistribution`,
together with its consequences for the inverse transform, and the inverse relations
`⟨·⟩^r ⟨·⟩^{-r} = 1`, `B^r B^{-r} = 1` on tempered distributions.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform

/-! ### The angular Schwartz transform and Mathlib's transform -/

/-- The angular Fourier transform of a Schwartz function at `x` is Mathlib's transform at
`x/(2π)`. -/
theorem angularFourierSchwartz_eq_fourier (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    angularFourierSchwartz φ x = 𝓕 (⇑φ) ((2 * Real.pi)⁻¹ * x) := by
  unfold angularFourierSchwartz
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, realDilationCLE_apply]
  rfl

/-- Mathlib's Fourier transform applied twice is the reflection. -/
theorem fourier_fourier_schwartz_neg (φ : SchwartzMap ℝ ℂ) (y : ℝ) :
    𝓕 (𝓕 (⇑φ)) (-y) = φ y := by
  rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
    FourierTransform.fourierInv_fourier_eq]

/-- The angular Fourier transform applied twice is `2π` times the reflection. -/
theorem angularFourierSchwartz_angularFourierSchwartz (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    angularFourierSchwartz (angularFourierSchwartz φ) x = (2 * Real.pi : ℂ) * φ (-x) := by
  rw [angularFourierSchwartz_eq_fourier]
  have h : (⇑(angularFourierSchwartz φ)) = fun y => 𝓕 (⇑φ) ((2 * Real.pi)⁻¹ * y) :=
    funext (angularFourierSchwartz_eq_fourier φ)
  rw [h, Real.fourier_comp_mul_left _ (inv_ne_zero two_mul_pi_ne_zero), inv_inv, abs_inv,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), inv_inv,
    mul_inv_cancel_left₀ two_mul_pi_ne_zero, ← neg_neg x, fourier_fourier_schwartz_neg, neg_neg,
    Complex.real_smul]
  push_cast
  ring

/-- The angular Fourier transform is injective on Schwartz functions. -/
theorem angularFourierSchwartz_injective : Function.Injective angularFourierSchwartz := by
  intro φ ψ h
  apply (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).injective
  ext x
  have hx := congrArg (fun f : SchwartzMap ℝ ℂ => f (2 * Real.pi * x)) h
  simp only [angularFourierSchwartz_eq_fourier, inv_mul_cancel_left₀ two_mul_pi_ne_zero] at hx
  exact hx

/-- The reflection `φ(-·)` of a Schwartz function. -/
def reflectSchwartz (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) φ

/-- The reflected Schwartz function has value `φ (-x)`. -/
theorem reflectSchwartz_apply (φ : SchwartzMap ℝ ℂ) (x : ℝ) : reflectSchwartz φ x = φ (-x) := by
  rw [reflectSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rfl

/-- The support of the reflection of a function supported away from the origin stays away
from the origin. -/
theorem zero_notMem_tsupport_reflectSchwartz {φ : SchwartzMap ℝ ℂ} (hφ : (0 : ℝ) ∉ tsupport φ) :
    (0 : ℝ) ∉ tsupport (reflectSchwartz φ) := by
  rw [notMem_tsupport_iff_eventuallyEq] at hφ ⊢
  have hneg : Tendsto (fun ω : ℝ => -ω) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  filter_upwards [hφ.comp_tendsto hneg] with ω hω
  simpa [reflectSchwartz_apply] using hω

/-- The reflection of a compactly supported Schwartz function is compactly supported. -/
theorem hasCompactSupport_reflectSchwartz {φ : SchwartzMap ℝ ℂ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (reflectSchwartz φ) := by
  have h := hφ.comp_homeomorph (Homeomorph.neg ℝ)
  have heq : ⇑(reflectSchwartz φ) = ⇑φ ∘ ⇑(Homeomorph.neg ℝ) := funext fun x => by
    rw [reflectSchwartz_apply, Function.comp_apply]
    rfl
  rw [heq]
  exact h

/-! ### The Bessel multiplier and the weight -/

/-- The weight `⟨x⟩^r` is even. -/
theorem temperedWeight_neg (r : ℝ) (x : ℝ) : temperedWeight r (-x) = temperedWeight r x := by
  unfold temperedWeight japaneseBracketPow
  rw [norm_neg]

/-- The Bessel multiplier of the angular Fourier transform is the angular Fourier transform of
the weighted function: `B^r (F φ) = F (⟨·⟩^r φ)`. -/
theorem fourierMultiplier_angularFourierSchwartz (r : ℝ) (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol r) (angularFourierSchwartz φ) =
      angularFourierSchwartz (SchwartzMap.smulLeftCLM ℂ (temperedWeight r) φ) := by
  apply angularFourierSchwartz_injective
  rw [angularFourierSchwartz_fourierMultiplier]
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight r),
    angularFourierSchwartz_angularFourierSchwartz, angularFourierSchwartz_angularFourierSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight r), temperedWeight_neg,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The angular Fourier transform intertwines the Bessel potential with the weight:
`F (B^r u) = ⟨·⟩^r (F u)` on tempered distributions. -/
theorem angularFourierDistribution_angularBesselPotential (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    angularFourierDistribution (angularBesselPotential r u) =
      temperedWeightMultiplier r (angularFourierDistribution u) := by
  ext φ
  unfold angularBesselPotential temperedWeightMultiplier
  rw [angularFourierDistribution_apply, TemperedDistribution.fourierMultiplierCLM_apply_apply,
    fourier_smulLeft_fourierInv_of_even (hasTemperateGrowth_angularBesselSymbol r)
      (angularBesselSymbol_neg r), fourierMultiplier_angularFourierSchwartz,
    TemperedDistribution.smulLeftCLM_apply_apply, angularFourierDistribution_apply]

/-- `F⁻¹ (B^r v) = ⟨·⟩^r (F⁻¹ v)`. -/
theorem angularFourierInvDistribution_angularBesselPotential (r : ℝ)
    (v : TemperedDistribution ℝ ℂ) :
    angularFourierInvDistribution (angularBesselPotential r v) =
      temperedWeightMultiplier r (angularFourierInvDistribution v) := by
  have h := angularBesselPotential_angularFourierDistribution r (angularFourierInvDistribution v)
  rw [angularFourierDistribution_angularFourierInvDistribution] at h
  rw [h, angularFourierInvDistribution_angularFourierDistribution]

/-- `F⁻¹ (⟨·⟩^r v) = B^r (F⁻¹ v)`. -/
theorem angularFourierInvDistribution_temperedWeightMultiplier (r : ℝ)
    (v : TemperedDistribution ℝ ℂ) :
    angularFourierInvDistribution (temperedWeightMultiplier r v) =
      angularBesselPotential r (angularFourierInvDistribution v) := by
  have h := angularFourierDistribution_angularBesselPotential r (angularFourierInvDistribution v)
  rw [angularFourierDistribution_angularFourierInvDistribution] at h
  rw [← h, angularFourierInvDistribution_angularFourierDistribution]

/-! ### Inverses of the weights and of the Bessel potentials -/

/-- `⟨·⟩^r ⟨·⟩^{-r} u = u`. -/
theorem temperedWeightMultiplier_temperedWeightMultiplier_neg (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    temperedWeightMultiplier r (temperedWeightMultiplier (-r) u) = u := by
  unfold temperedWeightMultiplier
  have h2 : temperedWeight (-r) * temperedWeight r = 1 := by
    rw [mul_comm]
    exact temperedWeight_mul_neg r
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (hasTemperateGrowth_temperedWeight (-r))
    (hasTemperateGrowth_temperedWeight r)]
  simp only [h2]
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ => (1 : ℂ)) u = u
  simp

/-- `⟨·⟩^{-r} ⟨·⟩^r u = u`. -/
theorem temperedWeightMultiplier_neg_temperedWeightMultiplier (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    temperedWeightMultiplier (-r) (temperedWeightMultiplier r u) = u := by
  have h := temperedWeightMultiplier_temperedWeightMultiplier_neg (-r) u
  rwa [neg_neg] at h

/-- `B^r B^{-r} u = u`. -/
theorem angularBesselPotential_angularBesselPotential_neg (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    angularBesselPotential r (angularBesselPotential (-r) u) = u := by
  unfold angularBesselPotential
  have h1 : angularBesselSymbol (-r) * angularBesselSymbol r = 1 := angularBesselSymbol_neg_mul r
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_angularBesselSymbol (-r)) (hasTemperateGrowth_angularBesselSymbol r)]
  simp only [h1]
  change TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : ℝ => (1 : ℂ)) u = u
  rw [TemperedDistribution.fourierMultiplierCLM_const]
  simp

/-- `B^{-r} B^r u = u`. -/
theorem angularBesselPotential_neg_angularBesselPotential (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    angularBesselPotential (-r) (angularBesselPotential r u) = u := by
  have h := angularBesselPotential_angularBesselPotential_neg (-r) u
  rwa [neg_neg] at h

end OperatorRidgelet
