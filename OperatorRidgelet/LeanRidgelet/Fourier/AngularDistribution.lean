-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Fourier/AngularDistribution.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex, Claude
-/
module

public import LeanRidgelet.Fourier.Convention
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Angular-frequency Fourier analysis on tempered distributions

This file implements the manuscript convention `f♯(ω) = ∫ z, exp (-i z ω) f(z) dz` on
one-dimensional tempered distributions: pointwise and distributional conjugation, real
dilations, the angular-frequency forward and inverse Fourier transforms with their test-function
actions, the `L¹` inversion theorem in the angular convention, and the even-symbol transpose
identity used by Fourier multipliers.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate FourierTransform RealInnerProductSpace
open FourierTransform MeasureTheory TemperedDistribution

namespace LeanRidgelet.Fourier

section TemperedDistribution

/-! ### The manuscript convention on one-dimensional tempered distributions -/

/-- Pointwise complex conjugation as a continuous conjugate-linear map on Schwartz space. -/
def schwartzConjugation :
    SchwartzMap ℝ ℂ →SL[starRingEnd ℂ] SchwartzMap ℝ ℂ where
  toFun := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
  map_add' f g := by
    ext x
    simp [SchwartzMap.postcompCLM_apply]
  map_smul' c f := by
    ext x
    simp [SchwartzMap.postcompCLM_apply]
  cont := by
    exact (SchwartzMap.postcompCLM (𝕜 := ℝ)
      Complex.conjCLE.toContinuousLinearMap).continuous

@[simp]
theorem schwartzConjugation_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzConjugation f x = conj (f x) := rfl

@[simp]
theorem schwartzConjugation_involutive (f : SchwartzMap ℝ ℂ) :
    schwartzConjugation (schwartzConjugation f) = f := by
  ext x
  simp

/-- Distributional complex conjugation, defined by
`conj u [φ] = conj (u [conj φ])`. -/
def temperedDistributionConjugation :
    TemperedDistribution ℝ ℂ →SL[starRingEnd ℂ] TemperedDistribution ℝ ℂ :=
  (PointwiseConvergenceCLM.postcomp (SchwartzMap ℝ ℂ)
    ({ toFun := conj
       map_add' := map_add conj
       map_smul' := fun c z ↦ by simp
       cont := Complex.continuous_conj } : ℂ →SL[starRingEnd ℂ] ℂ)).comp
    (PointwiseConvergenceCLM.precomp ℂ schwartzConjugation)

@[simp]
theorem temperedDistributionConjugation_apply
    (u : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    temperedDistributionConjugation u φ = conj (u (schwartzConjugation φ)) := rfl

@[simp]
theorem temperedDistributionConjugation_involutive (u : TemperedDistribution ℝ ℂ) :
    temperedDistributionConjugation (temperedDistributionConjugation u) = u := by
  ext φ
  change conj (conj (u (schwartzConjugation (schwartzConjugation φ)))) = u φ
  simp

/-- Multiplication by a nonzero real scalar as a continuous linear equivalence. -/
def realDilationCLE (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

@[simp]
theorem realDilationCLE_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    realDilationCLE c hc x = c * x := rfl

@[simp]
theorem realDilationCLE_symm_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    (realDilationCLE c hc).symm x = c⁻¹ * x := by
  change (↑(Units.mk0 c hc)⁻¹ : ℝ) • x = c⁻¹ * x
  simp [smul_eq_mul]

/-- Pull a one-dimensional tempered distribution back by `x ↦ c x`.

For an ordinary function `u`, the resulting distribution represents `x ↦ u (c x)`.  The
Jacobian factor is included in the action on Schwartz test functions. -/
def temperedDistributionDilation (c : ℝ) (hc : c ≠ 0) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  ((|c| : ℝ) : ℂ)⁻¹ •
    PointwiseConvergenceCLM.precomp ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE c hc).symm)

theorem temperedDistributionDilation_apply (c : ℝ) (hc : c ≠ 0)
    (u : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    temperedDistributionDilation c hc u φ =
      ((|c| : ℝ) : ℂ)⁻¹ *
        u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE c hc).symm φ) := rfl

/-- Distributional dilation agrees with pointwise dilation on Schwartz functions. -/
theorem temperedDistributionDilation_toTemperedDistributionCLM_eq
    (c : ℝ) (hc : c ≠ 0) (f : SchwartzMap ℝ ℂ) :
    temperedDistributionDilation c hc
        (SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume f) =
      SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilationCLE c hc) f) := by
  ext φ
  rw [temperedDistributionDilation_apply]
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply, smul_eq_mul]
  rw [show (∫ x : ℝ,
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE c hc).symm φ) x * f x) =
      |c| * ∫ y : ℝ, φ y *
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE c hc) f) y by
    let F : ℝ → ℂ := fun x ↦
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE c hc).symm φ) x * f x
    have hfun : (fun y : ℝ ↦ φ y *
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE c hc) f) y) = fun y ↦ F (c • y) := by
      funext y
      change φ y * f (c * y) = φ ((realDilationCLE c hc).symm (c * y)) * f (c * y)
      congr 1
      rw [realDilationCLE_symm_apply]
      field_simp [hc]
    rw [hfun, Measure.integral_comp_smul volume F c]
    simp only [Module.finrank_self, pow_one]
    simp [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      abs_inv, abs_ne_zero.mpr hc]]
  field_simp [abs_ne_zero.mpr hc]

/-- Dilation by `c` and then by `c⁻¹` cancel on tempered distributions. -/
theorem temperedDistributionDilation_inv (c : ℝ) (hc : c ≠ 0)
    (u : TemperedDistribution ℝ ℂ) :
    temperedDistributionDilation c hc
        (temperedDistributionDilation c⁻¹ (inv_ne_zero hc) u) = u := by
  ext φ
  change ((|c| : ℝ) : ℂ)⁻¹ *
      (((|c⁻¹| : ℝ) : ℂ)⁻¹ *
        u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE c⁻¹ (inv_ne_zero hc)).symm
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realDilationCLE c hc).symm φ))) = u φ
  have htest :
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE c⁻¹ (inv_ne_zero hc)).symm
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realDilationCLE c hc).symm φ) = φ := by
    ext x
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    change φ ((realDilationCLE c hc).symm
      ((realDilationCLE c⁻¹ (inv_ne_zero hc)).symm x)) = φ x
    congr 1
    rw [realDilationCLE_symm_apply, realDilationCLE_symm_apply]
    field_simp [hc]
  rw [htest]
  simp [abs_inv, abs_ne_zero.mpr hc]


/-- Fourier transform of a one-dimensional tempered distribution in the manuscript convention
`exp (-i x ω)`. -/
def angularFourierDistribution :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  temperedDistributionDilation (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero) ∘L
    FourierTransform.fourierCLM ℂ (TemperedDistribution ℝ ℂ)

/-- Inverse Fourier transform of a one-dimensional tempered distribution in the manuscript
convention. -/
def angularFourierInvDistribution :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  FourierTransform.fourierInvCLM ℂ (TemperedDistribution ℝ ℂ) ∘L
    temperedDistributionDilation (2 * Real.pi) two_mul_pi_ne_zero

/-- The angular-frequency Fourier transform of a Schwartz function, still in Schwartz space. -/
def angularFourierSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) (𝓕 f)

/-- The distributional angular Fourier transform agrees with the Schwartz-space formula. -/
theorem angularFourierDistribution_toTemperedDistributionCLM_eq
    (f : SchwartzMap ℝ ℂ) :
    angularFourierDistribution
        (SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume f) =
      SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume (angularFourierSchwartz f) := by
  unfold angularFourierDistribution angularFourierSchwartz
  simp only [ContinuousLinearMap.comp_apply, fourierCLM_apply]
  rw [TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
  exact temperedDistributionDilation_toTemperedDistributionCLM_eq
    (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero) (𝓕 f)

/-- The angular-frequency Fourier transform is a left inverse of its inverse transform. -/
theorem angularFourierDistribution_angularFourierInvDistribution
    (u : TemperedDistribution ℝ ℂ) :
    angularFourierDistribution (angularFourierInvDistribution u) = u := by
  unfold angularFourierDistribution angularFourierInvDistribution
  simp only [ContinuousLinearMap.comp_apply, fourierCLM_apply, fourierInvCLM_apply]
  rw [fourier_fourierInv_eq]
  simpa only [inv_inv] using
    temperedDistributionDilation_inv (2 * Real.pi)⁻¹
      (inv_ne_zero two_mul_pi_ne_zero) u

/-- The angular-frequency inverse Fourier transform is a left inverse of the forward transform. -/
theorem angularFourierInvDistribution_angularFourierDistribution
    (u : TemperedDistribution ℝ ℂ) :
    angularFourierInvDistribution (angularFourierDistribution u) = u := by
  unfold angularFourierDistribution angularFourierInvDistribution
  simp only [ContinuousLinearMap.comp_apply, fourierCLM_apply, fourierInvCLM_apply]
  rw [show temperedDistributionDilation (2 * Real.pi) two_mul_pi_ne_zero
      (temperedDistributionDilation (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)
        (𝓕 u)) = 𝓕 u by
    exact temperedDistributionDilation_inv (2 * Real.pi) two_mul_pi_ne_zero (𝓕 u)]
  exact fourierInv_fourier_eq u

end TemperedDistribution

/-! ### Test-function action and inversion for the angular convention on `ℝ` -/

/-- The angular-frequency Schwartz Fourier transform is the angular Fourier integral. -/
theorem angularFourierSchwartz_eq_angularFourierIntegralInner
    (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    angularFourierSchwartz f ξ = angularFourierIntegralInner (f : ℝ → ℂ) ξ := by
  rw [angularFourierIntegralInner_eq_mathlib]
  unfold angularFourierSchwartz
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourier_coe]
  rfl

/-- Pointwise integral formula for the angular-frequency Schwartz Fourier transform. -/
theorem angularFourierSchwartz_apply (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    angularFourierSchwartz f ξ =
      ∫ b : ℝ, Complex.exp (-Complex.I * (b * ξ)) * f b := by
  rw [angularFourierSchwartz_eq_angularFourierIntegralInner]
  unfold angularFourierIntegralInner
  apply integral_congr_ae
  filter_upwards with b
  have harg : -Complex.I * ((inner ℝ b ξ : ℝ) : ℂ) =
      -Complex.I * ((b : ℂ) * (ξ : ℂ)) := by
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [harg]

/-- Rescaling a Schwartz function by `2π` rescales its Mathlib Fourier transform to the angular
transform. -/
theorem fourier_schwartz_comp_two_pi (φ : SchwartzMap ℝ ℂ) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)).symm φ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ • angularFourierSchwartz φ := by
  ext ξ
  let F : ℝ → ℂ := fun w ↦ Real.fourierChar (-(w * ((2 * Real.pi)⁻¹ * ξ))) • φ w
  have hstep1 : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)).symm φ) ξ =
      ∫ v : ℝ, F ((2 * Real.pi) • v) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with v
    have hval : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)).symm φ) v =
        φ (2 * Real.pi * v) := by
      rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      change φ ((realDilationCLE (2 * Real.pi)⁻¹
        (inv_ne_zero two_mul_pi_ne_zero)).symm v) = _
      rw [realDilationCLE_symm_apply, inv_inv]
    have hchar : -(inner ℝ v ξ) = -(2 * Real.pi * v * ((2 * Real.pi)⁻¹ * ξ)) := by
      simp only [RCLike.inner_apply, conj_trivial, neg_inj]
      rw [show 2 * Real.pi * v * ((2 * Real.pi)⁻¹ * ξ) =
          2 * Real.pi * (2 * Real.pi)⁻¹ * (v * ξ) by ring,
        mul_inv_cancel₀ two_mul_pi_ne_zero, one_mul]
      exact mul_comm ξ v
    change Real.fourierChar (-(inner ℝ v ξ)) •
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)).symm φ) v =
        F ((2 * Real.pi) • v)
    rw [hval, hchar]
    change Real.fourierChar (-(2 * Real.pi * v * ((2 * Real.pi)⁻¹ * ξ))) •
        φ (2 * Real.pi * v) =
      Real.fourierChar (-((2 * Real.pi) • v * ((2 * Real.pi)⁻¹ * ξ))) •
        φ ((2 * Real.pi) • v)
    rw [smul_eq_mul]
  have hstep2 : (∫ v : ℝ, F ((2 * Real.pi) • v)) =
      |((2 * Real.pi) ^ Module.finrank ℝ ℝ)⁻¹| • ∫ w : ℝ, F w :=
    Measure.integral_comp_smul volume F (2 * Real.pi)
  have hstep3 : (∫ w : ℝ, F w) = angularFourierSchwartz φ ξ := by
    unfold angularFourierSchwartz
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    change _ = 𝓕 φ ((realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) ξ)
    rw [realDilationCLE_apply, SchwartzMap.fourier_coe, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with w
    change F w = Real.fourierChar (-(inner ℝ w ((2 * Real.pi)⁻¹ * ξ))) • φ w
    have hchar : -(w * ((2 * Real.pi)⁻¹ * ξ)) = -(inner ℝ w ((2 * Real.pi)⁻¹ * ξ)) := by
      simp only [RCLike.inner_apply, conj_trivial, neg_inj]
      ring
    change Real.fourierChar (-(w * ((2 * Real.pi)⁻¹ * ξ))) • φ w = _
    rw [hchar]
  rw [hstep1, hstep2, hstep3]
  have habs : |((2 * Real.pi) ^ Module.finrank ℝ ℝ)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [Module.finrank_self, pow_one, abs_inv, abs_of_pos (by positivity)]
  rw [habs, smul_apply, Complex.real_smul]
  push_cast
  rfl

/-- The angular-frequency distributional Fourier transform acts by the angular-frequency Schwartz
transform on test functions. -/
theorem angularFourierDistribution_apply (u : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    angularFourierDistribution u φ = u (angularFourierSchwartz φ) := by
  unfold angularFourierDistribution
  simp only [ContinuousLinearMap.comp_apply, fourierCLM_apply]
  rw [temperedDistributionDilation_apply, TemperedDistribution.fourier_apply,
    fourier_schwartz_comp_two_pi, map_smul]
  have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_inv, abs_of_pos (by positivity)]
  rw [habs]
  rw [smul_eq_mul, ← mul_assoc]
  have hpi : (((2 * Real.pi)⁻¹ : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ)⁻¹ = 1 := by
    push_cast
    field_simp
  rw [hpi, one_mul]

/-- Angular-convention `L¹` Fourier inversion: if a continuous integrable function has an
integrable angular inverse transform `g`, then it is recovered from `g` by the angular forward
integral. -/
theorem angularFourier_inversion_of_integrable {f g : ℝ → ℂ}
    (hf_cont : Continuous f) (hf : Integrable f) (hg : Integrable g)
    (hfg : ∀ ω : ℝ,
      (2 * Real.pi : ℂ)⁻¹ * ∫ z : ℝ, f z * Complex.exp (Complex.I * (z * ω)) = g ω)
    (z : ℝ) :
    f z = ∫ ω : ℝ, g ω * Complex.exp (-Complex.I * (z * ω)) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := two_mul_pi_complex_ne_zero
  have hInv : ∀ ν : ℝ, 𝓕⁻ f ν = 2 * Real.pi * g (2 * Real.pi * ν) := by
    intro ν
    rw [Real.fourierInv_eq]
    have hval := hfg (2 * Real.pi * ν)
    have hintegrand : (∫ v : ℝ, Real.fourierChar (inner ℝ v ν) • f v) =
        ∫ v : ℝ, f v * Complex.exp (Complex.I * ((v : ℂ) * ((2 * Real.pi * ν : ℝ) : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [Circle.smul_def, Real.fourierChar_apply]
      simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
      rw [mul_comm]
      congr 1
      push_cast
      ring
    rw [hintegrand, ← hval, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  have hInvFun : 𝓕⁻ f = fun ν : ℝ ↦ 2 * Real.pi * g (2 * Real.pi * ν) := funext hInv
  have hgInt : Integrable (fun ν : ℝ ↦ 2 * Real.pi * g (2 * Real.pi * ν)) := by
    have hcomp : Integrable (fun ν : ℝ ↦ g ((2 * Real.pi) • ν)) :=
      hg.comp_smul two_mul_pi_ne_zero
    simpa only [smul_eq_mul] using hcomp.const_mul (2 * Real.pi : ℂ)
  have hInvInt : Integrable (𝓕⁻ f) := by
    rw [hInvFun]
    exact hgInt
  have hFInt : Integrable (𝓕 f) := by
    have hneg : Integrable (fun w : ℝ ↦ 𝓕⁻ f (-w)) := by
      have hcomp := hInvInt.comp_smul (by norm_num : (-1 : ℝ) ≠ 0)
      simpa only [neg_smul, one_smul] using hcomp
    refine hneg.congr ?_
    filter_upwards with w
    rw [Real.fourierInv_eq_fourier_neg f (-w), neg_neg]
  have hInversion := hf_cont.fourier_fourierInv_eq hf hFInt
  have hpoint : 𝓕 (𝓕⁻ f) z = f z := congrFun hInversion z
  rw [← hpoint, Real.fourier_eq]
  have hexp : (∫ ν : ℝ, Real.fourierChar (-inner ℝ ν z) • 𝓕⁻ f ν) =
      ∫ ν : ℝ, (fun ω : ℝ ↦ 2 * Real.pi * (g ω * Complex.exp (-Complex.I * (z * ω))))
        ((2 * Real.pi) • ν) := by
    apply integral_congr_ae
    filter_upwards with ν
    simp only [smul_eq_mul]
    rw [hInv ν, Circle.smul_def, Real.fourierChar_apply]
    have harg : ((2 * Real.pi * -inner ℝ ν z : ℝ) : ℂ) * Complex.I =
        -Complex.I * ((z : ℂ) * ((2 * Real.pi * ν : ℝ) : ℂ)) := by
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    rw [harg]
    ring
  rw [hexp, Measure.integral_comp_smul volume
    (fun ω : ℝ ↦ 2 * Real.pi * (g ω * Complex.exp (-Complex.I * (z * ω)))) (2 * Real.pi)]
  simp only [Module.finrank_self, pow_one]
  rw [abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [integral_const_mul, Complex.real_smul, ← mul_assoc]
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr two_mul_pi_ne_zero
  push_cast at hπ ⊢
  rw [inv_mul_cancel₀ hπ, one_mul]

/-- For an even multiplier symbol, the transposed action appearing in the distributional Fourier
multiplier agrees with the Schwartz-level Fourier multiplier. -/
theorem fourier_smulLeft_fourierInv_of_even {g : ℝ → ℂ}
    (hg : Function.HasTemperateGrowth g) (hge : ∀ ξ : ℝ, g (-ξ) = g ξ)
    (h : SchwartzMap ℝ ℂ) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ h)) = SchwartzMap.fourierMultiplierCLM ℂ g h := by
  ext x
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe]
  have hleft : (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ h) : ℝ → ℂ) =
      fun ω : ℝ ↦ g ω • 𝓕 (h : ℝ → ℂ) (-ω) := by
    funext ω
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg]
  have hright : (SchwartzMap.smulLeftCLM ℂ g (𝓕 h) : ℝ → ℂ) =
      fun ω : ℝ ↦ g ω • 𝓕 (h : ℝ → ℂ) ω := by
    funext ω
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe]
  rw [hleft, hright, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun ω : ℝ ↦ g ω • 𝓕 (h : ℝ → ℂ) (-ω)) =
      fun ω : ℝ ↦ g (-ω) • 𝓕 (h : ℝ → ℂ) (-ω) := by
    funext ω
    rw [hge ω]
  rw [hfun]

end LeanRidgelet.Fourier
