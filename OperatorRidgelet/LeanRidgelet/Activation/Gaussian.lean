-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Activation/Gaussian.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Activation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian activation

This file begins the standard-activation analysis of Chapter 5. The normalized Gaussian has angular
Fourier transform `exp (-ω² / 2)`, which directly gives its coordinate in `A_{0,0}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- Fourier coordinate of the normalized standard Gaussian in the angular-frequency convention. -/
def gaussianFourierCoordinateFn (ω : ℝ) : ℂ :=
  Complex.exp (-(2 : ℂ)⁻¹ * (ω : ℂ) ^ 2)

theorem memLp_gaussianFourierCoordinateFn :
    MemLp gaussianFourierCoordinateFn 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by
    unfold gaussianFourierCoordinateFn
    fun_prop)).2
  convert integrable_exp_neg_mul_sq (b := 1) (by positivity) using 1
  funext ω
  rw [show gaussianFourierCoordinateFn ω =
    Complex.exp (-(2 : ℂ)⁻¹ * (ω : ℂ) ^ 2) from rfl]
  rw [norm_cexp_neg_mul_sq]
  norm_num
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The standard Gaussian as an activation coordinate in `A_{0,0}`. -/
def gaussianActivation : ActivationSpace 0 0 :=
  memLp_gaussianFourierCoordinateFn.toLp gaussianFourierCoordinateFn

/-- The Gaussian activation coordinate is nonzero. -/
theorem gaussianActivation_ne_zero : gaussianActivation ≠ 0 := by
  intro hγ
  have hzero : ∀ᵐ ω ∂volume, gaussianActivation ω = 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp hγ
  have hcoe : gaussianActivation =ᵐ[volume] gaussianFourierCoordinateFn :=
    memLp_gaussianFourierCoordinateFn.coeFn_toLp
  have hfalse : ∀ᵐ _ω : ℝ ∂volume, False := by
    filter_upwards [hzero, hcoe] with ω hω hγω
    exact Complex.exp_ne_zero _ (hγω.symm.trans hω)
  exact hfalse.exists.elim fun _ h ↦ h

/-- At `(s,t)=(0,0)`, realization agrees with the canonical `L²` tempered distribution. -/
theorem activationDistribution_gaussianActivation :
    activationDistribution 0 0 gaussianActivation =
      Lp.toTemperedDistributionCLM ℂ volume 2 gaussianActivation := by
  have hweight : temperedWeight 0 = fun _ : ℝ ↦ 1 := by
    funext x
    simp [temperedWeight]
  have hbessel : angularBesselSymbol 0 = fun _ : ℝ ↦ 1 := by
    funext ξ
    simp [angularBesselSymbol]
  unfold activationDistribution temperedWeightMultiplier angularBesselPotential
  simp only [neg_zero]
  rw [hweight, hbessel]
  simp [TemperedDistribution.smulLeftCLM_const,
    TemperedDistribution.fourierMultiplierCLM_const]

end LeanRidgelet
