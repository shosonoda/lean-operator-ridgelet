-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Space/Activation.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Basic
public import LeanRidgelet.Fourier.AngularLp
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Activation Hilbert space

This file begins the formalization of Section 2.1 and Proposition 1 of the L2 manuscript. The
activation space is represented by its `L²(ℝ)` coordinate under the isometric isomorphism (7).
Its realization as a tempered distribution is reconstructed using a Bessel potential and
multiplication by a Japanese-bracket weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal FourierTransform SchwartzMap

namespace LeanRidgelet

open Fourier

/-- The Japanese bracket to the power `r`: `⟨x⟩^r = (1 + ‖x‖²)^(r / 2)`. -/
def japaneseBracketPow {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (r / 2)

theorem japaneseBracketPow_pos {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) :
    0 < japaneseBracketPow r x := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem japaneseBracketPow_add {E : Type*} [NormedAddCommGroup E]
    (r u : ℝ) (x : E) :
    japaneseBracketPow (r + u) x = japaneseBracketPow r x * japaneseBracketPow u x := by
  unfold japaneseBracketPow
  rw [show (r + u) / 2 = r / 2 + u / 2 by ring]
  exact Real.rpow_add (by positivity) _ _

theorem japaneseBracketPow_sq {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) :
    japaneseBracketPow r x ^ 2 = japaneseBracketPow (2 * r) x := by
  rw [pow_two, ← japaneseBracketPow_add]
  congr 1
  ring

@[simp]
theorem japaneseBracketPow_zero {E : Type*} [NormedAddCommGroup E] (x : E) :
    japaneseBracketPow 0 x = 1 := by
  simp [japaneseBracketPow]

/-- The complex-valued Japanese-bracket multiplier used on tempered distributions. -/
def temperedWeight (r : ℝ) (x : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow r x)

@[simp]
theorem temperedWeight_mul_neg (r : ℝ) : temperedWeight r * temperedWeight (-r) = 1 := by
  funext x
  simp only [Pi.mul_apply, Pi.one_apply, temperedWeight, ← Complex.ofReal_mul]
  rw [← japaneseBracketPow_add]
  simp

@[fun_prop]
theorem hasTemperateGrowth_temperedWeight (r : ℝ) :
    Function.HasTemperateGrowth (temperedWeight r) := by
  unfold temperedWeight japaneseBracketPow
  fun_prop

/-- Multiplication of a tempered distribution by `⟨x⟩^r`. -/
def temperedWeightMultiplier (r : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.smulLeftCLM ℂ (temperedWeight r)

/-- Multiplication by a Japanese-bracket weight commutes with the canonical embedding of a
Schwartz function into tempered distributions. -/
theorem temperedWeightMultiplier_toTemperedDistributionCLM
    (r : ℝ) (f : SchwartzMap ℝ ℂ) :
    temperedWeightMultiplier r
        (SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume f) =
      SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume
        (SchwartzMap.smulLeftCLM ℂ (temperedWeight r) f) := by
  ext φ
  simp only [temperedWeightMultiplier,
    TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards with ω
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_temperedWeight r)]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_temperedWeight r)]
  simp [smul_eq_mul]
  ring

/-- The Bessel symbol in Mathlib frequency coordinates for the angular-frequency Fourier
convention. -/
def angularBesselSymbol (r : ℝ) (ξ : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow r ((2 * Real.pi) * ξ))

@[simp]
theorem angularBesselSymbol_neg_mul (r : ℝ) :
    angularBesselSymbol (-r) * angularBesselSymbol r = 1 := by
  funext ξ
  simp only [Pi.mul_apply, Pi.one_apply, angularBesselSymbol, ← Complex.ofReal_mul]
  rw [← japaneseBracketPow_add]
  simp

@[fun_prop]
theorem hasTemperateGrowth_angularBesselSymbol (r : ℝ) :
    Function.HasTemperateGrowth (angularBesselSymbol r) := by
  unfold angularBesselSymbol japaneseBracketPow
  exact (Function.Complex.hasTemperateGrowth_ofReal).comp <|
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (r / 2)).comp (by fun_prop)

/-- The Bessel potential for the angular-frequency convention `exp (-i x · ξ)`.

Mathlib uses a `2π` Fourier character, hence the rescaled symbol `⟨2πξ⟩^r`. -/
def angularBesselPotential (r : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.fourierMultiplierCLM ℂ (angularBesselSymbol r)

/-- Membership in the angular-frequency Sobolev space `H^s(ℝ)`. -/
def MemAngularSobolev (s : ℝ) (σ : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ f : L2 ℝ volume, angularBesselPotential s σ = f

/-- Membership in the real-domain description `⟨·⟩^t H^s(ℝ)` of the activation space. -/
def MemActivationSpace (s t : ℝ) (σ : TemperedDistribution ℝ ℂ) : Prop :=
  MemAngularSobolev s (temperedWeightMultiplier (-t) σ)

/-- The Hilbert coordinate model of the activation space `A_{s,t}`. -/
abbrev ActivationSpace (_s _t : ℝ) := L2 ℝ volume

/-- The activation-space isometry in the transported `L²` coordinate model. -/
def activationCoordinateEquiv (s t : ℝ) : ActivationSpace s t ≃ₗᵢ[ℂ] L2 ℝ volume :=
  LinearIsometryEquiv.refl ℂ (L2 ℝ volume)

/-- Realize an activation coordinate as an element of `⟨·⟩^t H^s(ℝ) ⊆ 𝓢'(ℝ)`. -/
def activationDistribution (s t : ℝ) :
    ActivationSpace s t →L[ℂ] TemperedDistribution ℝ ℂ :=
  temperedWeightMultiplier t ∘L
    angularBesselPotential (-s) ∘L
      Lp.toTemperedDistributionCLM ℂ volume 2

/-- Applying the inverse weights recovers the original `L²` coordinate as a distribution. -/
theorem angularBesselPotential_temperedWeightMultiplier_activationDistribution
    (s t : ℝ) (σ : ActivationSpace s t) :
    angularBesselPotential s
        (temperedWeightMultiplier (-t) (activationDistribution s t σ)) =
      Lp.toTemperedDistributionCLM ℂ volume 2 σ := by
  unfold activationDistribution angularBesselPotential temperedWeightMultiplier
  simp only [ContinuousLinearMap.comp_apply]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_temperedWeight t) (hasTemperateGrowth_temperedWeight (-t))]
  rw [temperedWeight_mul_neg]
  have hone (f : TemperedDistribution ℝ ℂ) :
      TemperedDistribution.smulLeftCLM ℂ (1 : ℝ → ℂ) f = f := by
    change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ ↦ 1) f = f
    simp
  rw [hone]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_angularBesselSymbol (-s)) (hasTemperateGrowth_angularBesselSymbol s)]
  rw [angularBesselSymbol_neg_mul]
  change TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : ℝ ↦ 1)
    (Lp.toTemperedDistributionCLM ℂ volume 2 σ) = _
  rw [TemperedDistribution.fourierMultiplierCLM_const]
  simp

/-- The concrete realization of every activation coordinate belongs to `A_{s,t}`. -/
theorem memActivationSpace_activationDistribution (s t : ℝ) (σ : ActivationSpace s t) :
    MemActivationSpace s t (activationDistribution s t σ) := by
  exact ⟨σ, angularBesselPotential_temperedWeightMultiplier_activationDistribution s t σ⟩

/-- Multiplication by the trivial weight `⟨x⟩⁰` is the identity. -/
theorem temperedWeightMultiplier_zero_apply (u : TemperedDistribution ℝ ℂ) :
    temperedWeightMultiplier 0 u = u := by
  have hone : temperedWeight 0 = fun _ : ℝ ↦ (1 : ℂ) := by
    funext x
    simp [temperedWeight]
  unfold temperedWeightMultiplier
  rw [hone]
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ ↦ (1 : ℂ)) u = u
  simp

/-- The order-zero angular Bessel potential is the identity. -/
theorem angularBesselPotential_zero_apply (u : TemperedDistribution ℝ ℂ) :
    angularBesselPotential 0 u = u := by
  have hone : angularBesselSymbol 0 = fun _ : ℝ ↦ (1 : ℂ) := by
    funext ξ
    simp [angularBesselSymbol]
  unfold angularBesselPotential
  rw [hone]
  change TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : ℝ ↦ (1 : ℂ)) u = u
  rw [TemperedDistribution.fourierMultiplierCLM_const]
  simp

/-- The angular Bessel symbol is even. -/
theorem angularBesselSymbol_neg (r : ℝ) (ξ : ℝ) :
    angularBesselSymbol r (-ξ) = angularBesselSymbol r ξ := by
  unfold angularBesselSymbol japaneseBracketPow
  rw [show (2 * Real.pi) * -ξ = -((2 * Real.pi) * ξ) by ring, norm_neg]

/-- The angular Fourier transform intertwines the Bessel multiplier with the Japanese-bracket
weight on Schwartz functions: `(⟨∂ω⟩^r φ)♯ = ⟨ω⟩^r φ♯`. -/
theorem angularFourierSchwartz_fourierMultiplier (r : ℝ) (φ : SchwartzMap ℝ ℂ) :
    angularFourierSchwartz (SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol r) φ) =
      SchwartzMap.smulLeftCLM ℂ (temperedWeight r) (angularFourierSchwartz φ) := by
  have hFmult : 𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol r) φ) =
      SchwartzMap.smulLeftCLM ℂ (angularBesselSymbol r) (𝓕 φ) := by
    rw [SchwartzMap.fourierMultiplierCLM_apply]
    exact FourierTransform.fourier_fourierInv_eq _
  ext ω
  unfold angularFourierSchwartz
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change 𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (angularBesselSymbol r) φ)
      ((realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) ω) = _
  rw [hFmult, realDilationCLE_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_angularBesselSymbol r),
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight r)]
  have harg : angularBesselSymbol r ((2 * Real.pi)⁻¹ * ω) = temperedWeight r ω := by
    unfold angularBesselSymbol temperedWeight
    congr 1
    rw [show 2 * Real.pi * ((2 * Real.pi)⁻¹ * ω) =
        (2 * Real.pi * (2 * Real.pi)⁻¹) * ω by ring,
      mul_inv_cancel₀ two_mul_pi_ne_zero, one_mul]
  rw [harg]
  rfl

/-- The angular Fourier transform intertwines the Bessel potential with the Japanese-bracket
weight on tempered distributions: `⟨∂ω⟩^r[𝓕_p u] = 𝓕_p[⟨x⟩^r u]`. -/
theorem angularBesselPotential_angularFourierDistribution (r : ℝ)
    (u : TemperedDistribution ℝ ℂ) :
    angularBesselPotential r (angularFourierDistribution u) =
      angularFourierDistribution (temperedWeightMultiplier r u) := by
  ext φ
  unfold angularBesselPotential
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply,
    fourier_smulLeft_fourierInv_of_even (hasTemperateGrowth_angularBesselSymbol r)
      (angularBesselSymbol_neg r) φ,
    angularFourierDistribution_apply, angularFourierDistribution_apply,
    angularFourierSchwartz_fourierMultiplier]
  unfold temperedWeightMultiplier
  rw [TemperedDistribution.smulLeftCLM_apply_apply]

/-- The manuscript activation spectrum `σ♯ = ⟨∂ω⟩^t[⟨ω⟩^{-s} σ]`, reconstructed from the
`L²` activation coordinate `σ = ⟨ω⟩^s ⟨∂ω⟩^{-t}[σ♯]`. -/
def activationSpectrum (s t : ℝ) :
    ActivationSpace s t →L[ℂ] TemperedDistribution ℝ ℂ :=
  angularBesselPotential t ∘L
    temperedWeightMultiplier (-s) ∘L
      Lp.toTemperedDistributionCLM ℂ volume 2

/-- The classical activation `σ = 𝓕⁻¹_ang[σ♯]`, realized as a tempered distribution from the
activation coordinate.  This is the activation whose network the synthesis operator actually
computes; compare `activationDistribution`, which realizes the same coordinate through the
real-domain weighted Sobolev isometry instead. -/
def activationRealization (s t : ℝ) :
    ActivationSpace s t →L[ℂ] TemperedDistribution ℝ ℂ :=
  angularFourierInvDistribution ∘L activationSpectrum s t

/-- The angular Fourier transform of the realized activation is its spectrum. -/
theorem angularFourierDistribution_activationRealization (s t : ℝ)
    (σ : ActivationSpace s t) :
    angularFourierDistribution (activationRealization s t σ) = activationSpectrum s t σ :=
  angularFourierDistribution_angularFourierInvDistribution _

/-- On `A_{0,t}`, the spectrum of an angular-Fourier-transformed `L²` coordinate is the
angular Fourier transform of its weighted distribution. -/
theorem activationSpectrum_zero_angularFourierLp (t : ℝ) (σ0 : L2 ℝ volume) :
    activationSpectrum 0 t (angularFourierLp σ0) =
      angularFourierDistribution
        (temperedWeightMultiplier t (Lp.toTemperedDistributionCLM ℂ volume 2 σ0)) := by
  unfold activationSpectrum
  simp only [ContinuousLinearMap.comp_apply, neg_zero]
  rw [temperedWeightMultiplier_zero_apply, toTemperedDistribution_angularFourierLp,
    angularBesselPotential_angularFourierDistribution]

/-- On `A_{0,t}`, the realized classical activation of a angular-Fourier-transformed `L²`
coordinate is the weighted distribution `⟨x⟩^t σ₀`.  This is the interface used to realize
concrete activations such as `tanh` and ReLU. -/
theorem activationRealization_zero_angularFourierLp (t : ℝ) (σ0 : L2 ℝ volume) :
    activationRealization 0 t (angularFourierLp σ0) =
      temperedWeightMultiplier t (Lp.toTemperedDistributionCLM ℂ volume 2 σ0) := by
  unfold activationRealization
  rw [ContinuousLinearMap.comp_apply, activationSpectrum_zero_angularFourierLp,
    angularFourierInvDistribution_angularFourierDistribution]

/-- The activation-space isometry gives unique `L²` coordinates for realized activations. -/
theorem activationDistribution_injective (s t : ℝ) :
    Function.Injective (activationDistribution s t) := by
  intro σ τ hστ
  have hdist : Lp.toTemperedDistributionCLM ℂ volume 2 σ =
      Lp.toTemperedDistributionCLM ℂ volume 2 τ := by
    rw [← angularBesselPotential_temperedWeightMultiplier_activationDistribution s t σ,
      ← angularBesselPotential_temperedWeightMultiplier_activationDistribution s t τ, hστ]
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  exact hdist

end LeanRidgelet
