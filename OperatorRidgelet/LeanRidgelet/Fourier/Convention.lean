-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Fourier/Convention.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The angular-frequency Fourier convention of the ridgelet manuscripts

Mathlib uses the character `exp (2 π i x)` whereas the L2 ridgelet manuscript uses

`f̂(ξ) = ∫ x, exp (-i ⟪x, ξ⟫) f(x) dx`.

We define the latter integral explicitly here. All normalization bridges between this convention
and Mathlib's unitary Fourier transform should live in this file.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate FourierTransform RealInnerProductSpace
open FourierTransform MeasureTheory

/-- Multiplying an integrable function by an a.e.-bounded-by-one measurable factor preserves
integrability.  This is the common oscillatory-kernel step of the angular Fourier calculations. -/
theorem MeasureTheory.Integrable.mul_unimodular {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f g : α → ℂ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1) :
    MeasureTheory.Integrable (fun x ↦ f x * g x) μ := by
  simpa only [mul_comm] using hf.bdd_mul hg hbound

namespace LeanRidgelet.Fourier

variable {m : ℕ}

theorem two_mul_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by positivity

theorem two_mul_pi_complex_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp [Real.pi_ne_zero]

theorem conj_two_mul_pi_inv :
    (starRingEnd ℂ) ((2 * Real.pi : ℂ)⁻¹) = (2 * Real.pi : ℂ)⁻¹ := by
  rw [map_inv₀]
  congr 1
  rw [map_mul, Complex.conj_ofNat, Complex.conj_ofReal]

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The manuscript Fourier integral on an arbitrary finite-dimensional real inner-product space. -/
def angularFourierIntegralInner (f : V → ℂ) (ξ : V) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) * f x

theorem angularFourierIntegralInner_eq_mathlib (f : V → ℂ) (ξ : V) :
    angularFourierIntegralInner f ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ V) f ((2 * Real.pi)⁻¹ • ξ) := by
  unfold angularFourierIntegralInner VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
  congr 2
  rw [map_smul]
  simp only [smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero]
  simp only [innerₗ_apply_apply]

/-- Plancherel normalization for the manuscript Fourier convention on any finite-dimensional
real inner-product space. -/
theorem angular_plancherel_schwartz_inner (f : SchwartzMap V ℂ) :
    ∫ ξ, ‖angularFourierIntegralInner f ξ‖ ^ 2 =
      (2 * Real.pi) ^ Module.finrank ℝ V * ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [angularFourierIntegralInner_eq_mathlib]
  change
    (∫ ξ, ‖𝓕 (f : V → ℂ) ((2 * Real.pi)⁻¹ • ξ)‖ ^ 2) =
      (2 * Real.pi) ^ Module.finrank ℝ V * ∫ x, ‖f x‖ ^ 2
  rw [Measure.integral_comp_inv_smul volume
    (fun ξ : V ↦ ‖𝓕 (f : V → ℂ) ξ‖ ^ 2) (2 * Real.pi)]
  rw [abs_of_nonneg (pow_nonneg (by positivity) _)]
  rw [← SchwartzMap.fourier_coe]
  exact congrArg ((2 * Real.pi) ^ Module.finrank ℝ V * ·)
    (SchwartzMap.integral_norm_sq_fourier f)

end FiniteDimensional

/-- The phase occurring in the Fourier convention of the L2 ridgelet manuscript. -/
def angularPhase (x ξ : InputSpace m) : ℂ :=
  Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ))

@[simp]
theorem angularPhase_zero_right (x : InputSpace m) : angularPhase x 0 = 1 := by
  simp [angularPhase]

@[simp]
theorem angularPhase_zero_left (ξ : InputSpace m) : angularPhase 0 ξ = 1 := by
  simp [angularPhase]

theorem norm_angularPhase (x ξ : InputSpace m) : ‖angularPhase x ξ‖ = 1 := by
  rw [angularPhase, Complex.norm_exp]
  simp

theorem continuous_angularPhase_left (ξ : InputSpace m) :
    Continuous (fun x => angularPhase x ξ) := by
  unfold angularPhase
  fun_prop

/-- The non-unitarily normalized Fourier integral used in the manuscript. -/
def angularFourierIntegral (f : InputSpace m → ℂ) (ξ : InputSpace m) : ℂ :=
  ∫ x, angularPhase x ξ * f x

@[simp]
theorem angularFourierIntegral_zero :
    angularFourierIntegral (fun _ : InputSpace m => 0) = 0 := by
  funext ξ
  simp [angularFourierIntegral]

theorem angularFourierIntegral_add {f g : InputSpace m → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    angularFourierIntegral (f + g) = angularFourierIntegral f + angularFourierIntegral g := by
  funext ξ
  simp only [angularFourierIntegral, Pi.add_apply, mul_add]
  rw [integral_add]
  · apply hf.bdd_mul
    · exact (continuous_angularPhase_left ξ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by rw [norm_angularPhase]
  · apply hg.bdd_mul
    · exact (continuous_angularPhase_left ξ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by rw [norm_angularPhase]

theorem angularFourierIntegral_smul (c : ℂ) (f : InputSpace m → ℂ) :
    angularFourierIntegral (c • f) = c • angularFourierIntegral f := by
  funext ξ
  simp only [angularFourierIntegral, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [angularPhase]
  ring

/-- Frequency rescaling relating the angular-frequency convention to Mathlib's `2π` convention. -/
def toMathlibFrequency (ξ : InputSpace m) : InputSpace m :=
  (2 * Real.pi)⁻¹ • ξ

/-- Pointwise bridge from the angular Fourier integral to Mathlib's Fourier integral.

This is deliberately exposed as a named theorem with a placeholder proof, so subsequent work on
Fourier normalization can find it mechanically without depending on a bundled assumption object.
-/
theorem angularFourierIntegral_eq_mathlib (f : InputSpace m → ℂ) (ξ : InputSpace m) :
    angularFourierIntegral f ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ (InputSpace m)) f (toMathlibFrequency ξ) := by
  unfold angularFourierIntegral VectorFourier.fourierIntegral angularPhase toMathlibFrequency
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
  congr 2
  rw [map_smul]
  simp only [smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero]
  simp only [innerₗ_apply_apply]

/-- Plancherel normalization in the manuscript convention, first stated for Schwartz functions. -/
theorem angular_plancherel_schwartz (f : SchwartzMap (InputSpace m) ℂ) :
    ∫ ξ, ‖angularFourierIntegral f ξ‖ ^ 2 =
      (2 * Real.pi) ^ m * ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [angularFourierIntegral_eq_mathlib]
  change
    (∫ ξ, ‖𝓕 (f : InputSpace m → ℂ) ((2 * Real.pi)⁻¹ • ξ)‖ ^ 2) =
      (2 * Real.pi) ^ m * ∫ x, ‖f x‖ ^ 2
  rw [Measure.integral_comp_inv_smul volume
    (fun ξ : InputSpace m ↦ ‖𝓕 (f : InputSpace m → ℂ) ξ‖ ^ 2) (2 * Real.pi)]
  simp only [finrank_euclideanSpace_fin]
  rw [abs_of_nonneg (pow_nonneg (by positivity) m)]
  rw [← SchwartzMap.fourier_coe]
  exact congrArg ((2 * Real.pi) ^ m * ·) (SchwartzMap.integral_norm_sq_fourier f)

end LeanRidgelet.Fourier
