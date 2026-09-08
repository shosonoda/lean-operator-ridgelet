-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Activation/ReLU.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Activation

/-!
# Rectified-linear-unit activation

This file realizes the classical rectified linear unit as an activation coordinate in `A_{0,t}`.
The condition `3 / 2 < t` makes `⟨x⟩⁻ᵗ max x 0` square-integrable, and the manuscript isometry
coordinate of ReLU is its angular Fourier transform: `σ = ⟨∂ω⟩^{-t}[relu♯] = (⟨·⟩⁻ᵗ relu)♯`.
The pairing-consistent classical realization `activationRealization` then acts by integration
against the classical ReLU function.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

open Fourier

/-- The classical rectified linear unit. -/
def relu (x : ℝ) : ℝ :=
  max x 0

theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := by
  simp [relu]

theorem relu_le_norm (x : ℝ) : relu x ≤ ‖x‖ := by
  rw [Real.norm_eq_abs]
  exact max_le (le_abs_self x) (abs_nonneg x)

/-- The weighted `L²` coordinate associated with the classical rectified linear unit. -/
def reluWeightedFn (t : ℝ) (x : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow (-t) x * relu x)

theorem continuous_reluWeightedFn (t : ℝ) : Continuous (reluWeightedFn t) := by
  have hj : Continuous (japaneseBracketPow (-t) : ℝ → ℝ) := by
    unfold japaneseBracketPow
    apply Continuous.rpow_const
    · fun_prop
    · intro x
      left
      positivity
  have hreLU : Continuous relu := by
    unfold relu
    fun_prop
  exact Complex.continuous_ofReal.comp (hj.mul hreLU)

theorem memLp_reluWeightedFn (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    MemLp (reluWeightedFn t) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_reluWeightedFn t).aestronglyMeasurable).2
  apply (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := 2 * t - 2) (by simp; linarith)).mono'
  · exact (continuous_reluWeightedFn t).norm.pow 2 |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖reluWeightedFn t x‖)]
    simp only [reluWeightedFn, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (japaneseBracketPow_pos _ _),
      abs_of_nonneg (relu_nonneg x), mul_pow]
    calc
      japaneseBracketPow (-t) x ^ 2 * relu x ^ 2 ≤
          japaneseBracketPow (-t) x ^ 2 * japaneseBracketPow 1 x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [japaneseBracketPow_sq]
        unfold japaneseBracketPow
        norm_num [Real.rpow_one]
        have hsq : relu x ^ 2 ≤ ‖x‖ ^ 2 := by
          nlinarith [relu_nonneg x, relu_le_norm x, norm_nonneg x]
        have hnormsq : ‖x‖ ^ 2 = x ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
        nlinarith
      _ = (1 + ‖x‖ ^ 2) ^ (-(2 * t - 2) / 2) := by
        rw [japaneseBracketPow_sq, japaneseBracketPow_sq, ← japaneseBracketPow_add]
        unfold japaneseBracketPow
        rw [show (2 * -t + 2 * 1) / 2 = -(2 * t - 2) / 2 by ring]

/-- The weighted `L²` element `⟨x⟩⁻ᵗ relu x`, the angular inverse-Fourier side of the ReLU
activation coordinate. -/
def reluWeightedCoordinate (t : ℝ) (ht : (3 : ℝ) / 2 < t) : L2 ℝ volume :=
  (memLp_reluWeightedFn t ht).toLp (reluWeightedFn t)

theorem reluWeightedCoordinate_coe_ae (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    reluWeightedCoordinate t ht =ᵐ[volume] reluWeightedFn t :=
  (memLp_reluWeightedFn t ht).coeFn_toLp

theorem reluWeightedCoordinate_ne_zero (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    reluWeightedCoordinate t ht ≠ 0 := by
  intro hσ
  have hzero : reluWeightedCoordinate t ht =ᵐ[volume] (0 : ℝ → ℂ) :=
    Lp.eq_zero_iff_ae_eq_zero.mp hσ
  have hae : reluWeightedFn t =ᵐ[volume] (0 : ℝ → ℂ) :=
    (reluWeightedCoordinate_coe_ae t ht).symm.trans hzero
  have hfun : reluWeightedFn t = 0 :=
    (Continuous.ae_eq_iff_eq volume (continuous_reluWeightedFn t) continuous_zero).mp hae
  have hvalue := congrFun hfun 1
  have hweight : japaneseBracketPow (-t) (1 : ℝ) ≠ 0 :=
    (japaneseBracketPow_pos (-t) 1).ne'
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hweight (by norm_num [relu])) hvalue

/-- The rectified linear unit as an activation coordinate in `A_{0,t}`: the manuscript isometry
coordinate `⟨∂ω⟩^{-t}[relu♯] = (⟨·⟩⁻ᵗ relu)♯`, i.e. the angular Fourier transform of the
weighted `L²` element. -/
def reluActivation (t : ℝ) (ht : (3 : ℝ) / 2 < t) : ActivationSpace 0 t :=
  angularFourierLp (reluWeightedCoordinate t ht)

theorem reluActivation_ne_zero (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    reluActivation t ht ≠ 0 := by
  intro hσ
  apply reluWeightedCoordinate_ne_zero t ht
  apply angularFourierLp_injective
  rw [map_zero]
  exact hσ

/-- The pairing-consistent tempered-distribution realization of the rectified linear unit,
`σ = 𝓕⁻¹_ang[σ♯]`. -/
def reluTemperedDistribution (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    TemperedDistribution ℝ ℂ :=
  activationRealization 0 t (reluActivation t ht)

/-- The realized ReLU activation is the weighted distribution `⟨x⟩ᵗ ⟨x⟩⁻ᵗ relu`. -/
theorem reluTemperedDistribution_eq_weight (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    reluTemperedDistribution t ht =
      temperedWeightMultiplier t
        (Lp.toTemperedDistributionCLM ℂ volume 2 (reluWeightedCoordinate t ht)) :=
  activationRealization_zero_angularFourierLp t (reluWeightedCoordinate t ht)

/-- The distribution realization acts by integration against the classical ReLU function. -/
theorem reluTemperedDistribution_apply (t : ℝ) (ht : (3 : ℝ) / 2 < t)
    (g : SchwartzMap ℝ ℂ) :
    reluTemperedDistribution t ht g =
      ∫ x : ℝ, g x * Complex.ofReal (relu x) := by
  rw [reluTemperedDistribution_eq_weight]
  unfold temperedWeightMultiplier
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [reluWeightedCoordinate_coe_ae t ht] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight t), hx]
  change temperedWeight t x * g x * reluWeightedFn t x =
    g x * Complex.ofReal (relu x)
  rw [show temperedWeight t x * g x * reluWeightedFn t x =
    g x * (temperedWeight t x * reluWeightedFn t x) by ring]
  congr 1
  unfold reluWeightedFn temperedWeight
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, ← japaneseBracketPow_add]
  simp

/-- The realized ReLU activation lies in `A_{0,t} = ⟨·⟩ᵗ H⁰(ℝ)`. -/
theorem memActivationSpace_reluTemperedDistribution (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    MemActivationSpace 0 t (reluTemperedDistribution t ht) := by
  refine ⟨reluWeightedCoordinate t ht, ?_⟩
  rw [angularBesselPotential_zero_apply, reluTemperedDistribution_eq_weight]
  unfold temperedWeightMultiplier
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_temperedWeight t) (hasTemperateGrowth_temperedWeight (-t))]
  rw [temperedWeight_mul_neg]
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ ↦ (1 : ℂ)) _ = _
  simp

end LeanRidgelet
