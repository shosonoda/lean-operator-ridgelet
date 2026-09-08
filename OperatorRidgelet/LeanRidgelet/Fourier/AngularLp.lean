-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Fourier/AngularLp.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.AngularDistribution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The angular Fourier transform on `L²(ℝ)`

The angular-frequency Fourier transform `f ↦ f♯` extends from the Schwartz class to a continuous
linear map on `L²(ℝ)` with `‖f♯‖ = √(2π) ‖f‖`.  This file performs the extension, proves
compatibility with the distributional angular Fourier transform, and derives injectivity.  It is
used to define the manuscript isometry coordinates of concrete activations such as `tanh` and
ReLU.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate FourierTransform
open FourierTransform MeasureTheory TemperedDistribution

namespace LeanRidgelet.Fourier

/-! ### The angular Fourier transform on `L²(ℝ)` -/

/-- The angular-frequency Schwartz Fourier transform, bundled as a continuous linear map. -/
def angularFourierSchwartzCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) ∘L
    FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)

@[simp]
theorem angularFourierSchwartzCLM_apply (f : SchwartzMap ℝ ℂ) :
    angularFourierSchwartzCLM f = angularFourierSchwartz f := rfl

/-- The `L²` norm of a one-dimensional Schwartz function as an integral. -/
theorem norm_schwartz_toLp_two_sq (g : SchwartzMap ℝ ℂ) :
    ‖g.toLp 2 volume‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume] with x hx
  rw [hx, inner_self_eq_norm_sq]

/-- Plancherel bound for the angular Schwartz transform in the `L²` norm. -/
theorem norm_toLp_angularFourierSchwartz_le (f : SchwartzMap ℝ ℂ) :
    ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L
        angularFourierSchwartzCLM).toLinearMap f‖ ≤
      Real.sqrt (2 * Real.pi) *
        ‖(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap f‖ := by
  have hsq : ‖(angularFourierSchwartz f).toLp 2 volume‖ ^ 2 =
      2 * Real.pi * ‖f.toLp 2 volume‖ ^ 2 := by
    rw [norm_schwartz_toLp_two_sq, norm_schwartz_toLp_two_sq]
    have hplancherel := angular_plancherel_schwartz_inner (V := ℝ) f
    rw [Module.finrank_self, pow_one] at hplancherel
    rw [← hplancherel]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [angularFourierSchwartz_eq_angularFourierIntegralInner]
  have hle : ‖(angularFourierSchwartz f).toLp 2 volume‖ =
      Real.sqrt (2 * Real.pi) * ‖f.toLp 2 volume‖ := by
    have h1 : (0 : ℝ) ≤ ‖(angularFourierSchwartz f).toLp 2 volume‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * ‖f.toLp 2 volume‖ := by positivity
    apply sq_eq_sq₀ h1 h2 |>.mp
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hsq]
  exact le_of_eq hle

/-- The angular Fourier transform on `L²(ℝ)`, extended from the Schwartz class by density. -/
def angularFourierLp : L2 ℝ volume →L[ℂ] L2 ℝ volume :=
  LinearMap.extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L angularFourierSchwartzCLM).toLinearMap
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

theorem denseRange_toLpCLM_toLinearMap :
    DenseRange (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

/-- The `L²` angular Fourier transform agrees with the Schwartz transform on the Schwartz class. -/
theorem angularFourierLp_toLp (f : SchwartzMap ℝ ℂ) :
    angularFourierLp (f.toLp 2 volume) = (angularFourierSchwartz f).toLp 2 volume := by
  have h := LinearMap.extendOfNorm_eq
    (f := (SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L angularFourierSchwartzCLM).toLinearMap)
    (e := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap)
    denseRange_toLpCLM_toLinearMap
    ⟨Real.sqrt (2 * Real.pi), norm_toLp_angularFourierSchwartz_le⟩ f
  simpa [angularFourierLp] using h

/-- The `L²` angular Fourier transform agrees with the distributional angular Fourier transform. -/
theorem toTemperedDistribution_angularFourierLp (f : L2 ℝ volume) :
    Lp.toTemperedDistributionCLM ℂ volume 2 (angularFourierLp f) =
      angularFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).induction_on f
    ?_ ?_
  · apply isClosed_eq
    · exact ((Lp.toTemperedDistributionCLM ℂ volume 2).comp angularFourierLp).continuous
    · exact (angularFourierDistribution.comp
        (Lp.toTemperedDistributionCLM ℂ volume 2)).continuous
  · intro g
    change Lp.toTemperedDistributionCLM ℂ volume 2 (angularFourierLp (g.toLp 2 volume)) =
      angularFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 (g.toLp 2 volume))
    rw [angularFourierLp_toLp]
    change Lp.toTemperedDistribution ((angularFourierSchwartz g).toLp 2 volume) =
      angularFourierDistribution (Lp.toTemperedDistribution (g.toLp 2 volume))
    rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
    exact (angularFourierDistribution_toTemperedDistributionCLM_eq g).symm

/-- The `L²` angular Fourier transform is injective. -/
theorem angularFourierLp_injective : Function.Injective angularFourierLp := by
  intro f g hfg
  have hdist : Lp.toTemperedDistributionCLM ℂ volume 2 f =
      Lp.toTemperedDistributionCLM ℂ volume 2 g := by
    have h1 := toTemperedDistribution_angularFourierLp f
    have h2 := toTemperedDistribution_angularFourierLp g
    have h3 : angularFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 f) =
        angularFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 g) := by
      rw [← h1, ← h2, hfg]
    have h4 := congrArg angularFourierInvDistribution h3
    rwa [angularFourierInvDistribution_angularFourierDistribution,
      angularFourierInvDistribution_angularFourierDistribution] at h4
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℝ)))
  exact hdist

end LeanRidgelet.Fourier
