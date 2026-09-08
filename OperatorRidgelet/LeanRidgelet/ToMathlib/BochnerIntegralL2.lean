-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/BochnerIntegralL2.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise representatives of Bochner integrals in L²

This file identifies a Bochner integral of scalar `L²`-valued functions with the pointwise
integral of a family of representatives. The proof tests both functions on finite-measure sets,
commutes the resulting continuous `L²` inner-product functional with the Bochner integral, and then
applies Fubini. Since only finite-measure test sets enter, integrability of the family over the
slices `μ.prod (ν.restrict s)` suffices; the globally integrable statement is a corollary.

The Hölder bound that makes those slice hypotheses checkable is proved here as well: on a set of
finite measure an `L²` class is integrable, with `L¹` norm at most its `L²` norm times the square
root of the measure of the set.
-/
@[expose] public section

noncomputable section

open scoped ENNReal InnerProductSpace

namespace MeasureTheory

section Hoelder

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]

/-- Hölder's inequality for an `L²` class on a set of finite measure: the integral of the norm
over the set is bounded by the `L²` norm times the square root of the measure of the set.  In
particular the class is integrable there, which is what makes a slice hypothesis such as the one of
`MeasureTheory.integral_L2_coeFn_ae_of_restrict` verifiable. -/
theorem integral_norm_restrict_le_norm_mul_rpow (μ : Measure α) {s : Set α} (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) (h : Lp F 2 μ) :
    ∫ a in s, ‖(h : α → F) a‖ ∂μ ≤ ‖h‖ * (μ s).toReal ^ (2 : ℝ)⁻¹ := by
  have huniv : (μ.restrict s) Set.univ = μ s := by
    rw [Measure.restrict_apply' hs, Set.univ_inter]
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [huniv]; exact hfin.lt_top⟩
  have hmem : MemLp (h : α → F) 2 (μ.restrict s) := (Lp.memLp h).restrict s
  have hcalc : ENNReal.ofReal (∫ a in s, ‖(h : α → F) a‖ ∂μ) ≤
      ENNReal.ofReal ‖h‖ * μ s ^ (2 : ℝ)⁻¹ := by
    calc ENNReal.ofReal (∫ a in s, ‖(h : α → F) a‖ ∂μ)
        = eLpNorm (h : α → F) 1 (μ.restrict s) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          exact ofReal_integral_norm_eq_lintegral_enorm (hmem.integrable one_le_two)
      _ ≤ eLpNorm (h : α → F) 2 (μ.restrict s) *
            (μ.restrict s) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two hmem.aestronglyMeasurable
      _ = eLpNorm (h : α → F) 2 (μ.restrict s) * μ s ^ (2 : ℝ)⁻¹ := by
          rw [huniv]; norm_num
      _ ≤ ENNReal.ofReal ‖h‖ * μ s ^ (2 : ℝ)⁻¹ := by
          gcongr
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]
          exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hne : ENNReal.ofReal ‖h‖ * μ s ^ (2 : ℝ)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin)
  calc ∫ a in s, ‖(h : α → F) a‖ ∂μ
      = (ENNReal.ofReal (∫ a in s, ‖(h : α → F) a‖ ∂μ)).toReal :=
        (ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)).symm
    _ ≤ (ENNReal.ofReal ‖h‖ * μ s ^ (2 : ℝ)⁻¹).toReal := ENNReal.toReal_mono hne hcalc
    _ = ‖h‖ * (μ s).toReal ^ (2 : ℝ)⁻¹ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), ← ENNReal.toReal_rpow]

end Hoelder

/-- A Bochner integral in scalar `L²` has the pointwise iterated integral as an almost-everywhere
representative when the chosen two-variable representatives are integrable over every slice
`μ.prod (ν.restrict s)` with `ν s < ∞`.

This is the form in which the finite-measure test sets are used: equality is detected by
integrating over every measurable set of finite measure, using its indicator as an `L²` test
vector, and only integrability over that set is needed to commute the two integrals. The
almost-everywhere fin-strong measurability of the pointwise integral, which the slice hypothesis
cannot supply, is assumed separately. -/
theorem integral_L2_coeFn_ae_of_restrict_of_aefinStronglyMeasurable
    {α β 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β] [RCLike 𝕜]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {φ : α → Lp 𝕜 2 ν} {F : α → β → 𝕜}
    (hφ : Integrable φ μ)
    (hF : ∀ s : Set β, MeasurableSet s → ν s ≠ ∞ →
      Integrable (Function.uncurry F) (μ.prod (ν.restrict s)))
    (hmeas : AEFinStronglyMeasurable (fun b ↦ ∫ a, F a b ∂μ) ν)
    (hφF : ∀ᵐ a ∂μ, (φ a : β → 𝕜) =ᵐ[ν] F a) :
    ((∫ a, φ a ∂μ : Lp 𝕜 2 ν) : β → 𝕜) =ᵐ[ν] fun b ↦ ∫ a, F a b ∂μ := by
  let I : Lp 𝕜 2 ν := ∫ a, φ a ∂μ
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq
      (f := fun b ↦ I b) (g := fun b ↦ ∫ a, F a b ∂μ)
  · intro s _ hνs
    exact integrableOn_Lp_of_measure_ne_top I fact_one_le_two_ennreal.elim hνs.ne
  · intro s hs hνs
    exact (hF s hs hνs.ne).integral_prod_right
  · intro s hs hνs
    let v : Lp 𝕜 2 ν := indicatorConstLp 2 hs hνs.ne (1 : 𝕜)
    have hinner : ∀ᵐ a ∂μ, ⟪v, φ a⟫_𝕜 = ∫ b in s, F a b ∂ν := by
      filter_upwards [hφF] with a ha
      rw [L2.inner_indicatorConstLp_one hs hνs.ne]
      exact integral_congr_ae (ae_restrict_of_ae ha)
    calc
      ∫ b in s, I b ∂ν = ⟪v, I⟫_𝕜 := (L2.inner_indicatorConstLp_one hs hνs.ne I).symm
      _ = ∫ a, ⟪v, φ a⟫_𝕜 ∂μ := ((innerSL 𝕜 v).integral_comp_comm hφ).symm
      _ = ∫ a, (∫ b in s, F a b ∂ν) ∂μ := integral_congr_ae hinner
      _ = ∫ b in s, (∫ a, F a b ∂μ) ∂ν := integral_integral_swap (hF s hs hνs.ne)
  · exact (Lp.finStronglyMeasurable I two_ne_zero
      ENNReal.coe_ne_top).aefinStronglyMeasurable
  · exact hmeas

/-- A Bochner integral in scalar `L²` has the pointwise iterated integral as an almost-everywhere
representative when the chosen two-variable representatives are integrable over every slice
`μ.prod (ν.restrict s)` with `ν s < ∞`.

Unlike `MeasureTheory.integral_L2_coeFn_ae`, the family `F` need not be integrable on all of
`μ.prod ν`, so a merely locally integrable pointwise integral is allowed; the price is that the
measurability of `fun b ↦ ∫ a, F a b ∂μ` must be assumed, and that `ν` must be σ-finite for that
measurability to give the fin-strong measurability the test-set criterion consumes. -/
theorem integral_L2_coeFn_ae_of_restrict
    {α β 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β] [RCLike 𝕜]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SigmaFinite ν]
    {φ : α → Lp 𝕜 2 ν} {F : α → β → 𝕜}
    (hφ : Integrable φ μ)
    (hF : ∀ s : Set β, MeasurableSet s → ν s ≠ ∞ →
      Integrable (Function.uncurry F) (μ.prod (ν.restrict s)))
    (hmeas : AEStronglyMeasurable (fun b ↦ ∫ a, F a b ∂μ) ν)
    (hφF : ∀ᵐ a ∂μ, (φ a : β → 𝕜) =ᵐ[ν] F a) :
    ((∫ a, φ a ∂μ : Lp 𝕜 2 ν) : β → 𝕜) =ᵐ[ν] fun b ↦ ∫ a, F a b ∂μ :=
  integral_L2_coeFn_ae_of_restrict_of_aefinStronglyMeasurable hφ hF
    ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk.finStronglyMeasurable ν, hmeas.ae_eq_mk⟩ hφF

theorem integral_L2_coeFn_ae
    {α β 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β] [RCLike 𝕜]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {φ : α → Lp 𝕜 2 ν} {F : α → β → 𝕜}
    (hφ : Integrable φ μ) (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (hφF : ∀ᵐ a ∂μ, (φ a : β → 𝕜) =ᵐ[ν] F a) :
    ((∫ a, φ a ∂μ : Lp 𝕜 2 ν) : β → 𝕜) =ᵐ[ν] fun b ↦ ∫ a, F a b ∂μ := by
  refine integral_L2_coeFn_ae_of_restrict_of_aefinStronglyMeasurable hφ (fun s _ _ ↦ ?_)
    hF.integral_prod_right.aefinStronglyMeasurable hφF
  have heq : μ.prod (ν.restrict s) = (μ.prod ν).restrict (Set.univ ×ˢ s) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [heq]
  exact hF.restrict

end MeasureTheory
