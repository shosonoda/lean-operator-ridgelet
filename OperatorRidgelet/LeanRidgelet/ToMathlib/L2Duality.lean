-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/L2Duality.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cauchy--Schwarz and an `L²` duality criterion

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

## Main results

* `MeasureTheory.eLpNorm_two_eq_lintegral_enorm_sq`: the `L²` seminorm as the square root of the
  `lintegral` of the squared enorm, and `MeasureTheory.eLpNorm_two_sq_eq_lintegral_enorm_sq`: the
  same with the root cleared.
* `MeasureTheory.lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two` (**Cauchy--Schwarz for lower
  Lebesgue integrals**): `∫⁻ ‖u‖ₑ ‖v‖ₑ ≤ ‖u‖₂ ‖v‖₂`, with no integrability hypothesis and the two
  targets allowed to differ.
* `MeasureTheory.MemLp.norm_integral_mul_conj_le` (**Cauchy--Schwarz for Bochner integrals**):
  `‖∫ u ⋅ conj v‖ ≤ (∫ ‖u‖²)^{1/2} (∫ ‖v‖²)^{1/2}` for square-integrable `u`, `v`.
* `MeasureTheory.memLp_two_of_integrable_of_bound`: `L¹ ∩ L^∞ ⊆ L²` — an integrable function
  with a uniform bound is square-integrable.
* `MeasureTheory.MemLp.integrable_norm_sq`: `‖·‖²` is integrable for a square-integrable
  function.
* `MeasureTheory.eLpNorm_two_le_of_forall_indicator_pairing_le` (**`L²` duality criterion**): a
  measurable function whose pairings against its own truncations to an exhausting sequence of
  measurable sets are bounded by `M` times the `L²` norm of the truncation is itself in `L²`,
  with `‖h‖₂ ≤ M`. This is the standard device for turning a duality bound
  `|⟨h, g⟩| ≤ M ‖g‖₂` into a norm bound without knowing `h ∈ L²` beforehand: the truncations
  are square-integrable by construction, and monotone convergence transports the resulting
  uniform bound to `h`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

namespace MeasureTheory

/-- The `L²` seminorm is the square root of the `lintegral` of the squared enorm. -/
theorem eLpNorm_two_eq_lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] (g : α → E) :
    eLpNorm g 2 μ = (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num [ENNReal.rpow_natCast]


/-- The square of the `L²` seminorm is the lower Lebesgue integral of the squared enorm.  This is
`MeasureTheory.eLpNorm_two_eq_lintegral_enorm_sq` with the square root cleared, which is the form a
caller needs when an `L²` seminorm has to meet a `lintegral` identity. -/
theorem eLpNorm_two_sq_eq_lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : Type*} [NormedAddCommGroup F] (u : α → F) :
    eLpNorm u 2 μ ^ 2 = ∫⁻ a, ‖u a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_two_eq_lintegral_enorm_sq,
    ← ENNReal.rpow_natCast ((∫⁻ a, ‖u a‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Cauchy--Schwarz for lower Lebesgue integrals.**  The integral of a product of two enorms is at
most the product of the two `L²` seminorms.  This is Hölder's inequality at the conjugate pair
`(2, 2)`, stated for two possibly different targets so that it applies to a pairing of a scalar
coefficient against a vector-valued kernel. -/
theorem lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F G : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
    [OpensMeasurableSpace F] [NormedAddCommGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {u : α → F} {v : α → G} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ∫⁻ a, ‖u a‖ₑ * ‖v a‖ₑ ∂μ ≤ eLpNorm u 2 μ * eLpNorm v 2 μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hu.enorm hv.enorm
  simp only [Pi.mul_apply] at h
  refine h.trans_eq ?_
  rw [eLpNorm_two_eq_lintegral_enorm_sq, eLpNorm_two_eq_lintegral_enorm_sq]
  norm_num [ENNReal.rpow_natCast]

/-- **Cauchy--Schwarz inequality** for the Bochner integral of a product `u ⋅ conj v` of
square-integrable scalar functions. -/
theorem MemLp.norm_integral_mul_conj_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hofReal : ENNReal.ofReal (2 : ℝ) = 2 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have hnu : MemLp (fun x => ‖u x‖) (ENNReal.ofReal (2 : ℝ)) μ := by rw [hofReal]; exact hu.norm
  have hnv : MemLp (fun x => ‖v x‖) (ENNReal.ofReal (2 : ℝ)) μ := by rw [hofReal]; exact hv.norm
  have hsq : ∀ w : α → ℂ, (∫ x, ‖w x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖w x‖ ^ 2 ∂μ := by
    intro w
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖∫ x, u x * conj (v x) ∂μ‖
      ≤ ∫ x, ‖u x * conj (v x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖u x‖ * ‖v x‖ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖v x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg hpq
          (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (Filter.Eventually.of_forall fun x => norm_nonneg _) hnu hnv
    _ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) := by
        rw [hsq u, hsq v, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- Square-integrability of the squared norm of an `L²` function, in natural-power form. -/
theorem MemLp.integrable_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {g : α → E} (hg : MemLp g 2 μ) :
    Integrable (fun x => ‖g x‖ ^ 2) μ := by
  have h := hg.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **`L²` duality criterion.** If `h` is measurable, the sets `s n` are measurable, increasing
and exhaust the space, each truncation `1_{s n} h` is square-integrable, and the pairing of `h`
against every truncation is bounded by `M` times the `L²` norm of that truncation, then `h` is
square-integrable with `‖h‖₂ ≤ M`. -/
theorem eLpNorm_two_le_of_forall_indicator_pairing_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {h : α → ℂ} {M : ℝ} (hM : 0 ≤ M) (hh : AEStronglyMeasurable h μ)
    {s : ℕ → Set α} (hsm : ∀ n, MeasurableSet (s n)) (hsmono : Monotone s)
    (hsu : ∀ x, ∃ n, x ∈ s n)
    (hmem : ∀ n, MemLp (Set.indicator (s n) h) 2 μ)
    (hpair : ∀ n, ‖∫ x, h x * conj (Set.indicator (s n) h x) ∂μ‖
      ≤ M * Real.sqrt (∫ x, ‖Set.indicator (s n) h x‖ ^ 2 ∂μ)) :
    eLpNorm h 2 μ ≤ ENNReal.ofReal M := by
  classical
  set F : ℕ → α → ℝ≥0∞ := fun n x => Set.indicator (s n) (fun y => ‖h y‖ₑ ^ 2) x with hF_def
  -- each truncation obeys the `L²` bound `M`
  have hkey : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal (M ^ 2) := by
    intro n
    set g : α → ℂ := Set.indicator (s n) h with hg_def
    set t : ℝ := ∫ x, ‖g x‖ ^ 2 ∂μ with ht_def
    have ht0 : 0 ≤ t := integral_nonneg fun x => by positivity
    have hself : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.mul_conj', Complex.ofReal_pow]
    have hpt : ∀ x, h x * conj (g x) = ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      by_cases hx : x ∈ s n
      · rw [hg_def, Set.indicator_of_mem hx, hself]
      · rw [hg_def, Set.indicator_of_notMem hx, map_zero, mul_zero, norm_zero]
        norm_num
    have heq : (∫ x, h x * conj (g x) ∂μ) = ((t : ℝ) : ℂ) := by
      rw [ht_def, ← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    have hb := hpair n
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at hb
    -- the pairing bound `t ≤ M √t` gives `t ≤ M²`
    have htM : t ≤ M ^ 2 := by
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]
        positivity
      · have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
        have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
        nlinarith [hb]
    -- transport the bound to the `lintegral`
    have hlt : (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) = ENNReal.ofReal t := by
      rw [ht_def, ofReal_integral_eq_lintegral_ofReal (hmem n).integrable_norm_sq
        (Filter.Eventually.of_forall fun x => by positivity)]
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have hFn : (∫⁻ x, F n x ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ s n
      · simp [hF_def, hg_def, Set.indicator_of_mem hx]
      · simp [hF_def, hg_def, Set.indicator_of_notMem hx]
    rw [hFn, hlt]
    exact ENNReal.ofReal_le_ofReal htM
  -- monotone convergence over the exhausting sequence
  have hmeasF : ∀ n, AEMeasurable (F n) μ := fun n =>
    (hh.enorm.pow_const 2).indicator (hsm n)
  have hmono : ∀ᵐ x ∂μ, Monotone fun n => F n x := by
    refine Filter.Eventually.of_forall fun x => ?_
    intro i j hij
    exact Set.indicator_le_indicator_of_subset (hsmono hij) (fun _ => zero_le) x
  have hsup : ∀ x, ⨆ n, F n x = ‖h x‖ₑ ^ 2 := by
    intro x
    obtain ⟨n, hn⟩ := hsu x
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le n ?_)
    · exact Set.indicator_le_self' (fun _ _ => zero_le) x
    · rw [hF_def]
      simp only []
      rw [Set.indicator_of_mem hn]
  have hlint : (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ) ≤ ENNReal.ofReal (M ^ 2) := by
    calc (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ) = ∫⁻ x, ⨆ n, F n x ∂μ :=
          lintegral_congr fun x => (hsup x).symm
      _ = ⨆ n, ∫⁻ x, F n x ∂μ := lintegral_iSup' hmeasF hmono
      _ ≤ ENNReal.ofReal (M ^ 2) := iSup_le hkey
  rw [eLpNorm_two_eq_lintegral_enorm_sq]
  calc (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (M ^ 2)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hlint (by norm_num)
    _ = ENNReal.ofReal M := by
        rw [ENNReal.ofReal_pow hM, ← ENNReal.rpow_natCast (ENNReal.ofReal M) 2,
          ← ENNReal.rpow_mul]
        norm_num

/-- An integrable function with a uniform bound is square-integrable. -/
theorem memLp_two_of_integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℂ} (hint : Integrable h μ) {M : ℝ} (hbd : ∀ x, ‖h x‖ ≤ M) :
    MemLp h 2 μ := by
  refine ⟨hint.aestronglyMeasurable, ?_⟩
  have hrw : eLpNorm h 2 μ = (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num [ENNReal.rpow_natCast]
  rw [hrw]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hle : ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal M * ∫⁻ x, ‖h x‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ hint.aestronglyMeasurable.enorm]
    refine lintegral_mono fun x => ?_
    rw [pow_two]
    refine mul_le_mul' ?_ le_rfl
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hbd x)
  have hfin : (∫⁻ x, ‖h x‖ₑ ∂μ) < ∞ := hint.2
  exact (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)).ne

end MeasureTheory
