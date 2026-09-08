-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/SchwartzAux.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Auxiliary lemmas on Schwartz functions and supports

Small general-purpose facts used when a Schwartz test function is required to avoid a point, or
when a linear rescaling of the frequency variable has to be recognized as a Schwartz-space
endomorphism.

## Main results

* `coe_iterate_schwartz_derivCLM`: iterating `SchwartzMap.derivCLM` computes `iteratedDeriv`.
* `iteratedDeriv_eq_zero_of_tsupport_subset_compl`: all derivatives of a Schwartz function
  supported away from a point vanish at that point.
* `exists_pos_le_abs_of_tsupport_subset`: a function supported away from the origin is
  uniformly separated from it.
* `MeasureTheory.integrable_mul_of_bound_on_tsupport`: multiplying an integrable function by a
  factor bounded on its support preserves integrability.
* `hasTemperateGrowth_const_mul`, `antilipschitzWith_const_mul`: the scaling `ζ ↦ c ζ` is of
  temperate growth and, for `c ≠ 0`, antilipschitz — the hypotheses of
  `SchwartzMap.compCLMOfAntilipschitz`.

All statements are Mathlib-only and are upstream candidates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

/-- The coercion of an iterated Schwartz derivative is the iterated derivative. -/
theorem coe_iterate_schwartz_derivCLM (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    ⇑((⇑(SchwartzMap.derivCLM ℂ ℂ))^[n] φ) = iteratedDeriv n (⇑φ) := by
  induction n generalizing φ with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, iteratedDeriv_succ', ih (SchwartzMap.derivCLM ℂ ℂ φ)]
    congr 1

/-- A Schwartz function supported away from the origin has all iterated derivatives vanishing
at the origin. -/
theorem iteratedDeriv_eq_zero_of_tsupport_subset_compl (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) (n : ℕ) : iteratedDeriv n (⇑φ) 0 = 0 := by
  have hmem : (0 : ℝ) ∈ (tsupport ⇑φ)ᶜ := fun h => hφ h rfl
  have h0 : ⇑φ =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [(isClosed_tsupport ⇑φ).isOpen_compl.mem_nhds hmem] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [Filter.EventuallyEq.iteratedDeriv_eq n h0]
  simp

/-- A test function supported away from the origin is uniformly separated from it. -/
theorem exists_pos_le_abs_of_tsupport_subset {g : ℝ → ℂ}
    (hg : tsupport g ⊆ {(0 : ℝ)}ᶜ) :
    ∃ δ > (0 : ℝ), ∀ ζ ∈ tsupport g, δ ≤ |ζ| := by
  have hmem : (0 : ℝ) ∈ (tsupport g)ᶜ := fun h => hg h rfl
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0 hmem
  refine ⟨δ, hδ, fun ζ hζ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hball (by simpa [Real.dist_eq] using hlt) hζ

theorem hasTemperateGrowth_const_mul (c : ℝ) :
    Function.HasTemperateGrowth (fun ζ : ℝ => c * ζ) := by
  have h := (c • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
  have heq : ⇑(c • ContinuousLinearMap.id ℝ ℝ) = fun ζ : ℝ => c * ζ := by
    funext ζ
    simp
  rwa [heq] at h

theorem antilipschitzWith_const_mul {c : ℝ} (hc : c ≠ 0) :
    AntilipschitzWith (Real.nnabs c⁻¹) (fun ζ : ℝ => c * ζ) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have hc' : (0 : ℝ) < |c| := abs_pos.mpr hc
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, Real.coe_nnabs, abs_inv,
    inv_mul_cancel_left₀ (ne_of_gt hc')]

namespace MeasureTheory

/-- Multiplying an integrable function by a factor bounded on its support preserves
integrability. -/
theorem integrable_mul_of_bound_on_tsupport {c g : ℝ → ℂ} {C : ℝ}
    (hc : AEStronglyMeasurable c volume) (hg : Integrable g volume)
    (hbound : ∀ ζ ∈ tsupport g, ‖c ζ‖ ≤ C) :
    Integrable (fun ζ => c ζ * g ζ) volume := by
  refine Integrable.mono' (hg.norm.const_mul C)
    (hc.mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun ζ => ?_)
  by_cases hζ : ζ ∈ tsupport g
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound ζ hζ) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hζ]
    simp

end MeasureTheory
