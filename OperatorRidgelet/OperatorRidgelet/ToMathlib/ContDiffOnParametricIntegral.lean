import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import OperatorRidgelet.ToMathlib.IteratedDerivMeasurable

/-!
# Smoothness of a parametric integral on an open set with dominated derivatives

Mathlib differentiates under the integral sign once
(`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  Iterating it: if
`t ↦ f x t` is `C^∞` on an open set `U` for every `x`, the iterated derivatives are
almost-everywhere strongly measurable in `x` at every point of `U`, and every order of
derivative is dominated on `U` by an integrable function of `x`, then `t ↦ ∫ f x t ∂μ` is `C^∞`
on `U` and its iterated derivatives are the integrals of the iterated derivatives of the
integrand.

* `MeasureTheory.hasDerivAt_integral_iteratedDeriv`: one differentiation of
  `t ↦ ∫ iteratedDeriv k (f x) t ∂μ` at a point of `U`.
* `MeasureTheory.iteratedDeriv_integral_eq`: `∂ᵏ_t ∫ f x t ∂μ = ∫ ∂ᵏ_t f x t ∂μ` on `U`.
* `MeasureTheory.contDiffOn_integral_of_dominated`: `t ↦ ∫ f x t ∂μ` is `C^∞` on `U`.
-/

open Filter Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ → ℂ} {U : Set ℝ}

/-- **Differentiation under the integral sign**, one order at a time: at every point of the
open set `U`, `t ↦ ∫ ∂ᵏ_t f x t ∂μ` has derivative `∫ ∂ᵏ⁺¹_t f x t ∂μ`. -/
theorem hasDerivAt_integral_iteratedDeriv (hU : IsOpen U)
    (hf : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (f x) U)
    (hmeas : ∀ k : ℕ, ∀ t ∈ U, AEStronglyMeasurable (fun x => iteratedDeriv k (f x) t) μ)
    (hbound : ∀ k : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ x, ∀ t ∈ U, ‖iteratedDeriv k (f x) t‖ ≤ B x)
    (k : ℕ) {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun t => ∫ x, iteratedDeriv k (f x) t ∂μ)
      (∫ x, iteratedDeriv (k + 1) (f x) t ∂μ) t := by
  obtain ⟨B, hB, hBk⟩ := hbound (k + 1)
  obtain ⟨B₀, hB₀, hB₀k⟩ := hbound k
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := U)
    (F := fun t x => iteratedDeriv k (f x) t) (F' := fun t x => iteratedDeriv (k + 1) (f x) t)
    (bound := B) (hU.mem_nhds ht) ?_ ?_ (hmeas (k + 1) t ht) ?_ hB ?_
  · exact h.2
  · filter_upwards [hU.mem_nhds ht] with t' ht'
    exact hmeas k t' ht'
  · exact Integrable.mono' hB₀ (hmeas k t ht) (Eventually.of_forall fun x => hB₀k x t ht)
  · exact Eventually.of_forall fun x t' ht' => hBk x t' ht'
  · refine Eventually.of_forall fun x t' ht' => ?_
    have hs := (hf x).iteratedDeriv_of_isOpen hU k
    have hd : DifferentiableAt ℝ (iteratedDeriv k (f x)) t' :=
      (hs.contDiffAt (hU.mem_nhds ht')).differentiableAt (WithTop.coe_ne_zero.mpr ENat.top_ne_zero)
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt

/-- The iterated derivatives of a dominated parametric integral on an open set are the integrals
of the iterated derivatives. -/
theorem iteratedDeriv_integral_eq (hU : IsOpen U)
    (hf : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (f x) U)
    (hmeas : ∀ k : ℕ, ∀ t ∈ U, AEStronglyMeasurable (fun x => iteratedDeriv k (f x) t) μ)
    (hbound : ∀ k : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ x, ∀ t ∈ U, ‖iteratedDeriv k (f x) t‖ ≤ B x)
    (k : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv k (fun t => ∫ x, f x t ∂μ) t = ∫ x, iteratedDeriv k (f x) t ∂μ := by
  induction k generalizing t with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun t => ∫ x, f x t ∂μ) =ᶠ[𝓝 t]
        fun t => ∫ x, iteratedDeriv k (f x) t ∂μ := by
      filter_upwards [hU.mem_nhds ht] with t' ht'
      exact ih ht'
    rw [hev.deriv_eq]
    exact (hasDerivAt_integral_iteratedDeriv hU hf hmeas hbound k ht).deriv

/-- **Smoothness of a dominated parametric integral on an open set.** -/
theorem contDiffOn_integral_of_dominated (hU : IsOpen U)
    (hf : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (f x) U)
    (hmeas : ∀ k : ℕ, ∀ t ∈ U, AEStronglyMeasurable (fun x => iteratedDeriv k (f x) t) μ)
    (hbound : ∀ k : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ x, ∀ t ∈ U, ‖iteratedDeriv k (f x) t‖ ≤ B x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t => ∫ x, f x t ∂μ) U := by
  have key : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ n (fun t => ∫ x, iteratedDeriv k (f x) t ∂μ) U := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht =>
        (hasDerivAt_integral_iteratedDeriv hU hf hmeas hbound k ht).continuousAt.continuousWithinAt
    | succ n ih =>
      intro k
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun t ht => (hasDerivAt_integral_iteratedDeriv hU hf hmeas hbound k
        ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · refine (ih (k + 1)).congr fun t ht => ?_
        exact (hasDerivAt_integral_iteratedDeriv hU hf hmeas hbound k ht).deriv
  have h0 : (fun t => ∫ x, f x t ∂μ) = fun t => ∫ x, iteratedDeriv 0 (f x) t ∂μ := by
    simp only [iteratedDeriv_zero]
  rw [h0]
  exact contDiffOn_infty.mpr fun n => key n 0

end MeasureTheory
