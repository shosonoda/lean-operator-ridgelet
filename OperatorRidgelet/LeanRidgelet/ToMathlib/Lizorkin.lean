-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/Lizorkin.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The Lizorkin space and Lizorkin distributions

The Lizorkin dual `𝒮₀'(ℝ)` consists of the tempered distributions modulo polynomials: a point
mass `δ^{(j)}` at the origin of the frequency line — equivalently a polynomial summand of a
function on the space side — is invisible to it. This file introduces the test-function side of
that duality as a type.

Mathlib has the Schwartz space and its Fourier theory but not the Lizorkin subspace, so these
declarations are upstream candidates.

## Main definitions and results

* `IsLizorkin`, `LizorkinSpace`: the **Lizorkin space** `𝒮₀(ℝ)`, the Schwartz functions all of
  whose moments vanish, as a submodule of `𝓢(ℝ, ℂ)`.
* `Real.iteratedDeriv_fourier_zero`: the moments of a Schwartz function are the derivatives of
  its Fourier transform at the origin, up to the factor `(-2πi)^n`.
* `mem_lizorkinSpace_iff_fourier_flat`: the **Fourier characterization** — a Schwartz function
  is Lizorkin exactly when its Fourier transform vanishes to infinite order at the origin.
* `integral_polynomial_mul_eq_zero_of_mem_lizorkinSpace`: **polynomials annihilate the Lizorkin
  space**.
* `LizorkinDistribution`: the **Lizorkin distributions** `𝒮₀'(ℝ)`, the continuous linear
  functionals on `𝒮₀(ℝ)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- A Schwartz function is a **Lizorkin test function** when all of its moments vanish. -/
def IsLizorkin (φ : SchwartzMap ℝ ℂ) : Prop :=
  ∀ n : ℕ, (∫ z : ℝ, (z : ℂ) ^ n * φ z) = 0

/-- Integrability of the moment integrands of a Schwartz function. -/
theorem integrable_pow_smul_schwartz (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun z : ℝ => (z : ℂ) ^ n * φ z) volume := by
  have h := φ.integrable_pow_mul volume n
  refine Integrable.mono' h ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((Complex.continuous_ofReal.pow n).mul φ.continuous).aestronglyMeasurable
  · simp

/-- The **Lizorkin space** `𝒮₀(ℝ)`: the Schwartz functions all of whose moments vanish. Its
annihilator contains every polynomial, which is why the Lizorkin dual `𝒮₀'(ℝ)` sees tempered
distributions only modulo polynomials. -/
def LizorkinSpace : Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {φ | IsLizorkin φ}
  add_mem' := by
    intro φ ψ hφ hψ n
    have h : (∫ z : ℝ, (z : ℂ) ^ n * (φ + ψ) z)
        = (∫ z : ℝ, (z : ℂ) ^ n * φ z) + ∫ z : ℝ, (z : ℂ) ^ n * ψ z := by
      rw [← integral_add (integrable_pow_smul_schwartz φ n) (integrable_pow_smul_schwartz ψ n)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [add_apply]
      ring
    rw [h, hφ n, hψ n, add_zero]
  zero_mem' := by
    intro n
    simp
  smul_mem' := by
    intro c φ hφ n
    have h : (∫ z : ℝ, (z : ℂ) ^ n * (c • φ) z) = c * ∫ z : ℝ, (z : ℂ) ^ n * φ z := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [smul_apply, smul_eq_mul]
      ring
    rw [h, hφ n, mul_zero]

theorem mem_lizorkinSpace_iff {φ : SchwartzMap ℝ ℂ} :
    φ ∈ LizorkinSpace ↔ ∀ n : ℕ, (∫ z : ℝ, (z : ℂ) ^ n * φ z) = 0 := Iff.rfl

/-- The Fourier transform at the origin is the total integral. -/
theorem Real.fourier_apply_zero (g : ℝ → ℂ) : 𝓕 g 0 = ∫ z : ℝ, g z := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp

/-- The moments of a Schwartz function are the derivatives of its Fourier transform at the
origin. -/
theorem Real.iteratedDeriv_fourier_zero (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    iteratedDeriv n (𝓕 (⇑φ)) 0
      = (-2 * (Real.pi : ℂ) * Complex.I) ^ n * ∫ z : ℝ, (z : ℂ) ^ n * φ z := by
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (fun z : ℝ => z ^ k • (φ z)) volume := by
    intro k _
    refine (integrable_pow_smul_schwartz φ k).congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.real_smul]
  have h := Real.iteratedDeriv_fourier (f := (⇑φ)) (N := (⊤ : ℕ∞)) (n := n)
    (fun k hk => hint k hk) le_top
  rw [h, Real.fourier_apply_zero, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  ring

/-- **Fourier characterization of the Lizorkin space**: a Schwartz function has all moments
vanishing exactly when its Fourier transform vanishes to infinite order at the origin. -/
theorem mem_lizorkinSpace_iff_fourier_flat {φ : SchwartzMap ℝ ℂ} :
    φ ∈ LizorkinSpace ↔ ∀ n : ℕ, iteratedDeriv n (𝓕 (⇑φ)) 0 = 0 := by
  constructor
  · intro hφ n
    rw [Real.iteratedDeriv_fourier_zero φ n, hφ n, mul_zero]
  · intro hφ n
    have hne : ((-2 * (Real.pi : ℂ) * Complex.I) ^ n) ≠ 0 := by
      refine pow_ne_zero _ ?_
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, neg_eq_zero,
        OfNat.ofNat_ne_zero, false_or]
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h := Real.iteratedDeriv_fourier_zero φ n
    rw [hφ n] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne


/-- **Polynomials annihilate the Lizorkin space.** This is the precise form of the statement
that a point mass `δ^{(j)}` at the origin — equivalently a polynomial summand on the space side
— is invisible to a Lizorkin distribution. -/
theorem integral_polynomial_mul_eq_zero_of_mem_lizorkinSpace {φ : SchwartzMap ℝ ℂ}
    (hφ : φ ∈ LizorkinSpace) (Q : Polynomial ℂ) :
    (∫ z : ℝ, Q.eval (z : ℂ) * φ z) = 0 := by
  have hpt : ∀ z : ℝ, Q.eval (z : ℂ) * φ z
      = ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * ((z : ℂ) ^ i * φ z) := by
    intro z
    rw [Q.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [show (∫ z : ℝ, Q.eval (z : ℂ) * φ z)
      = ∫ z : ℝ, ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * ((z : ℂ) ^ i * φ z) from
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun i _ => ((integrable_pow_smul_schwartz φ i).const_mul _))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, hφ i, mul_zero]

/-- The **Lizorkin distributions** `𝒮₀'(ℝ)`: the continuous linear functionals on the Lizorkin
space. Restricting a tempered distribution to `𝒮₀(ℝ)` forgets exactly its polynomial part, by
`integral_polynomial_mul_eq_zero_of_mem_lizorkinSpace`. -/
abbrev LizorkinDistribution := LizorkinSpace →L[ℂ] ℂ
