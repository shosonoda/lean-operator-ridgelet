-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/ToMathlib/FourierPlancherel.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Plancherel's theorem on `L¹ ∩ L²`

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` provides the Fourier transform on `L²` of a
finite-dimensional real inner product space as a linear isometry equivalence, together with its
compatibility with the Schwartz and tempered-distribution Fourier transforms. What the pinned
version does not provide is the classical bridge: on `L¹ ∩ L²` the abstract `L²` Fourier
transform is computed by the Fourier integral. This file proves that bridge and the resulting
Plancherel identities for the Fourier integral.

## Main results

* `MeasureTheory.Integrable.fourier_toLp_ae_eq`: for `f ∈ L¹ ∩ L²`, the `L²` Fourier transform
  of (the class of) `f` has the Fourier integral `𝓕 f` as an almost-everywhere representative.
* `MeasureTheory.Integrable.memLp_fourier`: for `f ∈ L¹ ∩ L²`, the Fourier integral `𝓕 f` is
  square-integrable.
* `MeasureTheory.Integrable.integral_norm_fourier_sq` (**Plancherel's theorem on `L¹ ∩ L²`**):
  `∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx`, together with the `lintegral` version
  `MeasureTheory.Integrable.lintegral_enorm_fourier_sq`.

The proof of the bridge pairs the `L²` Fourier transform against Schwartz functions through
`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`, rewrites the pairing with the
self-adjointness of the Fourier integral
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`), and identifies the two locally
integrable representatives with `ae_eq_of_integral_contDiff_smul_eq`.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ComplexConjugate ENNReal RealInnerProductSpace

namespace MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem innerₗ_flip_eq : (innerₗ E).flip = innerₗ E := by
  ext x y
  simp only [LinearMap.flip_apply, innerₗ_apply_apply]
  exact real_inner_comm x y

/-- An element of `L²` that pairs with every Schwartz function like a locally integrable
function is almost everywhere equal to that function. -/
theorem Lp.ae_eq_of_forall_schwartz_integral_smul_eq {u : Lp F 2 volume} {g : E → F}
    (hg : LocallyIntegrable g volume)
    (h : ∀ φ : 𝓢(E, ℂ), (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x) :
    ⇑u =ᵐ[volume] g := by
  have hu : LocallyIntegrable (⇑u) volume := (Lp.memLp u).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hu hg fun r r_diff r_supp => ?_
  have hr₁ : HasCompactSupport (Complex.ofRealCLM ∘ r) := r_supp.comp_left rfl
  have hr₂ := Complex.ofRealCLM.contDiff.comp r_diff
  have hpair := h (hr₁.toSchwartzMap hr₂)
  rw [Lp.toTemperedDistribution_apply] at hpair
  have hval : ∀ (v : E → F) (x : E),
      (hr₁.toSchwartzMap hr₂) x • v x = r x • v x := fun v x => by
    change ((r x : ℝ) : ℂ) • v x = r x • v x
    simp
  calc ∫ x, r x • u x
      = ∫ x, (hr₁.toSchwartzMap hr₂) x • u x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hval (⇑u) x).symm)
    _ = ∫ x, (hr₁.toSchwartzMap hr₂) x • g x := hpair
    _ = ∫ x, r x • g x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hval g x)

/-- On `L¹ ∩ L²`, the `L²` Fourier transform is computed by the Fourier integral: the
Fourier integral `𝓕 f` is an almost-everywhere representative of `𝓕` applied to the `L²`
class of `f`. -/
theorem Integrable.fourier_toLp_ae_eq {f : E → F} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    ⇑(𝓕 (h2.toLp f) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  refine Lp.ae_eq_of_forall_schwartz_integral_smul_eq hc.locallyIntegrable fun φ => ?_
  have h1 : ((𝓕 (h2.toLp f) : Lp F 2 volume) : 𝓢'(E, F)) φ
      = ((h2.toLp f : Lp F 2 volume) : 𝓢'(E, F)) (𝓕 φ) := by
    rw [← Lp.fourier_toTemperedDistribution_eq]
    rfl
  rw [h1, Lp.toTemperedDistribution_apply]
  have h2' : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h2']
  have hmul := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ E) (μ := volume) (ν := volume)
    Real.continuous_fourierChar (by exact continuous_inner) φ.integrable hf
  rw [innerₗ_flip_eq] at hmul
  exact hmul

/-- On `L¹ ∩ L²`, the Fourier integral is square-integrable. -/
theorem Integrable.memLp_fourier {f : E → F} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (h2.toLp f) : Lp F 2 (volume : Measure E))).ae_eq
    (hf.fourier_toLp_ae_eq h2)

/-- **Plancherel's theorem on `L¹ ∩ L²`**, `lintegral` form:
`∫⁻ ‖𝓕 f ξ‖ₑ² dξ = ∫⁻ ‖f x‖ₑ² dx`. -/
theorem Integrable.lintegral_enorm_fourier_sq {f : E → F} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2 ∂(volume : Measure E) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(volume : Measure E) := by
  have he1 : eLpNorm (𝓕 f) 2 volume
      = eLpNorm (⇑(𝓕 (h2.toLp f) : Lp F 2 (volume : Measure E))) 2 volume :=
    (eLpNorm_congr_ae (hf.fourier_toLp_ae_eq h2)).symm
  have he2 : eLpNorm (⇑(h2.toLp f)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_congr_ae h2.coeFn_toLp
  have hnorm : eLpNorm (⇑(𝓕 (h2.toLp f) : Lp F 2 (volume : Measure E))) 2 volume
      = eLpNorm (⇑(h2.toLp f)) 2 volume := by
    have h := Lp.norm_fourier_eq (h2.toLp f)
    rw [Lp.norm_def, Lp.norm_def] at h
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp h
  have hkey : eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
    rw [he1, hnorm, he2]
  have hrw : ∀ v : E → F, eLpNorm v 2 volume
      = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂(volume : Measure E)) ^ ((1 : ℝ) / 2) := by
    intro v
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num [ENNReal.rpow_natCast]
  rw [hrw, hrw] at hkey
  have h2pos : (0 : ℝ) < 1 / 2 := by norm_num
  exact ENNReal.rpow_left_injective (ne_of_gt h2pos) hkey

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- The Bochner integral of a squared norm is the `toReal` of the corresponding `lintegral`;
both sides vanish together in the non-integrable case. -/
theorem integral_norm_sq_eq_toReal_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {v : α → F} (hv : AEStronglyMeasurable v μ) :
    ∫ x, ‖v x‖ ^ 2 ∂μ = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ).toReal := by
  have hm : AEStronglyMeasurable (fun x => ‖v x‖ ^ 2) μ := by
    exact hv.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => by positivity) hm]
  congr 1
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Plancherel's theorem on `L¹ ∩ L²`**: `∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx`. -/
theorem Integrable.integral_norm_fourier_sq {f : E → F} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 ∂(volume : Measure E) = ∫ x, ‖f x‖ ^ 2 ∂(volume : Measure E) := by
  rw [integral_norm_sq_eq_toReal_lintegral (hf.memLp_fourier h2).aestronglyMeasurable,
    integral_norm_sq_eq_toReal_lintegral h2.aestronglyMeasurable,
    hf.lintegral_enorm_fourier_sq h2]

/-- The pointwise product `u ⋅ conj v` of two square-integrable functions is integrable —
the scalar mul-conjugate form of `MeasureTheory.L2.integrable_inner`. -/
theorem MemLp.integrable_mul_conj {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hv.toLp v) (hu.toLp u)
  refine h.congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
  rw [RCLike.inner_apply, h1, h2]

/-- **Parseval's relation on `L¹ ∩ L²`**: the Fourier integral preserves pointwise inner
products of integrable square-integrable functions,
`∫ ⟪𝓕 f ξ, 𝓕 g ξ⟫ dξ = ∫ ⟪f x, g x⟫ dx`. Bridges the unitarity of the `L²` Fourier
transform (`MeasureTheory.Lp.fourierTransformₗᵢ`) to the Fourier integral through the
`L¹ ∩ L²` representation. -/
theorem Integrable.integral_inner_fourier {f g : E → F}
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    ∫ ξ, inner ℂ (𝓕 f ξ) (𝓕 g ξ) ∂(volume : Measure E)
      = ∫ x, inner ℂ (f x) (g x) ∂(volume : Measure E) := by
  have hFae : ⇑(𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕 f :=
    hf1.fourier_toLp_ae_eq hf2
  have hGae : ⇑(𝓕 (hg2.toLp g) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕 g :=
    hg1.fourier_toLp_ae_eq hg2
  calc ∫ ξ, inner ℂ (𝓕 f ξ) (𝓕 g ξ) ∂(volume : Measure E)
      = ∫ ξ, inner ℂ ((𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure E)) ξ)
          ((𝓕 (hg2.toLp g) : Lp F 2 (volume : Measure E)) ξ) ∂(volume : Measure E) := by
        refine integral_congr_ae ?_
        filter_upwards [hFae, hGae] with ξ h1 h2
        rw [h1, h2]
    _ = inner ℂ (𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure E)) (𝓕 (hg2.toLp g)) :=
        (L2.inner_def _ _).symm
    _ = inner ℂ (hf2.toLp f) (hg2.toLp g) :=
        LinearIsometryEquiv.inner_map_map (Lp.fourierTransformₗᵢ E F) _ _
    _ = ∫ x, inner ℂ (f x) (g x) ∂(volume : Measure E) := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x h1 h2
        rw [h1, h2]

/-- **Parseval's relation on `L¹ ∩ L²`**, scalar mul-conjugate form:
`∫ 𝓕 u ⋅ conj (𝓕 v) = ∫ u ⋅ conj v`. -/
theorem Integrable.integral_fourier_mul_conj_fourier {u v : E → ℂ}
    (hu1 : Integrable u volume) (hu2 : MemLp u 2 volume)
    (hv1 : Integrable v volume) (hv2 : MemLp v 2 volume) :
    ∫ ξ, 𝓕 u ξ * conj (𝓕 v ξ) ∂(volume : Measure E)
      = ∫ x, u x * conj (v x) ∂(volume : Measure E) := by
  have h := hu1.integral_inner_fourier hu2 hv1 hv2
  calc ∫ ξ, 𝓕 u ξ * conj (𝓕 v ξ) ∂(volume : Measure E)
      = ∫ ξ, conj (inner ℂ (𝓕 u ξ) (𝓕 v ξ)) ∂(volume : Measure E) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only []
        rw [RCLike.inner_apply, map_mul, RCLike.conj_conj]
        ring
    _ = conj (∫ ξ, inner ℂ (𝓕 u ξ) (𝓕 v ξ) ∂(volume : Measure E)) := integral_conj
    _ = conj (∫ x, inner ℂ (u x) (v x) ∂(volume : Measure E)) := by rw [h]
    _ = ∫ x, u x * conj (v x) ∂(volume : Measure E) := by
        rw [← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [RCLike.inner_apply, map_mul, RCLike.conj_conj]
        ring

end MeasureTheory
