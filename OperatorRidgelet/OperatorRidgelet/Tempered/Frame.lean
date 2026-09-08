import OperatorRidgelet.Transform.Plancherel
import OperatorRidgelet.Reconstruction.Basic
import OperatorRidgelet.Tempered.Defs

/-!
# The cross frame identity on `𝒦`

For admissible filters `ρ₁, ρ₂` and `f ∈ 𝒦 = 𝓔_α`, the synthesis with `ρ₁` of the transform
with `ρ₂` is a multiple of the Riesz map:
`S_{ρ₁} R_{ρ₂} f = C^{(α)}_{ρ₂,ρ₁} J f` (`synthesis_ridgeletExtension_eq`).  On the image of the
core this is the Plancherel identity `⟨R_{ρ₂} f, R_{ρ₁} g⟩_{L²(λ)} = C^{(α)}_{ρ₂,ρ₁} ⟨f, g⟩_𝓔`
(`integral_ridgelet_mul_conj`), and both sides are continuous in `(f, g)`, so the identity
extends by density.  It is the instance `(ρ, β_ε)` of Theorem `thm:B`(i) used in the proof of
Theorem `thm:tempered-reconstruction`; the chosen extension `ridgeletExtension` is identified
with the extension by density `ridgeletExtensionCLM` (`ridgeletExtension_eq`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The chosen bounded extension of `R_ρ` is the extension by density. -/
theorem ridgeletExtension_eq (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) :
    ridgeletExtension μ ν ρ = ridgeletExtensionCLM hν hρ := by
  classical
  have hex : ∃ R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f :=
    ⟨_, coeFn_ridgeletExtensionCLM_embed hν hρ⟩
  rw [ridgeletExtension, dif_pos hex]
  exact eq_ridgeletExtensionCLM hν hρ _ hex.choose_spec

/-- The Riesz map on the image of the core is the spectral inner product. -/
theorem rieszMap_embed_embed (μ ν : Measure H) [IsFiniteMeasure μ] (f g : spectralCore μ ν) :
    rieszMap μ ν (spectralEmbed μ ν f) (spectralEmbed μ ν g) = spectralInner μ ν f g := by
  rw [rieszMap, innerSLFlip_apply_apply, Submodule.coe_inner, L2.inner_def, spectralInner]
  apply integral_congr_ae
  filter_upwards [f.2.coeFn_toLp, g.2.coeFn_toLp] with ξ h1 h2
  change inner ℂ (gaussFourierLp μ ν g ξ) (gaussFourierLp μ ν f ξ) =
    gaussFourier μ f ξ * (starRingEnd ℂ) (gaussFourier μ g ξ)
  rw [gaussFourierLp, gaussFourierLp, h1, h2, RCLike.inner_apply, mul_comm]

/-- The cross frame identity on the image of the core. -/
theorem synthesis_ridgeletExtension_embed (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) (f g : spectralCore μ ν) :
    synthesis μ ν ρ₁ (ridgeletExtension μ ν ρ₂ (spectralEmbed μ ν f)) (spectralEmbed μ ν g) =
      crossAdmissibilityConst α ρ₂ ρ₁ *
        rieszMap μ ν (spectralEmbed μ ν f) (spectralEmbed μ ν g) := by
  change inner ℂ (ridgeletExtension μ ν ρ₁ (spectralEmbed μ ν g))
    (ridgeletExtension μ ν ρ₂ (spectralEmbed μ ν f)) = _
  rw [ridgeletExtension_eq μ ν hν hρ₁, ridgeletExtension_eq μ ν hν hρ₂, L2.inner_def,
    rieszMap_embed_embed]
  have h := integral_ridgelet_mul_conj μ hν hρ₂ hρ₁
    ((Lp.memLp (f : Lp ℂ 2 μ)).integrable one_le_two) (Lp.memLp _)
    ((Lp.memLp (g : Lp ℂ 2 μ)).integrable one_le_two) (Lp.memLp _) f.2 g.2
  rw [← h]
  apply integral_congr_ae
  filter_upwards [coeFn_ridgeletExtensionCLM_embed hν hρ₁ g,
    coeFn_ridgeletExtensionCLM_embed hν hρ₂ f] with p h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- **The cross frame identity** `S_{ρ₁} R_{ρ₂} f = C^{(α)}_{ρ₂,ρ₁} J f` on `𝒦`. -/
theorem synthesis_ridgeletExtension_eq (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    {α : ℝ} (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ} (hρ₁ : IsAdmissible α ρ₁)
    (hρ₂ : IsAdmissible α ρ₂) (f : spectralRange μ ν) :
    synthesis μ ν ρ₁ (ridgeletExtension μ ν ρ₂ f) =
      crossAdmissibilityConst α ρ₂ ρ₁ • rieszMap μ ν f := by
  have hdense : DenseRange (Prod.map (spectralEmbedₗ μ ν) (spectralEmbedₗ μ ν)) :=
    (denseRange_spectralEmbedₗ μ ν).prodMap (denseRange_spectralEmbedₗ μ ν)
  have hΦ : Continuous fun p : spectralRange μ ν × spectralRange μ ν =>
      inner ℂ (ridgeletExtension μ ν ρ₁ p.2) (ridgeletExtension μ ν ρ₂ p.1) :=
    ((ridgeletExtension μ ν ρ₁).continuous.comp continuous_snd).inner
      ((ridgeletExtension μ ν ρ₂).continuous.comp continuous_fst)
  have hΨ : Continuous fun p : spectralRange μ ν × spectralRange μ ν =>
      crossAdmissibilityConst α ρ₂ ρ₁ * inner ℂ p.2 p.1 :=
    continuous_const.mul (continuous_snd.inner continuous_fst)
  have heq := hdense.equalizer hΦ hΨ (by
    funext p
    simp only [Function.comp_apply]
    have := synthesis_ridgeletExtension_embed μ ν hν hρ₁ hρ₂ p.1 p.2
    rw [rieszMap, innerSLFlip_apply_apply] at this
    exact this)
  ext g
  have := congrFun heq (f, g)
  simp only at this
  change inner ℂ (ridgeletExtension μ ν ρ₁ g) (ridgeletExtension μ ν ρ₂ f) = _ at this
  rw [smul_apply, smul_eq_mul, rieszMap, innerSLFlip_apply_apply]
  exact this

end OperatorRidgelet
