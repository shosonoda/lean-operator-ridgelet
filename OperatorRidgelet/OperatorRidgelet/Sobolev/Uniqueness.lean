import OperatorRidgelet.Sobolev.Defs
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# `L¹` uniqueness of the ray profile

Two integrable rays with the same profile agree almost everywhere.  The proof is the
multiplication formula `∫ φ (γ̂) = ∫ (φ̂) γ` together with the fact that every real smooth
compactly supported function is a profile of an integrable function, so that the profiles
determine the ray as a distribution.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter
open scoped FourierTransform

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The integrand of the profile has the norm of the ray. -/
theorem norm_exp_smul (ω b : ℝ) (y : Y) :
    ‖Complex.exp ((-(ω * b) : ℝ) * Complex.I) • y‖ = ‖y‖ := by
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The profile integrand of an integrable ray is integrable. -/
theorem integrable_exp_smul {γ : ℝ → Y} (hγ : Integrable γ volume) (ω : ℝ) :
    Integrable (fun b : ℝ => Complex.exp ((-(ω * b) : ℝ) * Complex.I) • γ b) volume := by
  refine hγ.norm.mono' ?_ (Filter.Eventually.of_forall fun b => ?_)
  · exact ((by fun_prop : Continuous fun b : ℝ =>
      Complex.exp ((-(ω * b) : ℝ) * Complex.I)).aestronglyMeasurable).smul
      hγ.aestronglyMeasurable
  · rw [norm_exp_smul]

/-- The profile of an integrable ray is bounded by its `L¹` norm. -/
theorem norm_rayProfile_le {γ : ℝ → Y} (hγ : Integrable γ volume) (ω : ℝ) :
    ‖rayProfile γ ω‖ ≤ ∫ b : ℝ, ‖γ b‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall fun b => norm_exp_smul ω b (γ b))

/-- The profile of an integrable ray is continuous. -/
theorem continuous_rayProfile {γ : ℝ → Y} (hγ : Integrable γ volume) :
    Continuous (rayProfile γ) := by
  refine continuous_of_dominated (bound := fun b => ‖γ b‖) (fun ω => ?_) (fun ω => ?_) hγ.norm ?_
  · exact ((by fun_prop : Continuous fun b : ℝ =>
      Complex.exp ((-(ω * b) : ℝ) * Complex.I)).aestronglyMeasurable).smul
      hγ.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun b => le_of_eq (norm_exp_smul ω b (γ b))
  · exact Filter.Eventually.of_forall fun b => by fun_prop

/-- **The multiplication formula** for the ray profile: `∫ φ (γ̂) = ∫ (φ̂) γ`. -/
theorem integral_smul_rayProfile {γ : ℝ → Y} (hγ : Integrable γ volume) {φ : ℝ → ℂ}
    (hφ : Integrable φ volume) :
    ∫ ω : ℝ, φ ω • rayProfile γ ω = ∫ t : ℝ, rayProfile φ t • γ t := by
  have hK : Integrable
      (fun z : ℝ × ℝ => (φ z.1 * Complex.exp ((-(z.1 * z.2) : ℝ) * Complex.I)) • γ z.2)
      (volume.prod volume) := by
    have hbound : Integrable (fun z : ℝ × ℝ => ‖φ z.1‖ * ‖γ z.2‖) (volume.prod volume) :=
      MeasureTheory.Integrable.mul_prod hφ.norm hγ.norm
    refine hbound.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine AEStronglyMeasurable.smul ?_ ?_
      · exact (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst).mul
          (by fun_prop : Continuous fun z : ℝ × ℝ =>
            Complex.exp ((-(z.1 * z.2) : ℝ) * Complex.I)).aestronglyMeasurable
      · exact hγ.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
    · rw [norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hlhs : ∫ ω : ℝ, φ ω • rayProfile γ ω =
      ∫ ω : ℝ, ∫ t : ℝ, (φ ω * Complex.exp ((-(ω * t) : ℝ) * Complex.I)) • γ t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show φ ω • (∫ b : ℝ, Complex.exp ((-(ω * b) : ℝ) * Complex.I) • γ b) = _
    rw [← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only
      rw [smul_smul])
  have hrhs : ∫ t : ℝ, rayProfile φ t • γ t =
      ∫ t : ℝ, ∫ ω : ℝ, (φ ω * Complex.exp ((-(ω * t) : ℝ) * Complex.I)) • γ t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (∫ ω : ℝ, Complex.exp ((-(t * ω) : ℝ) * Complex.I) • φ ω) • γ t = _
    rw [← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [smul_eq_mul, mul_comm (Complex.exp ((-(t * ω) : ℝ) * Complex.I)) (φ ω), mul_comm t ω]
  rw [hlhs, hrhs]
  exact integral_integral_swap hK

/-- The ray profile is the Fourier integral in Mathlib's convention at the rescaled
frequency: `γ̂(ω) = 𝓕 γ (ω / 2π)`. -/
theorem rayProfile_eq_fourier (γ : ℝ → Y) (ω : ℝ) :
    rayProfile γ ω = 𝓕 γ (ω / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hexp : ((-(ω * b) : ℝ) : ℂ) * Complex.I =
      ((-2 * Real.pi * (inner ℝ b (ω / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I := by
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    rw [RCLike.inner_apply, conj_trivial]
    push_cast
    field_simp
  simp only
  rw [hexp]

/-- Every real smooth compactly supported function is the profile of an integrable function. -/
theorem exists_integrable_rayProfile_eq {g : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hcpt : HasCompactSupport g) :
    ∃ φ : ℝ → ℂ, Integrable φ volume ∧ ∀ t : ℝ, rayProfile φ t = (g t : ℂ) := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  set G : ℝ → ℂ := fun ξ => (g (2 * Real.pi * ξ) : ℂ) with hGdef
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    Complex.ofRealCLM.contDiff.comp (hsmooth.comp (contDiff_const.mul contDiff_id))
  have hcp : HasCompactSupport G := by
    have hhom : HasCompactSupport fun ξ : ℝ => g (2 * Real.pi * ξ) :=
      hcpt.comp_homeomorph (Homeomorph.mulLeft₀ (2 * Real.pi) h2pi)
    have hcomp : HasCompactSupport
        ((fun z : ℝ => (z : ℂ)) ∘ fun ξ : ℝ => g (2 * Real.pi * ξ)) :=
      hhom.comp_left (by simp)
    exact hcomp
  set S : SchwartzMap ℝ ℂ := hcp.toSchwartzMap hsm with hSdef
  have hScoe : ⇑S = G := rfl
  have hGint : Integrable G volume := by
    have h := S.integrable (μ := (volume : Measure ℝ))
    rwa [hScoe] at h
  have hFGint : Integrable (𝓕 G) volume := by
    have h := (𝓕 S : SchwartzMap ℝ ℂ).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourier_coe, hScoe] at h
  have hinvint : Integrable (𝓕⁻ G) volume := by
    have h := (𝓕⁻ S : SchwartzMap ℝ ℂ).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourierInv_coe, hScoe] at h
  refine ⟨𝓕⁻ G, hinvint, ?_⟩
  intro t
  have hFI : 𝓕 (𝓕⁻ G) = G := hsm.continuous.fourier_fourierInv_eq hGint hFGint
  rw [rayProfile_eq_fourier, hFI, hGdef]
  congr 2
  field_simp

/-- **`L¹` uniqueness of the ray profile**: two integrable rays with the same profile agree
almost everywhere. -/
theorem ae_eq_of_rayProfile_eq {γ δ : ℝ → Y} (hγ : Integrable γ volume)
    (hδ : Integrable δ volume) (h : ∀ ω : ℝ, rayProfile γ ω = rayProfile δ ω) :
    γ =ᵐ[volume] δ := by
  refine ae_eq_of_integral_contDiff_smul_eq hγ.locallyIntegrable hδ.locallyIntegrable ?_
  intro g hg_smooth hg_cpt
  obtain ⟨φ, hφ, hφg⟩ := exists_integrable_rayProfile_eq hg_smooth hg_cpt
  have hcast : ∀ u : ℝ → Y, ∫ t : ℝ, g t • u t = ∫ t : ℝ, rayProfile φ t • u t := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [hφg t, Complex.coe_smul]
  rw [hcast γ, hcast δ, ← integral_smul_rayProfile hγ hφ, ← integral_smul_rayProfile hδ hφ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
    simp only
    rw [h ω])

end OperatorRidgelet
