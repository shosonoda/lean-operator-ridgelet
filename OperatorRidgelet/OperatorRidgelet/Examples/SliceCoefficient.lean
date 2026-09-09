import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.GaussianMeasurability
import OperatorRidgelet.Transform.Plancherel
import Mathlib.Analysis.Fourier.Inversion

/-!
# The ridgelet coefficient as the explicit coefficient of its spectral density

For an integrable `f`, the bias function `c ↦ R_ρ f(a, c)` is continuous and integrable, its
Fourier transform is `ρ̂(ω) 𝒢_μ f(-ωa)` (the Fourier-slice identity, Lemma
`lem:fourier-slice`), and Fourier inversion gives `R_ρ f = γ_G` for `G = 𝒢_μ f`
(`eq:slice-as-coefficient`).  The lemmas here only assume that the coordinates `x ↦ ⟪x, v⟫`
are a.e.-measurable under `μ` (which holds under a centred Gaussian measure for any σ-algebra
on `H`, `IsCenteredGaussian.aemeasurable_inner`), so that they apply to the statements of
Section 7 that do not carry a `BorelSpace H` hypothesis.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace FourierTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  (μ : Measure H) [SFinite μ] (ρ : SchwartzMap ℝ ℝ)

section AEMeasurable

variable (hcoord : ∀ v : H, AEMeasurable (fun x => ⟪x, v⟫) μ)
include hcoord

omit [SFinite μ] in
/-- The ridge `x ↦ ρ(⟪a, x⟫ + c)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_ridge (a : H) (c : ℝ) :
    AEStronglyMeasurable (fun x : H => (ρ (⟪a, x⟫ + c) : ℂ)) μ := by
  have h : AEStronglyMeasurable (fun x : H => (ρ (⟪x, a⟫ + c) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (continuous_id.add continuous_const))).comp_aestronglyMeasurable
      (hcoord a).aestronglyMeasurable
  refine h.congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [real_inner_comm x a]

omit [SFinite μ] in
/-- The kernel `(x, c) ↦ f(x) ρ(⟪a, x⟫ + c)` is jointly integrable against `μ ⊗ dc`. -/
theorem integrable_ridgelet_kernel' {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Integrable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ)) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ))
      (μ.prod volume) := by
    refine (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul ?_
    have h1 : AEMeasurable (fun q : H × ℝ => ⟪a, q.1⟫ + q.2) (μ.prod volume) := by
      have h2 : AEMeasurable (fun q : H × ℝ => ⟪q.1, a⟫) (μ.prod volume) :=
        (hcoord a).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      refine (h2.add measurable_snd.aemeasurable).congr (Eventually.of_forall fun q => ?_)
      simp only [Pi.add_apply]
      first
      | rfl
      | rw [real_inner_comm q.1 a]
    exact (Complex.continuous_ofReal.comp ρ.continuous).comp_aestronglyMeasurable
      h1.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with x
    exact ((ρ.integrable.comp_add_left ⟪a, x⟫).ofReal (𝕜 := ℂ)).const_mul (f x)
  · have : (fun x => ∫ c : ℝ, ‖f x * (ρ (⟪a, x⟫ + c) : ℂ)‖) =
        fun x => ‖f x‖ * ∫ t : ℝ, ‖ρ t‖ := by
      funext x
      simp_rw [norm_mul, Complex.norm_real]
      rw [integral_const_mul, integral_add_left_eq_self (f := fun t => ‖ρ t‖) ⟪a, x⟫]
    rw [this]
    exact hf.norm.mul_const _

/-- The bias function `R_ρ f(a, ·)` is integrable. -/
theorem integrable_ridgelet_slice' {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Integrable (fun c : ℝ => ridgelet μ ρ f (a, c)) :=
  (integrable_ridgelet_kernel' μ ρ hcoord hf a).integral_prod_right

omit [SFinite μ] in
/-- The bias function `R_ρ f(a, ·)` is continuous. -/
theorem continuous_ridgelet_slice' {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Continuous fun c : ℝ => ridgelet μ ρ f (a, c) := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  unfold ridgelet
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hf.norm.mul_const C) ?_
  · intro c
    exact hf.aestronglyMeasurable.mul (aestronglyMeasurable_ridge μ ρ hcoord a c)
  · intro c
    filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hC.2 _) (norm_nonneg _)
  · filter_upwards with x
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (ρ.continuous.comp (continuous_const.add continuous_id)))

/-- The Fourier-slice identity `\widehat{R_ρ f}(a, ω) = ρ̂(ω) 𝒢_μ f(-ωa)`. -/
theorem biasFourier_ridgelet' {f : H → ℂ} (hf : Integrable f μ) (a : H) (ω : ℝ) :
    biasFourier (ridgelet μ ρ f) a ω = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
  have hF := integrable_ridgelet_kernel' μ ρ hcoord hf a
  have hF' : Integrable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ) *
      Complex.exp (-((ω * q.2 : ℝ) * Complex.I))) (μ.prod volume) := by
    refine hF.mul_unimodular ?_ (Eventually.of_forall fun q => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((ω * t : ℝ) * Complex.I))).comp_aestronglyMeasurable
        measurable_snd.aestronglyMeasurable
    · rw [show -((ω * q.2 : ℝ) * Complex.I) = ((-(ω * q.2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hchar : ∀ x : H, character (-(ω • a)) x =
      Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) := by
    intro x
    simp only [character, inner_neg_right, inner_smul_right, real_inner_comm a x]
    push_cast
    ring_nf
  unfold biasFourier
  calc ∫ c : ℝ, ridgelet μ ρ f (a, c) * Complex.exp (-((ω * c : ℝ) * Complex.I))
      = ∫ c : ℝ, (∫ x, f x * (ρ (⟪a, x⟫ + c) : ℂ) *
          Complex.exp (-((ω * c : ℝ) * Complex.I)) ∂μ) := by
        congr 1
        funext c
        unfold ridgelet
        rw [← integral_mul_const]
    _ = ∫ x, (∫ c : ℝ, f x * (ρ (⟪a, x⟫ + c) : ℂ) *
          Complex.exp (-((ω * c : ℝ) * Complex.I))) ∂μ :=
        (integral_integral_swap hF').symm
    _ = ∫ x, (f x * character (-(ω • a)) x) * filterFourier ρ ω ∂μ := by
        congr 1
        funext x
        have hkey : (fun c : ℝ => f x * (ρ (⟪a, x⟫ + c) : ℂ) *
            Complex.exp (-((ω * c : ℝ) * Complex.I))) =
            fun c : ℝ => (f x * character (-(ω • a)) x) *
              ((fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))
                (⟪a, x⟫ + c)) := by
          funext c
          rw [hchar]
          have hexp : Complex.exp (-((ω * c : ℝ) * Complex.I)) =
              Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-Complex.I * ((inner ℝ (⟪a, x⟫ + c) ω : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            simp only [RCLike.inner_apply, conj_trivial]
            push_cast
            ring
          rw [hexp]
          ring
        rw [hkey, integral_const_mul, integral_add_left_eq_self
          (f := fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))]
        rfl
    _ = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
        rw [integral_mul_const, mul_comm]
        rfl

/-- Mathlib's Fourier transform of the bias function is the Fourier slice at frequency
`2πu`. -/
theorem fourier_ridgelet_slice' {f : H → ℂ} (hf : Integrable f μ) (a : H) (u : ℝ) :
    𝓕 (fun c => ridgelet μ ρ f (a, c)) u =
      filterFourier ρ (2 * Real.pi * u) * gaussFourier μ f (-((2 * Real.pi * u) • a)) := by
  rw [fourier_bias_eq, biasFourier_ridgelet' μ ρ hcoord hf]

omit [SFinite μ] in
/-- The characters `x ↦ e^{-i⟪x,ξ⟫}` are a.e. strongly measurable. -/
theorem aestronglyMeasurable_character' (ξ : H) : AEStronglyMeasurable (character ξ) μ := by
  have h := (by fun_prop :
    Continuous fun t : ℝ => Complex.exp (-((t : ℂ) * Complex.I))).comp_aestronglyMeasurable
    (hcoord ξ).aestronglyMeasurable
  exact h

omit [SFinite μ] in
/-- `𝒢_μ f` is continuous for integrable `f`. -/
theorem continuous_gaussFourier' {f : H → ℂ} (hf : Integrable f μ) :
    Continuous (gaussFourier μ f) := by
  unfold gaussFourier
  refine continuous_of_dominated (bound := fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · intro ξ
    exact hf.aestronglyMeasurable.mul (aestronglyMeasurable_character' μ hcoord ξ)
  · intro ξ
    filter_upwards with x
    rw [norm_mul, norm_character, mul_one]
  · filter_upwards with x
    exact continuous_const.mul (by unfold character; fun_prop)

omit [SFinite μ] in
/-- The Fourier slice `u ↦ ρ̂(2πu) 𝒢_μ f(-2πu a)` is integrable. -/
theorem integrable_fourier_slice' {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Integrable fun u : ℝ =>
      filterFourier ρ (2 * Real.pi * u) * gaussFourier μ f (-((2 * Real.pi * u) • a)) := by
  have h1 : Integrable fun u : ℝ => filterFourier ρ (2 * Real.pi * u) :=
    (integrable_filterFourier ρ).comp_mul_left' (by positivity)
  refine h1.mul_bdd (c := ∫ x, ‖f x‖ ∂μ) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_gaussFourier' μ hcoord hf).comp
      (by fun_prop : Continuous fun u : ℝ => -((2 * Real.pi * u) • a))).aestronglyMeasurable
  · exact norm_gaussFourier_le μ f _

/-- **The slice as a coefficient** (`eq:slice-as-coefficient`): for integrable `f`,
`R_ρ f = γ_G` with `G = 𝒢_μ f`, by Fourier inversion along the bias variable. -/
theorem ridgelet_eq_coefficientFormula' {f : H → ℂ} (hf : Integrable f μ) :
    ridgelet μ ρ f = coefficientFormula ρ (gaussFourier μ f) := by
  funext p
  obtain ⟨a, c⟩ := p
  rw [coefficientFormula_eq_fourier]
  have hslice : (fun u : ℝ => filterFourier ρ (2 * Real.pi * u) *
      gaussFourier μ f (-((2 * Real.pi * u) • a))) = 𝓕 (fun c => ridgelet μ ρ f (a, c)) := by
    funext u
    rw [fourier_ridgelet_slice' μ ρ hcoord hf]
  have hint : Integrable (𝓕 fun c => ridgelet μ ρ f (a, c)) := by
    rw [← hslice]
    exact integrable_fourier_slice' μ ρ hcoord hf a
  rw [hslice, ← Real.fourierInv_eq_fourier_neg,
    (continuous_ridgelet_slice' μ ρ hcoord hf a).fourierInv_fourier_eq
      (integrable_ridgelet_slice' μ ρ hcoord hf a) hint]

end AEMeasurable

end OperatorRidgelet
