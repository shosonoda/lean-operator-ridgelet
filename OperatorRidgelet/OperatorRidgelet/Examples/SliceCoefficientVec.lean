import OperatorRidgelet.Examples.SliceCoefficient
import OperatorRidgelet.Reconstruction.Defs

/-!
# The `Y`-valued ridgelet coefficient as the coefficient of its spectral density

The vector-valued counterpart of `OperatorRidgelet.Examples.SliceCoefficient`: for an
integrable `F : H → Y`, the bias function `c ↦ R_ρ F(a, c)` is continuous and integrable, its
Fourier transform is `ρ̂(ω) • 𝒢_μ F(-ωa)` (`fourier_ridgeletVec_slice'`), and Fourier inversion
gives `R_ρ F = γ_G` for `G = 𝒢_μ F` (`ridgeletVec_eq_coefficientFormulaVec'`).  As in the scalar
case only the a.e.-measurability of the coordinates `x ↦ ⟪x, v⟫` under `μ` is assumed.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace FourierTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  (μ : Measure H) [SFinite μ] (ρ : SchwartzMap ℝ ℝ)
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-! ### The Fourier transform of a translated filter -/

/-- The line Fourier transform of the translate `c ↦ ρ(t + c)` at frequency `ω` is
`e^{iωt} ρ̂(ω)`. -/
theorem integral_filter_add_mul_exp (t ω : ℝ) :
    ∫ c : ℝ, (ρ (t + c) : ℂ) * Complex.exp (-((ω * c : ℝ) * Complex.I)) =
      Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * filterFourier ρ ω := by
  have hkey : (fun c : ℝ => (ρ (t + c) : ℂ) * Complex.exp (-((ω * c : ℝ) * Complex.I))) =
      fun c : ℝ => Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) *
        ((fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))
          (t + c)) := by
    funext c
    have hexp : Complex.exp (-((ω * c : ℝ) * Complex.I)) =
        Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-Complex.I * ((inner ℝ (t + c) ω : ℝ) : ℂ)) := by
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

/-! ### The vector-valued slice -/

section AEMeasurable

variable (hcoord : ∀ v : H, AEMeasurable (fun x => ⟪x, v⟫) μ)
include hcoord

/-- The kernel `(x, c) ↦ ρ(⟪a, x⟫ + c) • F(x)` is jointly integrable against `μ ⊗ dc`. -/
theorem integrable_ridgeletVec_kernel' {F : H → Y} (hF : Integrable F μ) (a : H) :
    Integrable (fun q : H × ℝ => (ρ (⟪a, q.1⟫ + q.2) : ℂ) • F q.1) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun q : H × ℝ => (ρ (⟪a, q.1⟫ + q.2) : ℂ) • F q.1)
      (μ.prod volume) := by
    have h1 : AEMeasurable (fun q : H × ℝ => ⟪a, q.1⟫ + q.2) (μ.prod volume) := by
      have h2 : AEMeasurable (fun q : H × ℝ => ⟪q.1, a⟫) (μ.prod volume) :=
        (hcoord a).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      refine (h2.add measurable_snd.aemeasurable).congr (Eventually.of_forall fun q => ?_)
      simp only [Pi.add_apply]
      first
      | rfl
      | rw [real_inner_comm q.1 a]
    exact ((Complex.continuous_ofReal.comp ρ.continuous).comp_aestronglyMeasurable
      h1.aestronglyMeasurable).smul
      (hF.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with x
    exact ((ρ.integrable.comp_add_left ⟪a, x⟫).ofReal (𝕜 := ℂ)).smul_const (F x)
  · have : (fun x => ∫ c : ℝ, ‖(ρ (⟪a, x⟫ + c) : ℂ) • F x‖) =
        fun x => ‖F x‖ * ∫ t : ℝ, ‖ρ t‖ := by
      funext x
      simp_rw [norm_smul, Complex.norm_real]
      rw [integral_mul_const, integral_add_left_eq_self (f := fun t => ‖ρ t‖) ⟪a, x⟫, mul_comm]
    rw [this]
    exact hF.norm.mul_const _

/-- The bias function `R_ρ F(a, ·)` is integrable. -/
theorem integrable_ridgeletVec_slice' {F : H → Y} (hF : Integrable F μ) (a : H) :
    Integrable (fun c : ℝ => ridgeletVec μ ρ F (a, c)) :=
  (integrable_ridgeletVec_kernel' μ ρ hcoord hF a).integral_prod_right

/-- The bias function `R_ρ F(a, ·)` is continuous. -/
theorem continuous_ridgeletVec_slice' {F : H → Y} (hF : Integrable F μ) (a : H) :
    Continuous fun c : ℝ => ridgeletVec μ ρ F (a, c) := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  unfold ridgeletVec
  refine continuous_of_dominated (bound := fun x => C * ‖F x‖) ?_ ?_ (hF.norm.const_mul C) ?_
  · intro c
    exact (aestronglyMeasurable_ridge μ ρ hcoord a c).smul hF.aestronglyMeasurable
  · intro c
    filter_upwards with x
    rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC.2 _) (norm_nonneg _)
  · filter_upwards with x
    exact (Complex.continuous_ofReal.comp
      (ρ.continuous.comp (continuous_const.add continuous_id))).smul continuous_const

/-- The Fourier-slice identity for `Y`-valued targets:
`𝓕 (c ↦ R_ρ F(a, c)) u = ρ̂(2πu) • 𝒢_μ F(-2πu a)`. -/
theorem fourier_ridgeletVec_slice' {F : H → Y} (hF : Integrable F μ) (a : H) (u : ℝ) :
    𝓕 (fun c => ridgeletVec μ ρ F (a, c)) u =
      filterFourier ρ (2 * Real.pi * u) • gaussFourierVec μ F (-((2 * Real.pi * u) • a)) := by
  set ω : ℝ := 2 * Real.pi * u with hω
  have hF' : Integrable (fun q : H × ℝ =>
      (Complex.exp (-((ω * q.2 : ℝ) * Complex.I)) * (ρ (⟪a, q.1⟫ + q.2) : ℂ)) • F q.1)
      (μ.prod volume) := by
    have h := integrable_ridgeletVec_kernel' μ ρ hcoord hF a
    refine (h.smul_of_top_left (φ := fun q : H × ℝ => Complex.exp (-((ω * q.2 : ℝ) * Complex.I)))
      (memLp_top_of_bound ((by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((ω * t : ℝ) * Complex.I))).comp_aestronglyMeasurable
        measurable_snd.aestronglyMeasurable) 1 (Eventually.of_forall fun q => ?_))).congr
      (Eventually.of_forall fun q => ?_)
    · rw [show -((ω * q.2 : ℝ) * Complex.I) = ((-(ω * q.2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    · simp only [smul_smul]
  have hchar : ∀ x : H, character (-(ω • a)) x =
      Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) := by
    intro x
    simp only [character, inner_neg_right, inner_smul_right, real_inner_comm a x]
    push_cast
    ring_nf
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hexp : ∀ c : ℝ, Complex.exp (((-2 * Real.pi * c * u : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((ω * c : ℝ) * Complex.I)) := by
    intro c
    congr 1
    rw [hω]
    push_cast
    ring
  simp_rw [hexp]
  calc ∫ c : ℝ, Complex.exp (-((ω * c : ℝ) * Complex.I)) • ridgeletVec μ ρ F (a, c)
      = ∫ c : ℝ, ∫ x, (Complex.exp (-((ω * c : ℝ) * Complex.I)) *
          (ρ (⟪a, x⟫ + c) : ℂ)) • F x ∂μ := by
        congr 1
        funext c
        unfold ridgeletVec
        rw [← integral_smul]
        congr 1
        funext x
        rw [smul_smul]
    _ = ∫ x, ∫ c : ℝ, (Complex.exp (-((ω * c : ℝ) * Complex.I)) *
          (ρ (⟪a, x⟫ + c) : ℂ)) • F x ∂μ :=
        (integral_integral_swap hF').symm
    _ = ∫ x, (character (-(ω • a)) x * filterFourier ρ ω) • F x ∂μ := by
        congr 1
        funext x
        rw [integral_smul_const]
        congr 1
        have h := integral_filter_add_mul_exp ρ ⟪a, x⟫ ω
        rw [hchar, ← h]
        congr 1
        funext c
        ring
    _ = filterFourier ρ ω • gaussFourierVec μ F (-(ω • a)) := by
        unfold gaussFourierVec
        rw [← integral_smul]
        congr 1
        funext x
        rw [smul_smul, mul_comm]

/-- The `Y`-valued explicit coefficient is a Fourier transform along each ray. -/
theorem coefficientFormulaVec_eq_fourier (G : H → Y) (a : H) (c : ℝ) :
    coefficientFormulaVec ρ G (a, c) =
      𝓕 (fun u : ℝ => filterFourier ρ (2 * Real.pi * u) • G (-((2 * Real.pi * u) • a))) (-c) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold coefficientFormulaVec
  have h := Measure.integral_comp_mul_left (fun ω =>
    (filterFourier ρ ω * Complex.exp ((ω * c : ℝ) * Complex.I)) • G (-(ω • a))) (2 * Real.pi)
  rw [abs_of_pos (by positivity)] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_smul]
  congr 1
  have : ((-2 * Real.pi * u * -c : ℝ) : ℂ) = ((2 * Real.pi * u * c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]
  ring

/-- `𝒢_μ F` is bounded by `∫ ‖F‖ dμ`. -/
theorem norm_gaussFourierVec_le (F : H → Y) (ξ : H) :
    ‖gaussFourierVec μ F ξ‖ ≤ ∫ x, ‖F x‖ ∂μ := by
  unfold gaussFourierVec
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_smul, norm_character, one_mul]

/-- `𝒢_μ F` is continuous for integrable `F`. -/
theorem continuous_gaussFourierVec' {F : H → Y} (hF : Integrable F μ) :
    Continuous (gaussFourierVec μ F) := by
  unfold gaussFourierVec
  refine continuous_of_dominated (bound := fun x => ‖F x‖) ?_ ?_ hF.norm ?_
  · intro ξ
    exact (aestronglyMeasurable_character' μ hcoord ξ).smul hF.aestronglyMeasurable
  · intro ξ
    filter_upwards with x
    rw [norm_smul, norm_character, one_mul]
  · filter_upwards with x
    exact (by unfold character; fun_prop : Continuous fun ξ : H => character ξ x).smul
      continuous_const

/-- The Fourier slice `u ↦ ρ̂(2πu) • 𝒢_μ F(-2πu a)` is integrable. -/
theorem integrable_fourierVec_slice' {F : H → Y} (hF : Integrable F μ) (a : H) :
    Integrable fun u : ℝ =>
      filterFourier ρ (2 * Real.pi * u) • gaussFourierVec μ F (-((2 * Real.pi * u) • a)) := by
  have h1 : Integrable fun u : ℝ => filterFourier ρ (2 * Real.pi * u) :=
    (integrable_filterFourier ρ).comp_mul_left' (by positivity)
  refine h1.smul_of_top_left (memLp_top_of_bound ?_ (∫ x, ‖F x‖ ∂μ)
    (Eventually.of_forall fun u => norm_gaussFourierVec_le μ F _))
  exact ((continuous_gaussFourierVec' μ hcoord hF).comp
    (by fun_prop : Continuous fun u : ℝ => -((2 * Real.pi * u) • a))).aestronglyMeasurable

/-- **The `Y`-valued slice as a coefficient**: for integrable `F`, `R_ρ F = γ_G` with
`G = 𝒢_μ F`. -/
theorem ridgeletVec_eq_coefficientFormulaVec' {F : H → Y} (hF : Integrable F μ) :
    ridgeletVec μ ρ F = coefficientFormulaVec ρ (gaussFourierVec μ F) := by
  funext p
  obtain ⟨a, c⟩ := p
  rw [coefficientFormulaVec_eq_fourier]
  have hslice : (fun u : ℝ => filterFourier ρ (2 * Real.pi * u) •
      gaussFourierVec μ F (-((2 * Real.pi * u) • a))) =
      𝓕 (fun c => ridgeletVec μ ρ F (a, c)) := by
    funext u
    rw [fourier_ridgeletVec_slice' μ ρ hcoord hF]
  have hint : Integrable (𝓕 fun c => ridgeletVec μ ρ F (a, c)) := by
    rw [← hslice]
    exact integrable_fourierVec_slice' μ ρ hcoord hF a
  rw [hslice, ← Real.fourierInv_eq_fourier_neg,
    (continuous_ridgeletVec_slice' μ ρ hcoord hF a).fourierInv_fourier_eq
      (integrable_ridgeletVec_slice' μ ρ hcoord hF a) hint]

end AEMeasurable

end OperatorRidgelet
