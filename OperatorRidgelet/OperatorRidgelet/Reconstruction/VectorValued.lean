import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Reconstruction.Representation
import OperatorRidgelet.Transform.Plancherel

/-!
# The `Y`-valued Plancherel theory (Theorem `thm:vector-valued`)

The vector-valued counterpart of `OperatorRidgelet.Transform.Plancherel` for a complex Hilbert
target `Y`: the Fourier-slice identity, the Plancherel identity, the bounded extension
`R_ρ : 𝓔(Y) → L²(λ; Y)`, and injectivity.  Scalar products `f(x) φ(x)` become `φ(x) • f(x)`
and scalar integrals Bochner integrals; the one-dimensional Plancherel and Parseval identities
that drive the proofs (`MeasureTheory.Integrable.lintegral_enorm_fourier_sq` and
`MeasureTheory.Integrable.integral_inner_fourier` of `LeanRidgelet.ToMathlib.FourierPlancherel`)
are already stated for a complex Hilbert target, so the scalar arguments transcribe verbatim.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace FourierTransform

/-! ### The `Y`-valued weighted Fourier transform -/

section GaussFourierVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

omit [OpensMeasurableSpace H] in
/-- `𝒢_μ f` is bounded by `‖f‖_{L¹(μ;Y)}`. -/
theorem norm_gaussFourierVec_le' (μ : Measure H) (f : H → Y) (ξ : H) :
    ‖gaussFourierVec μ f ξ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  unfold gaussFourierVec
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_smul, norm_character, one_mul]

/-- `𝒢_μ f` is continuous for integrable `f` (dominated convergence). -/
theorem continuous_gaussFourierVec (μ : Measure H) {f : H → Y} (hf : Integrable f μ) :
    Continuous (gaussFourierVec μ f) := by
  unfold gaussFourierVec
  refine continuous_of_dominated (bound := fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · intro ξ
    exact (continuous_character ξ).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · intro ξ
    filter_upwards with x
    rw [norm_smul, norm_character, one_mul]
  · filter_upwards with x
    unfold character
    fun_prop

end GaussFourierVec

/-! ### The `Y`-valued ridgelet transform along a bias line -/

section Slices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

variable (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)

omit [IsProbabilityMeasure μ] [CompleteSpace Y] in
/-- The kernel `(x, c) ↦ ρ(⟪a, x⟫ + c) • f(x)` is jointly integrable against `μ ⊗ dc`. -/
theorem integrable_ridgeletVec_kernel {f : H → Y} (hf : Integrable f μ) (a : H) :
    Integrable (fun q : H × ℝ => (ρ (⟪a, q.1⟫ + q.2) : ℂ) • f q.1) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun q : H × ℝ => (ρ (⟪a, q.1⟫ + q.2) : ℂ) • f q.1)
      (μ.prod volume) :=
    (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun q : H × ℝ => ⟪a, q.1⟫ + q.2))).aestronglyMeasurable.smul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with x
    exact ((ρ.integrable.comp_add_left ⟪a, x⟫).ofReal (𝕜 := ℂ)).smul_const (f x)
  · have : (fun x => ∫ c : ℝ, ‖(ρ (⟪a, x⟫ + c) : ℂ) • f x‖) =
        fun x => ‖f x‖ * ∫ t : ℝ, ‖ρ t‖ := by
      funext x
      simp_rw [norm_smul, Complex.norm_real]
      rw [integral_mul_const, integral_add_left_eq_self (f := fun t => ‖ρ t‖) ⟪a, x⟫, mul_comm]
    rw [this]
    exact hf.norm.mul_const _

omit [IsProbabilityMeasure μ] [CompleteSpace Y] in
/-- `R_ρ f` is jointly continuous. -/
theorem continuous_ridgeletVec {f : H → Y} (hf : Integrable f μ) :
    Continuous (ridgeletVec μ ρ f) := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  unfold ridgeletVec
  refine continuous_of_dominated (bound := fun x => C * ‖f x‖) ?_ ?_ (hf.norm.const_mul C) ?_
  · intro p
    exact (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun x : H => ⟪p.1, x⟫ + p.2))).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  · intro p
    filter_upwards with x
    rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC.2 _) (norm_nonneg _)
  · filter_upwards with x
    fun_prop

/-- The bias function `R_ρ f(a, ·)` is integrable. -/
theorem integrable_ridgeletVec_slice {f : H → Y} (hf : Integrable f μ) (a : H) :
    Integrable (fun c : ℝ => ridgeletVec μ ρ f (a, c)) :=
  (integrable_ridgeletVec_kernel μ ρ hf a).integral_prod_right

/-- The bias function `R_ρ f(a, ·)` is square integrable for `f ∈ L²(μ; Y)`. -/
theorem memLp_ridgeletVec_slice {f : H → Y} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (a : H) :
    MemLp (fun c : ℝ => ridgeletVec μ ρ f (a, c)) 2 volume := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  have hA : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hpt : ∀ c : ℝ, ‖ridgeletVec μ ρ f (a, c)‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
    intro c
    have hρc : MemLp (fun x : H => ρ (⟪a, x⟫ + c)) (ENNReal.ofReal 2) μ :=
      MemLp.of_bound (ρ.continuous.comp
        (by fun_prop : Continuous fun x : H => ⟪a, x⟫ + c)).aestronglyMeasurable C
        (Eventually.of_forall fun x => hC.2 _)
    have hfn : MemLp (fun x : H => ‖f x‖) (ENNReal.ofReal 2) μ := by
      simpa using hf₂.norm
    have h1 : ‖ridgeletVec μ ρ f (a, c)‖ ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [norm_smul, Complex.norm_real, mul_comm]
    have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two hfn hρc
    simp_rw [Real.rpow_two, norm_norm] at h2
    have hB : 0 ≤ ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    have h0 : 0 ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := integral_nonneg fun x => by positivity
    calc ‖ridgeletVec μ ρ f (a, c)‖ ^ 2
        ≤ (∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ) ^ 2 := by gcongr
      _ ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA,
            ← Real.rpow_mul hB]
          norm_num
  have hsq : Integrable (fun t : ℝ => ‖ρ t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm ρ.continuous.aestronglyMeasurable).mp (ρ.memLp 2)
  have hG : Integrable (fun q : H × ℝ => ‖ρ (⟪a, q.1⟫ + q.2)‖ ^ 2) (μ.prod volume) := by
    have hmeas : AEStronglyMeasurable (fun q : H × ℝ => ‖ρ (⟪a, q.1⟫ + q.2)‖ ^ 2)
        (μ.prod volume) :=
      ((ρ.continuous.comp (by fun_prop : Continuous fun q : H × ℝ => ⟪a, q.1⟫ + q.2)).norm.pow 2)
        |>.aestronglyMeasurable
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards with x
      exact hsq.comp_add_left ⟪a, x⟫
    · have : (fun x : H => ∫ c : ℝ, ‖‖ρ (⟪a, x⟫ + c)‖ ^ 2‖) = fun _ => ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
        funext x
        simp_rw [norm_pow, norm_norm]
        exact integral_add_left_eq_self (f := fun t => ‖ρ t‖ ^ 2) ⟪a, x⟫
      rw [this]
      exact integrable_const _
  have hGc : Integrable (fun c : ℝ => (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) :=
    hG.integral_prod_right.const_mul _
  have hmeasR : AEStronglyMeasurable (fun c : ℝ => ridgeletVec μ ρ f (a, c)) volume :=
    ((continuous_ridgeletVec μ ρ hf).comp (by fun_prop : Continuous fun c : ℝ => (a, c)))
      |>.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeasR]
  refine hGc.mono' (hmeasR.norm.pow 2) (Eventually.of_forall fun c => ?_)
  rw [norm_pow, norm_norm]
  exact hpt c

/-- The `Y`-valued Fourier-slice identity
`\widehat{R_ρ f}(a, ω) = ρ̂(ω) • 𝒢_μ f(-ωa)`. -/
theorem biasFourierVec_ridgeletVec {f : H → Y} (hf : Integrable f μ) (a : H) (ω : ℝ) :
    biasFourierVec (ridgeletVec μ ρ f) a ω =
      filterFourier ρ ω • gaussFourierVec μ f (-(ω • a)) := by
  have hF := integrable_ridgeletVec_kernel μ ρ hf a
  have hF' : Integrable (fun q : H × ℝ =>
      (Complex.exp (-((ω * q.2 : ℝ) * Complex.I)) * (ρ (⟪a, q.1⟫ + q.2) : ℂ)) • f q.1)
      (μ.prod volume) := by
    refine (hF.smul_of_top_right (φ := fun q : H × ℝ =>
      Complex.exp (-((ω * q.2 : ℝ) * Complex.I)))
      (memLp_top_of_bound ((by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((ω * t : ℝ) * Complex.I))).comp_aestronglyMeasurable
        measurable_snd.aestronglyMeasurable) 1 (Eventually.of_forall fun q => ?_))).congr
      (Eventually.of_forall fun q => ?_)
    · rw [show -((ω * q.2 : ℝ) * Complex.I) = ((-(ω * q.2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    · simp only [Pi.smul_apply', smul_smul]
  have hchar : ∀ x : H, character (-(ω • a)) x =
      Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) := by
    intro x
    simp only [character, inner_neg_right, inner_smul_right, real_inner_comm a x]
    push_cast
    ring_nf
  unfold biasFourierVec
  calc ∫ c : ℝ, Complex.exp (-((ω * c : ℝ) * Complex.I)) • ridgeletVec μ ρ f (a, c)
      = ∫ c : ℝ, (∫ x, (Complex.exp (-((ω * c : ℝ) * Complex.I)) *
          (ρ (⟪a, x⟫ + c) : ℂ)) • f x ∂μ) := by
        congr 1
        funext c
        unfold ridgeletVec
        rw [← integral_smul]
        congr 1
        funext x
        rw [smul_smul]
    _ = ∫ x, (∫ c : ℝ, (Complex.exp (-((ω * c : ℝ) * Complex.I)) *
          (ρ (⟪a, x⟫ + c) : ℂ)) • f x) ∂μ :=
        (integral_integral_swap hF').symm
    _ = ∫ x, (character (-(ω • a)) x * filterFourier ρ ω) • f x ∂μ := by
        congr 1
        funext x
        rw [integral_smul_const]
        congr 1
        have h : ∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) * Complex.exp (-((ω * c : ℝ) * Complex.I)) =
            Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) * filterFourier ρ ω := by
          have hkey : (fun c : ℝ => (ρ (⟪a, x⟫ + c) : ℂ) *
              Complex.exp (-((ω * c : ℝ) * Complex.I))) =
              fun c : ℝ => Complex.exp (((ω * ⟪a, x⟫ : ℝ) : ℂ) * Complex.I) *
                ((fun u : ℝ => Complex.exp (-Complex.I * ((inner ℝ u ω : ℝ) : ℂ)) * (ρ u : ℂ))
                  (⟪a, x⟫ + c)) := by
            funext c
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
        rw [hchar, ← h]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        ring
    _ = filterFourier ρ ω • gaussFourierVec μ f (-(ω • a)) := by
        unfold gaussFourierVec
        rw [← integral_smul]
        congr 1
        funext x
        rw [smul_smul, mul_comm]

/-- Mathlib's Fourier transform of the `Y`-valued bias function is the Fourier slice at
frequency `2πu`. -/
theorem fourier_ridgeletVec_slice {f : H → Y} (hf : Integrable f μ) (a : H) (u : ℝ) :
    𝓕 (fun c => ridgeletVec μ ρ f (a, c)) u =
      filterFourier ρ (2 * Real.pi * u) • gaussFourierVec μ f (-((2 * Real.pi * u) • a)) := by
  rw [← biasFourierVec_ridgeletVec μ ρ hf a (2 * Real.pi * u)]
  unfold biasFourierVec
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  congr 1
  congr 1
  push_cast
  ring

end Slices

/-! ### A Cauchy--Schwarz bound in `ℝ≥0∞` -/

section EnormInner

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Cauchy--Schwarz in `ℝ≥0∞`: `‖⟪u, v⟫‖ₑ ≤ ‖u‖ₑ ‖v‖ₑ`. -/
theorem enorm_inner_le (u v : Y) : ‖inner ℂ u v‖ₑ ≤ ‖u‖ₑ * ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm (𝕜 := ℂ) u v)

end EnormInner

/-! ### The `Y`-valued Plancherel identity along a bias line -/

section SlicesHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

variable (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)

/-- Plancherel along the bias line, `Y`-valued:
`∫⁻ ‖R_ρ f(a,c)‖ₑ² dc = (2π)⁻¹ ∫⁻ ‖ρ̂(ω)‖ₑ² ‖𝒢_μ f(-ωa)‖ₑ² dω`. -/
theorem lintegral_ridgeletVec_slice_sq {f : H → Y} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ)
    (a : H) :
    ∫⁻ c, ‖ridgeletVec μ ρ f (a, c)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ ω, ‖filterFourier ρ ω‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(ω • a))‖ₑ ^ 2 := by
  rw [← (integrable_ridgeletVec_slice μ ρ hf a).lintegral_enorm_fourier_sq
    (memLp_ridgeletVec_slice μ ρ hf hf₂ a)]
  simp_rw [fourier_ridgeletVec_slice μ ρ hf a, enorm_smul, mul_pow]
  rw [lintegral_comp_mul_left_real
    (F := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(ω • a))‖ₑ ^ 2)
    (((continuous_filterFourier ρ).enorm.measurable.pow_const 2).mul
      (((continuous_gaussFourierVec μ hf).comp
        (by fun_prop : Continuous fun ω : ℝ => -(ω • a))).enorm.measurable.pow_const 2))
    (by positivity), abs_of_pos (by positivity)]

/-- Parseval along the bias line for two `Y`-valued transforms. -/
theorem integral_inner_ridgeletVec_slice (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) {f g : H → Y}
    (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) (hg : Integrable g μ) (hg₂ : MemLp g 2 μ) (a : H) :
    ∫ c, inner ℂ (ridgeletVec μ ρ₂ g (a, c)) (ridgeletVec μ ρ₁ f (a, c)) =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ ω, (filterFourier ρ₁ ω * (starRingEnd ℂ) (filterFourier ρ₂ ω)) *
          inner ℂ (gaussFourierVec μ g (-(ω • a))) (gaussFourierVec μ f (-(ω • a))) := by
  rw [← (integrable_ridgeletVec_slice μ ρ₂ hg a).integral_inner_fourier
    (memLp_ridgeletVec_slice μ ρ₂ hg hg₂ a) (integrable_ridgeletVec_slice μ ρ₁ hf a)
    (memLp_ridgeletVec_slice μ ρ₁ hf hf₂ a)]
  simp_rw [fourier_ridgeletVec_slice μ _ hf a, fourier_ridgeletVec_slice μ _ hg a,
    inner_smul_left, inner_smul_right]
  rw [Measure.integral_comp_mul_left (fun ω => (starRingEnd ℂ) (filterFourier ρ₂ ω) *
    (filterFourier ρ₁ ω *
      inner ℂ (gaussFourierVec μ g (-(ω • a))) (gaussFourierVec μ f (-(ω • a)))))
    (2 * Real.pi), abs_of_pos (by positivity), Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  ring

end SlicesHilbert

/-! ### The weighted Tonelli identity for a `Y`-valued density -/

section Rays

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y]

/-- The weighted Tonelli identity for `(a, ω) ↦ ρ̂(ω) • G(-ωa)` with a `Y`-valued `G`. -/
theorem IsAdmissible.lintegral_prod_enorm_sq_vec {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {G : H → Y}
    (hG : Measurable fun ξ => ‖G ξ‖ₑ) :
    ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 ∂ν.prod volume =
      ENNReal.ofReal (2 * Real.pi * admissibilityConst α ρ) * ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂ν := by
  rw [hν.lintegral_prod_neg_smul (K := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2)
    ((continuous_filterFourier ρ).enorm.measurable.pow_const 2) (hG.pow_const 2),
    hρ.lintegral_enorm_sq_mul]

/-- For `G ∈ L²(ν; Y)`, `(a, ω) ↦ ρ̂(ω) • G(-ωa)` is square integrable on `ν ⊗ dω`. -/
theorem IsAdmissible.lintegral_prod_enorm_sq_vec_lt_top {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {G : H → Y}
    (hG : Measurable fun ξ => ‖G ξ‖ₑ) (hG₂ : MemLp G 2 ν) :
    ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ ^ 2 ∂ν.prod volume < ⊤ := by
  rw [IsAdmissible.lintegral_prod_enorm_sq_vec hν hρ hG]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG₂.lintegral_enorm_sq_lt_top

end Rays

/-! ### Square integrability and the `Y`-valued Plancherel identity on `H × ℝ` -/

section Product

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

variable (μ : Measure H) [IsProbabilityMeasure μ] {ν : Measure H} [SFinite ν] {α : ℝ}

/-- The squared `L²(λ; Y)` norm of `R_ρ f`, as a lower Lebesgue integral. -/
theorem lintegral_ridgeletVec_sq (ν : Measure H) [SFinite ν] (ρ : SchwartzMap ℝ ℝ) {f : H → Y}
    (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    ∫⁻ p, ‖ridgeletVec μ ρ f p‖ₑ ^ 2 ∂parameterMeasure ν =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ p : H × ℝ, ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ ^ 2
          ∂ν.prod volume := by
  have hmeas : Measurable fun p : H × ℝ => ‖ridgeletVec μ ρ f p‖ₑ ^ 2 :=
    (continuous_ridgeletVec μ ρ hf).enorm.measurable.pow_const 2
  have hmeas' : Measurable fun p : H × ℝ =>
      ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ ^ 2 :=
    (((continuous_filterFourier ρ).comp continuous_snd).enorm.measurable.pow_const 2).mul
      (((continuous_gaussFourierVec μ hf).comp
        (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1))).enorm.measurable.pow_const 2)
  unfold parameterMeasure
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_prod _ hmeas'.aemeasurable,
    ← lintegral_const_mul _ (Measurable.lintegral_prod_right' hmeas')]
  refine lintegral_congr fun a => ?_
  exact lintegral_ridgeletVec_slice_sq μ ρ hf hf₂ a

/-- `R_ρ f ∈ L²(λ; Y)` for `f ∈ L²(μ; Y)` with `𝒢_μ f ∈ L²(ν; Y)` and `α`-admissible `ρ`. -/
theorem memLp_ridgeletVec (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsAdmissible α ρ) {f : H → Y} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ)
    (hG : MemLp (gaussFourierVec μ f) 2 ν) :
    MemLp (ridgeletVec μ ρ f) 2 (parameterMeasure ν) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top
    (continuous_ridgeletVec μ ρ hf).aestronglyMeasurable ?_
  rw [lintegral_ridgeletVec_sq μ ν ρ hf hf₂]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (IsAdmissible.lintegral_prod_enorm_sq_vec_lt_top hν hρ
      (continuous_gaussFourierVec μ hf).enorm.measurable hG)

/-- The product `(a, ω) ↦ ρ̂₁ conj ρ̂₂ (ω) ⟪𝒢g, 𝒢f⟫(-ωa)` is integrable on `ν ⊗ dω`. -/
theorem integrable_cross_kernel_vec (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) {f g : H → Y} (hf : Integrable f μ)
    (hg : Integrable g μ) (hGf : MemLp (gaussFourierVec μ f) 2 ν)
    (hGg : MemLp (gaussFourierVec μ g) 2 ν) :
    Integrable (fun p : H × ℝ => (filterFourier ρ₁ p.2 * (starRingEnd ℂ) (filterFourier ρ₂ p.2)) *
      inner ℂ (gaussFourierVec μ g (-(p.2 • p.1))) (gaussFourierVec μ f (-(p.2 • p.1))))
      (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  refine ⟨?_, ?_⟩
  · exact (((continuous_filterFourier ρ₁).comp continuous_snd).mul
      (Complex.continuous_conj.comp ((continuous_filterFourier ρ₂).comp continuous_snd))).mul
      (((continuous_gaussFourierVec μ hg).comp hc).inner
        ((continuous_gaussFourierVec μ hf).comp hc))
      |>.aestronglyMeasurable
  · rw [HasFiniteIntegral]
    calc ∫⁻ p : H × ℝ, ‖(filterFourier ρ₁ p.2 * (starRingEnd ℂ) (filterFourier ρ₂ p.2)) *
          inner ℂ (gaussFourierVec μ g (-(p.2 • p.1)))
            (gaussFourierVec μ f (-(p.2 • p.1)))‖ₑ ∂ν.prod volume
        ≤ ∫⁻ p : H × ℝ,
            ‖filterFourier ρ₁ p.2‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ ^ 2 +
            ‖filterFourier ρ₂ p.2‖ₑ ^ 2 * ‖gaussFourierVec μ g (-(p.2 • p.1))‖ₑ ^ 2
            ∂ν.prod volume := by
          refine lintegral_mono fun p => ?_
          simp only [enorm_mul, RCLike.enorm_conj]
          calc ‖filterFourier ρ₁ p.2‖ₑ * ‖filterFourier ρ₂ p.2‖ₑ *
                ‖inner ℂ (gaussFourierVec μ g (-(p.2 • p.1)))
                  (gaussFourierVec μ f (-(p.2 • p.1)))‖ₑ
              ≤ ‖filterFourier ρ₁ p.2‖ₑ * ‖filterFourier ρ₂ p.2‖ₑ *
                (‖gaussFourierVec μ g (-(p.2 • p.1))‖ₑ *
                  ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ) := by
                gcongr
                exact enorm_inner_le _ _
            _ = (‖filterFourier ρ₁ p.2‖ₑ * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ) *
                (‖filterFourier ρ₂ p.2‖ₑ * ‖gaussFourierVec μ g (-(p.2 • p.1))‖ₑ) := by ring
            _ ≤ (‖filterFourier ρ₁ p.2‖ₑ * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ) ^ 2 +
                (‖filterFourier ρ₂ p.2‖ₑ * ‖gaussFourierVec μ g (-(p.2 • p.1))‖ₑ) ^ 2 :=
                ENNReal.mul_le_sq_add_sq _ _
            _ = _ := by ring
      _ < ⊤ := by
          have hm : Measurable fun p : H × ℝ =>
              ‖filterFourier ρ₁ p.2‖ₑ ^ 2 * ‖gaussFourierVec μ f (-(p.2 • p.1))‖ₑ ^ 2 :=
            (((continuous_filterFourier ρ₁).comp continuous_snd).enorm.measurable.pow_const 2).mul
              (((continuous_gaussFourierVec μ hf).comp hc).enorm.measurable.pow_const 2)
          rw [lintegral_add_left hm]
          exact ENNReal.add_lt_top.mpr
            ⟨IsAdmissible.lintegral_prod_enorm_sq_vec_lt_top hν hρ₁
                (continuous_gaussFourierVec μ hf).enorm.measurable hGf,
              IsAdmissible.lintegral_prod_enorm_sq_vec_lt_top hν hρ₂
                (continuous_gaussFourierVec μ hg).enorm.measurable hGg⟩

/-- The pointwise inner product of two `Y`-valued transforms is `λ`-integrable. -/
theorem integrable_inner_ridgeletVec (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) {f g : H → Y} (hf : Integrable f μ)
    (hf₂ : MemLp f 2 μ) (hg : Integrable g μ) (hg₂ : MemLp g 2 μ)
    (hGf : MemLp (gaussFourierVec μ f) 2 ν) (hGg : MemLp (gaussFourierVec μ g) 2 ν) :
    Integrable (fun p : H × ℝ => inner ℂ (ridgeletVec μ ρ₂ g p) (ridgeletVec μ ρ₁ f p))
      (parameterMeasure ν) := by
  have hRf := memLp_ridgeletVec μ hν hρ₁ hf hf₂ hGf
  have hRg := memLp_ridgeletVec μ hν hρ₂ hg hg₂ hGg
  refine (L2.integrable_inner (𝕜 := ℂ) (hRg.toLp _) (hRf.toLp _)).congr ?_
  filter_upwards [hRg.coeFn_toLp, hRf.coeFn_toLp] with p h2 h1
  rw [h1, h2]

/-- **The `Y`-valued Plancherel identity** for the ridgelet transform:
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ;Y)} = C^{(α)}_{ρ₁,ρ₂} ⟨f, g⟩_{𝓔(Y)}`. -/
theorem integral_inner_ridgeletVec (hν : IsHomogeneous α ν) {ρ₁ ρ₂ : SchwartzMap ℝ ℝ}
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) {f g : H → Y} (hf : Integrable f μ)
    (hf₂ : MemLp f 2 μ) (hg : Integrable g μ) (hg₂ : MemLp g 2 μ)
    (hGf : MemLp (gaussFourierVec μ f) 2 ν) (hGg : MemLp (gaussFourierVec μ g) 2 ν) :
    ∫ p, inner ℂ (ridgeletVec μ ρ₂ g p) (ridgeletVec μ ρ₁ f p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInnerVec μ ν f g := by
  have hint := integrable_cross_kernel_vec μ hν hρ₁ hρ₂ hf hg hGf hGg
  have hprod := integrable_inner_ridgeletVec μ hν hρ₁ hρ₂ hf hf₂ hg hg₂ hGf hGg
  unfold parameterMeasure
  rw [integral_prod _ hprod]
  simp_rw [integral_inner_ridgeletVec_slice μ ρ₁ ρ₂ hf hf₂ hg hg₂]
  rw [integral_const_mul, ← integral_prod _ hint,
    hν.integral_prod_neg_smul (K := fun ω => filterFourier ρ₁ ω * (starRingEnd ℂ)
      (filterFourier ρ₂ ω))
      (F := fun ξ => inner ℂ (gaussFourierVec μ g ξ) (gaussFourierVec μ f ξ))
      (((continuous_gaussFourierVec μ hg).inner
        (continuous_gaussFourierVec μ hf)).measurable) hint]
  unfold crossAdmissibilityConst spectralInnerVec
  ring

/-- `‖R_ρ f‖²_{L²(λ;Y)} = C^{(α)}_ρ ∫ ‖𝒢_μ f‖² dν`. -/
theorem integral_ridgeletVec_norm_sq (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsAdmissible α ρ) {f : H → Y} (hf : Integrable f μ) (hf₂ : MemLp f 2 μ)
    (hG : MemLp (gaussFourierVec μ f) 2 ν) :
    ∫ p, ‖ridgeletVec μ ρ f p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖gaussFourierVec μ f ξ‖ ^ 2 ∂ν := by
  have h := integral_inner_ridgeletVec μ hν hρ hρ hf hf₂ hf hf₂ hG hG
  rw [crossAdmissibilityConst_self] at h
  have hL : ∫ p, inner ℂ (ridgeletVec μ ρ f p) (ridgeletVec μ ρ f p) ∂parameterMeasure ν =
      ((∫ p, ‖ridgeletVec μ ρ f p‖ ^ 2 ∂parameterMeasure ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hR : spectralInnerVec μ ν f f = ((∫ ξ, ‖gaussFourierVec μ f ξ‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    unfold spectralInnerVec
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hL, hR, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

end Product

end OperatorRidgelet
