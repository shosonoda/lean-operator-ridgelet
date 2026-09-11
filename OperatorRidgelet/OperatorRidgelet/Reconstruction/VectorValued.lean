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

/-! ### The bounded extension of the `Y`-valued transform to `𝒦(Y)` -/

section EmbeddingVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

variable (μ ν : Measure H) [IsFiniteMeasure μ]

/-- The L²-valued vector Fourier transform preserves addition on the spectral core. -/
theorem gaussFourierLpVec_add (f g : spectralCoreVec Y μ ν) :
    gaussFourierLpVec μ ν (f + g) = gaussFourierLpVec μ ν f + gaussFourierLpVec μ ν g := by
  unfold gaussFourierLpVec
  rw [← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourierVec μ ((f + g : Lp Y 2 μ) : H → Y) ξ = _
  rw [gaussFourierVec_add]

/-- The L²-valued vector Fourier transform sends zero to zero. -/
theorem gaussFourierLpVec_zero : gaussFourierLpVec μ ν (0 : spectralCoreVec Y μ ν) = 0 := by
  unfold gaussFourierLpVec
  rw [← MemLp.toLp_zero (MemLp.zero : MemLp (0 : H → Y) 2 ν)]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourierVec μ ((0 : Lp Y 2 μ) : H → Y) ξ = _
  rw [gaussFourierVec_zero']

/-- The L²-valued vector Fourier transform preserves complex scalar multiplication. -/
theorem gaussFourierLpVec_smul (c : ℂ) (f : spectralCoreVec Y μ ν) :
    gaussFourierLpVec μ ν (c • f) = c • gaussFourierLpVec μ ν f := by
  unfold gaussFourierLpVec
  rw [← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourierVec μ ((c • f : Lp Y 2 μ) : H → Y) ξ = _
  rw [gaussFourierVec_smul]

variable (Y) in
/-- The range `𝒢_μ(𝒟(Y))` as a submodule of `L²(ν; Y)`. -/
def gaussFourierRangeVec : Submodule ℂ (Lp Y 2 ν) where
  carrier := Set.range (gaussFourierLpVec μ ν)
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, gaussFourierLpVec_add μ ν f g⟩
  zero_mem' := ⟨0, gaussFourierLpVec_zero μ ν⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨c • f, gaussFourierLpVec_smul μ ν c f⟩

/-- The vector Fourier range is the range of the bundled L² transform. -/
theorem coe_gaussFourierRangeVec :
    (gaussFourierRangeVec Y μ ν : Set (Lp Y 2 ν)) = Set.range (gaussFourierLpVec μ ν) := rfl

/-- `𝒦(Y) = closure 𝒢_μ(𝒟(Y))`: the span in the definition of `spectralRangeVec` is
redundant. -/
theorem spectralRangeVec_eq_topologicalClosure :
    spectralRangeVec Y μ ν = (gaussFourierRangeVec Y μ ν).topologicalClosure := by
  unfold spectralRangeVec
  rw [← coe_gaussFourierRangeVec, Submodule.span_eq]

/-- `𝒢_μ : 𝒟(Y) → 𝒦(Y)` as a linear map. -/
def spectralEmbedVecₗ : spectralCoreVec Y μ ν →ₗ[ℂ] spectralRangeVec Y μ ν where
  toFun := spectralEmbedVec μ ν
  map_add' f g := Subtype.ext (gaussFourierLpVec_add μ ν f g)
  map_smul' c f := Subtype.ext (gaussFourierLpVec_smul μ ν c f)

/-- The linear spectral embedding evaluates as the original spectral embedding. -/
@[simp]
theorem spectralEmbedVecₗ_apply (f : spectralCoreVec Y μ ν) :
    spectralEmbedVecₗ μ ν f = spectralEmbedVec μ ν f := rfl

/-- The image of the core `𝒟(Y)` under `𝒢_μ` is dense in `𝒦(Y)`. -/
theorem denseRange_spectralEmbedVecₗ : DenseRange (spectralEmbedVecₗ (Y := Y) μ ν) := by
  have key : (spectralRangeVec Y μ ν : Set (Lp Y 2 ν)) ⊆
      closure (Set.range (gaussFourierLpVec μ ν)) := by
    rw [← coe_gaussFourierRangeVec, spectralRangeVec_eq_topologicalClosure,
      Submodule.topologicalClosure_coe]
  unfold DenseRange
  rw [Subtype.dense_iff]
  convert key using 2
  ext g
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨spectralEmbedVecₗ μ ν f, ⟨f, rfl⟩, rfl⟩

variable {μ}

omit [IsFiniteMeasure μ] in
/-- The integrand of the `Y`-valued ridgelet transform is integrable at every parameter. -/
theorem integrable_ridgeletVec_integrand (ρ : SchwartzMap ℝ ℝ) {f : H → Y} (hf : Integrable f μ)
    (p : H × ℝ) : Integrable (fun x => (ρ (⟪p.1, x⟫ + p.2) : ℂ) • f x) μ := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  refine hf.smul_of_top_right (memLp_top_of_bound (Complex.continuous_ofReal.comp
    (ρ.continuous.comp
      (by fun_prop : Continuous fun x : H => ⟪p.1, x⟫ + p.2))).aestronglyMeasurable C
    (Eventually.of_forall fun x => ?_))
  rw [Complex.norm_real]
  exact hC.2 _

/-- `R_ρ` is additive on `L²(μ; Y)` classes. -/
theorem ridgeletVec_coe_add (ρ : SchwartzMap ℝ ℝ) (f g : Lp Y 2 μ) :
    ridgeletVec μ ρ ((f + g : Lp Y 2 μ) : H → Y) = ridgeletVec μ ρ f + ridgeletVec μ ρ g := by
  funext p
  simp only [ridgeletVec, Pi.add_apply]
  rw [← integral_add (integrable_ridgeletVec_integrand ρ ((Lp.memLp f).integrable one_le_two) p)
    (integrable_ridgeletVec_integrand ρ ((Lp.memLp g).integrable one_le_two) p)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx, Pi.add_apply, smul_add]

omit [OpensMeasurableSpace H] in
/-- `R_ρ` is homogeneous on `L²(μ; Y)` classes. -/
theorem ridgeletVec_coe_smul (ρ : SchwartzMap ℝ ℝ) (c : ℂ) (f : Lp Y 2 μ) :
    ridgeletVec μ ρ ((c • f : Lp Y 2 μ) : H → Y) = c • ridgeletVec μ ρ f := by
  funext p
  simp only [ridgeletVec, Pi.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx, Pi.smul_apply, smul_comm]

end EmbeddingVec

section ExtensionVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SFinite ν]

variable {α : ℝ} (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hν hρ

/-- `R_ρ : 𝒟(Y) → L²(λ; Y)` as a linear map, for an `α`-admissible filter `ρ`. -/
def ridgeletCoreVecₗ : spectralCoreVec Y μ ν →ₗ[ℂ] Lp Y 2 (parameterMeasure ν) where
  toFun f := (memLp_ridgeletVec μ hν hρ ((Lp.memLp (f : Lp Y 2 μ)).integrable one_le_two)
    (Lp.memLp _) ((mem_spectralCoreVec_iff μ ν (f : Lp Y 2 μ)).mp f.2)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
    show ridgeletVec μ ρ (((f : Lp Y 2 μ) + (g : Lp Y 2 μ) : Lp Y 2 μ) : H → Y) p = _
    rw [ridgeletVec_coe_add]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
    show ridgeletVec μ ρ ((c • (f : Lp Y 2 μ) : Lp Y 2 μ) : H → Y) p = _
    rw [ridgeletVec_coe_smul]
    rfl

/-- `ridgeletCoreVecₗ f` is the `L²(λ; Y)` class of `R_ρ f`. -/
theorem ridgeletCoreVecₗ_apply (f : spectralCoreVec Y μ ν) :
    ridgeletCoreVecₗ hν hρ f = MemLp.toLp (ridgeletVec μ ρ f) (memLp_ridgeletVec μ hν hρ
      ((Lp.memLp (f : Lp Y 2 μ)).integrable one_le_two) (Lp.memLp _)
      ((mem_spectralCoreVec_iff μ ν (f : Lp Y 2 μ)).mp f.2)) := rfl

/-- `ridgeletCoreVecₗ f` agrees `λ`-almost everywhere with `R_ρ f`. -/
theorem coeFn_ridgeletCoreVecₗ (f : spectralCoreVec Y μ ν) :
    (ridgeletCoreVecₗ hν hρ f : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f := by
  rw [ridgeletCoreVecₗ_apply]
  exact MemLp.coeFn_toLp _

/-- The scaled isometry on the core: `‖R_ρ f‖² = C^{(α)}_ρ ‖𝒢_μ f‖²`. -/
theorem norm_ridgeletCoreVecₗ_sq (f : spectralCoreVec Y μ ν) :
    ‖ridgeletCoreVecₗ hν hρ f‖ ^ 2 = admissibilityConst α ρ * ‖spectralEmbedVecₗ μ ν f‖ ^ 2 := by
  rw [ridgeletCoreVecₗ_apply, MemLp.norm_toLp_two_sq]
  show _ = admissibilityConst α ρ * ‖gaussFourierLpVec μ ν f‖ ^ 2
  rw [gaussFourierLpVec, MemLp.norm_toLp_two_sq]
  exact integral_ridgeletVec_norm_sq μ hν hρ
    ((Lp.memLp (f : Lp Y 2 μ)).integrable one_le_two) (Lp.memLp _)
    ((mem_spectralCoreVec_iff μ ν (f : Lp Y 2 μ)).mp f.2)

/-- The norm bound `‖R_ρ f‖ ≤ √C_ρ ‖𝒢_μ f‖` on the core. -/
theorem norm_ridgeletCoreVecₗ_le (f : spectralCoreVec Y μ ν) :
    ‖ridgeletCoreVecₗ hν hρ f‖ ≤
      Real.sqrt (admissibilityConst α ρ) * ‖spectralEmbedVecₗ μ ν f‖ := by
  refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_)
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_ridgeletCoreVecₗ_sq]

/-- The bounded extension `R_ρ : 𝒦(Y) → L²(λ; Y)` of the `Y`-valued ridgelet transform. -/
def ridgeletExtensionVecCLM : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν) :=
  (ridgeletCoreVecₗ hν hρ).extendOfNorm (spectralEmbedVecₗ μ ν)

/-- The extension restricts to `ridgeletCoreVecₗ` on the image of the core. -/
theorem ridgeletExtensionVecCLM_embed (f : spectralCoreVec Y μ ν) :
    ridgeletExtensionVecCLM hν hρ (spectralEmbedVec μ ν f) = ridgeletCoreVecₗ hν hρ f :=
  LinearMap.extendOfNorm_eq (denseRange_spectralEmbedVecₗ μ ν)
    ⟨_, norm_ridgeletCoreVecₗ_le hν hρ⟩ f

/-- The extension agrees `λ`-almost everywhere with `R_ρ f` on the image of the core. -/
theorem coeFn_ridgeletExtensionVecCLM_embed (f : spectralCoreVec Y μ ν) :
    (ridgeletExtensionVecCLM hν hρ (spectralEmbedVec μ ν f) : H × ℝ → Y)
      =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f := by
  rw [ridgeletExtensionVecCLM_embed]
  exact coeFn_ridgeletCoreVecₗ hν hρ f

/-- Any bounded operator on `𝒦(Y)` restricting to `R_ρ` on the core is the extension. -/
theorem eq_ridgeletExtensionVecCLM
    (R : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCoreVec Y μ ν,
      (R (spectralEmbedVec μ ν f) : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f) :
    R = ridgeletExtensionVecCLM hν hρ := by
  symm
  refine LinearMap.extendOfNorm_unique (denseRange_spectralEmbedVecₗ μ ν) _
    (norm_ridgeletCoreVecₗ_le hν hρ) R ?_
  ext f
  exact (hR f).trans (coeFn_ridgeletCoreVecₗ hν hρ f).symm

/-- Existence and uniqueness of the bounded extension of the `Y`-valued `R_ρ` to `𝒦(Y)`. -/
theorem existsUnique_ridgeletExtensionVecCLM :
    ∃! R : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      ∀ f : spectralCoreVec Y μ ν,
        (R (spectralEmbedVec μ ν f) : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f :=
  ⟨ridgeletExtensionVecCLM hν hρ, coeFn_ridgeletExtensionVecCLM_embed hν hρ,
    fun R hR => eq_ridgeletExtensionVecCLM hν hρ R hR⟩

/-- `ridgeletExtensionVec` is the bounded extension. -/
theorem ridgeletExtensionVec_eq :
    ridgeletExtensionVec Y μ ν ρ = ridgeletExtensionVecCLM hν hρ := by
  have hex : ∃ R : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      ∀ f : spectralCoreVec Y μ ν,
        (R (spectralEmbedVec μ ν f) : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f :=
    ⟨ridgeletExtensionVecCLM hν hρ, coeFn_ridgeletExtensionVecCLM_embed hν hρ⟩
  unfold ridgeletExtensionVec
  rw [dif_pos hex]
  exact eq_ridgeletExtensionVecCLM hν hρ _ hex.choose_spec

/-- The extension is a scaled isometry: `‖R_ρ G‖² = C^{(α)}_ρ ‖G‖²` on `𝒦(Y)`. -/
theorem norm_ridgeletExtensionVecCLM_sq (G : spectralRangeVec Y μ ν) :
    ‖ridgeletExtensionVecCLM hν hρ G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  refine (denseRange_spectralEmbedVecₗ μ ν).induction_on G ?_ fun f => ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rw [spectralEmbedVecₗ_apply, ridgeletExtensionVecCLM_embed, norm_ridgeletCoreVecₗ_sq,
      spectralEmbedVecₗ_apply]

/-- `‖R_ρ G‖ = √C_ρ ‖G‖` on `𝒦(Y)`. -/
theorem norm_ridgeletExtensionVecCLM (G : spectralRangeVec Y μ ν) :
    ‖ridgeletExtensionVecCLM hν hρ G‖ = Real.sqrt (admissibilityConst α ρ) * ‖G‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt hρ.pos.le, norm_ridgeletExtensionVecCLM_sq]

/-- The extension has closed range. -/
theorem isClosed_range_ridgeletExtensionVecCLM :
    IsClosed (Set.range (ridgeletExtensionVecCLM (Y := Y) (μ := μ) hν hρ)) := by
  have hC : 0 < Real.sqrt (admissibilityConst α ρ) := Real.sqrt_pos.mpr hρ.pos
  haveI : CompleteSpace (spectralRangeVec Y μ ν) := Submodule.topologicalClosure.completeSpace _
  refine AntilipschitzWith.isClosed_range
    (K := (Real.sqrt (admissibilityConst α ρ))⁻¹.toNNReal) ?_
    (ridgeletExtensionVecCLM hν hρ).uniformContinuous
  refine (ridgeletExtensionVecCLM hν hρ).antilipschitz_of_bound fun G => ?_
  rw [norm_ridgeletExtensionVecCLM hν hρ, Real.coe_toNNReal _ (by positivity), ← mul_assoc,
    inv_mul_cancel₀ hC.ne', one_mul]

end ExtensionVec

/-! ### The `Y`-valued frame identity on `𝒦(Y)` -/

section FrameVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SFinite ν] {α : ℝ}
  (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hν hρ

/-- The polarized `Y`-valued Plancherel identity on `𝒦(Y)`:
`⟪R g, R f⟫_{L²(λ;Y)} = C^{(α)}_ρ ⟪g, f⟫`. -/
theorem inner_ridgeletExtensionVecCLM (f g : spectralRangeVec Y μ ν) :
    inner ℂ (ridgeletExtensionVecCLM hν hρ g) (ridgeletExtensionVecCLM hν hρ f) =
      (admissibilityConst α ρ : ℂ) * inner ℂ g f := by
  set T : spectralRangeVec Y μ ν →L[ℂ] spectralRangeVec Y μ ν :=
    (ContinuousLinearMap.adjoint (ridgeletExtensionVecCLM hν hρ)).comp
        (ridgeletExtensionVecCLM hν hρ) -
      (admissibilityConst α ρ : ℂ) • ContinuousLinearMap.id ℂ (spectralRangeVec Y μ ν) with hT
  have hT0 : ∀ u, inner ℂ (T u) u = 0 := by
    intro u
    have hnorm := norm_ridgeletExtensionVecCLM_sq hν hρ u
    simp only [hT, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
    rw [Submodule.coe_inner (spectralRangeVec Y μ ν) _ u, Submodule.coe_smul, inner_smul_left,
      ← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      Complex.conj_ofReal]
    show ((‖ridgeletExtensionVecCLM hν hρ u‖ : ℝ) : ℂ) ^ 2 -
      ((admissibilityConst α ρ : ℝ) : ℂ) * ((‖u‖ : ℝ) : ℂ) ^ 2 = 0
    rw [← Complex.ofReal_pow, hnorm]
    push_cast
    ring
  have hzero : T = 0 := by
    have h := (inner_map_self_eq_zero
      (T : spectralRangeVec Y μ ν →ₗ[ℂ] spectralRangeVec Y μ ν)).mp hT0
    refine ContinuousLinearMap.ext fun u => ?_
    exact congrArg (fun S : spectralRangeVec Y μ ν →ₗ[ℂ] spectralRangeVec Y μ ν => S u) h
  have h := congrArg (fun S : spectralRangeVec Y μ ν →L[ℂ] spectralRangeVec Y μ ν =>
    inner ℂ (S g) f) hzero
  simp only [hT, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    _root_.zero_apply, inner_zero_left] at h
  rw [Submodule.coe_inner (spectralRangeVec Y μ ν) _ f, Submodule.coe_smul, inner_smul_left,
    ← Submodule.coe_inner, Complex.conj_ofReal] at h
  exact sub_eq_zero.mp h

/-- The `Y`-valued frame identity `S_ρ R_ρ f = C^{(α)}_ρ T f` on `𝒦(Y)`. -/
theorem synthesisVec_ridgeletExtensionVec (f : spectralRangeVec Y μ ν) :
    synthesisVec μ ν ρ (ridgeletExtensionVec Y μ ν ρ f) =
      (admissibilityConst α ρ : ℂ) • frameOperatorVec μ ν f := by
  ext g
  simp only [synthesisVec, frameOperatorVec, transposeEmbedVec, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, innerSLFlip_apply_apply, Submodule.subtypeL_apply,
    ridgeletExtensionVec_eq hν hρ, smul_eq_mul]
  rw [inner_ridgeletExtensionVecCLM hν hρ, Submodule.coe_inner]

end FrameVec

/-! ### The `Y`-valued synthesis operator and the Riesz maps -/

section SynthesisAlgebraVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

variable (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)

/-- `(S_ρ γ)[g] = ⟪R_ρ g, γ⟫_{L²(λ;Y)}`. -/
theorem synthesisVec_apply (γ : Lp Y 2 (parameterMeasure ν)) (g : spectralRangeVec Y μ ν) :
    synthesisVec μ ν ρ γ g = inner ℂ (ridgeletExtensionVec Y μ ν ρ g) γ := rfl

/-- The `Y`-valued synthesis operator is homogeneous. -/
theorem synthesisVec_smul (c : ℂ) (γ : Lp Y 2 (parameterMeasure ν)) :
    synthesisVec μ ν ρ (c • γ) = c • synthesisVec (Y := Y) μ ν ρ γ := by
  ext g
  simp only [synthesisVec_apply, _root_.smul_apply, inner_smul_right, smul_eq_mul]

/-- The `Y`-valued synthesis operator is additive on differences. -/
theorem synthesisVec_sub (γ γ' : Lp Y 2 (parameterMeasure ν)) :
    synthesisVec μ ν ρ (γ - γ') = synthesisVec (Y := Y) μ ν ρ γ - synthesisVec μ ν ρ γ' := by
  ext g
  simp only [synthesisVec_apply, _root_.sub_apply, inner_sub_right]

/-- `S_ρ γ = 0` if and only if `γ ⊥ Ran R_ρ`. -/
theorem synthesisVec_eq_zero_iff (γ : Lp Y 2 (parameterMeasure ν)) :
    synthesisVec μ ν ρ γ = 0 ↔ γ ∈ (ridgeletRangeVec Y μ ν ρ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hu
    have := congrArg (fun F : SpectralAntiDualVec Y μ ν => F g) h
    simpa [synthesisVec_apply] using this
  · intro h
    ext g
    rw [synthesisVec_apply, _root_.zero_apply]
    exact h _ (LinearMap.mem_range.mpr ⟨g, rfl⟩)

/-- `J⁻¹ (J f) = f` for the `Y`-valued Riesz map. -/
theorem rieszInvVec_rieszMapVec (f : spectralRangeVec Y μ ν) :
    rieszInvVec μ ν (rieszMapVec Y μ ν f) = f := by
  have h : antiDualConj (rieszMapVec Y μ ν f) =
      InnerProductSpace.toDual ℂ (spectralRangeVec Y μ ν) f := by
    ext g
    simp only [rieszMapVec, antiDualConj_apply, innerSLFlip_apply_apply,
      InnerProductSpace.toDual_apply_apply, inner_conj_symm]
  unfold rieszInvVec
  rw [h, LinearIsometryEquiv.symm_apply_apply]

/-- `U' G = J G` for `G ∈ 𝒦(Y)`. -/
theorem transposeEmbedVec_coe (G : spectralRangeVec Y μ ν) :
    transposeEmbedVec μ ν (G : Lp Y 2 ν) = rieszMapVec Y μ ν G := by
  ext g
  simp only [transposeEmbedVec, rieszMapVec, ContinuousLinearMap.comp_apply,
    innerSLFlip_apply_apply, Submodule.subtypeL_apply, Submodule.coe_inner]

/-- `J⁻¹ (U' G) = G` for `G ∈ 𝒦(Y)`. -/
theorem rieszInvVec_transposeEmbedVec_coe (G : spectralRangeVec Y μ ν) :
    rieszInvVec μ ν (transposeEmbedVec μ ν (G : Lp Y 2 ν)) = G := by
  rw [transposeEmbedVec_coe, rieszInvVec_rieszMapVec]

end SynthesisAlgebraVec

/-! ### Fourier uniqueness and injectivity for `Y`-valued targets -/

section InjectivityVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

omit [SecondCountableTopology H] in
/-- `𝒢_μ f` is the target with spectral density `f` at the reflected point. -/
theorem gaussFourierVec_eq_spectralTarget (μ : Measure H) (f : H → Y) (ξ : H) :
    gaussFourierVec μ f ξ = spectralTarget μ f (-ξ) := by
  unfold gaussFourierVec spectralTarget character
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hx : (⟪-ξ, x⟫ : ℝ) = -⟪x, ξ⟫ := by
    rw [inner_neg_left, real_inner_comm]
  beta_reduce
  rw [hx]
  congr 2
  push_cast
  ring

/-- Fourier uniqueness for `Y`-valued targets: `𝒢_μ f = 0` forces `f = 0` `μ`-almost
everywhere. -/
theorem ae_eq_zero_of_gaussFourierVec_eq_zero (μ : Measure H) [IsFiniteMeasure μ] {f : H → Y}
    (hf : Integrable f μ) (h : ∀ ξ, gaussFourierVec μ f ξ = 0) : f =ᵐ[μ] 0 := by
  refine ae_eq_zero_of_spectralTarget_eq_zero_vec μ hf ?_
  funext x
  rw [Pi.zero_apply, ← neg_neg x, ← gaussFourierVec_eq_spectralTarget, h]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- `𝒢_μ` is additive on differences of `L²(μ; Y)` classes. -/
theorem gaussFourierVec_coe_sub (μ : Measure H) [IsFiniteMeasure μ] (f g : Lp Y 2 μ) :
    gaussFourierVec μ ((f - g : Lp Y 2 μ) : H → Y) =
      gaussFourierVec μ f - gaussFourierVec μ g := by
  funext ξ
  simp only [gaussFourierVec, Pi.sub_apply]
  rw [← integral_sub (integrable_character_smul μ f ξ) (integrable_character_smul μ g ξ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx, Pi.sub_apply, smul_sub]

/-- `𝒢_μ` is injective on `L²(μ; Y)`. -/
theorem Lp.eq_of_gaussFourierVec_eq (μ : Measure H) [IsFiniteMeasure μ] {f g : Lp Y 2 μ}
    (h : gaussFourierVec μ f = gaussFourierVec μ g) : f = g := by
  have hint : Integrable ((f - g : Lp Y 2 μ) : H → Y) μ := (Lp.memLp _).integrable one_le_two
  have hzero : ∀ ξ, gaussFourierVec μ ((f - g : Lp Y 2 μ) : H → Y) ξ = 0 := by
    intro ξ
    rw [gaussFourierVec_coe_sub, Pi.sub_apply, h, sub_self]
  have hae := ae_eq_zero_of_gaussFourierVec_eq_zero μ hint hzero
  rw [← sub_eq_zero]
  exact Lp.ext (hae.trans (Lp.coeFn_zero Y 2 μ).symm)

/-- `Δ_Q (𝒢_μ f) = f` for `f ∈ 𝒟(Y)`. -/
theorem gaussFourierInvVec_gaussFourierVec (μ ν : Measure H) [IsFiniteMeasure μ]
    (f : spectralCoreVec Y μ ν) :
    gaussFourierInvVec μ ν (gaussFourierVec μ (f : Lp Y 2 μ)) = (f : Lp Y 2 μ) := by
  have hex : ∃ f' : Lp Y 2 μ, f' ∈ spectralCoreVec Y μ ν ∧
      gaussFourierVec μ f' = gaussFourierVec μ (f : Lp Y 2 μ) := ⟨f, f.2, rfl⟩
  unfold gaussFourierInvVec
  rw [dif_pos hex]
  exact Lp.eq_of_gaussFourierVec_eq μ hex.choose_spec.2

/-- **Injectivity** of the `Y`-valued transform: if `R_ρ f = 0` `λ`-almost everywhere for
`f ∈ L¹(μ; Y)`, then `f = 0` `μ`-almost everywhere. -/
theorem ae_eq_zero_of_ridgeletVec_ae_eq_zero (μ : Measure H) [IsProbabilityMeasure μ]
    {ν : Measure H} [SFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ) {f : H → Y}
    (hf : Integrable f μ) (h : ridgeletVec μ ρ f =ᵐ[parameterMeasure ν] 0) : f =ᵐ[μ] 0 := by
  obtain ⟨ω₀, hω₀, hρω₀⟩ := hρ.exists_ne_zero_filterFourier_ne_zero hα
  have hslice : ∀ᵐ a ∂ν, gaussFourierVec μ f ((-ω₀) • a) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with a ha
    have hb : biasFourierVec (ridgeletVec μ ρ f) a ω₀ = 0 := by
      unfold biasFourierVec
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ha] with c hc
      simp only [hc, Pi.zero_apply, smul_zero]
    rw [biasFourierVec_ridgeletVec μ ρ hf, smul_eq_zero] at hb
    rw [neg_smul]
    exact hb.resolve_left hρω₀
  have hs : MeasurableSet {ξ : H | gaussFourierVec μ f ξ = 0} :=
    (isClosed_singleton.preimage (continuous_gaussFourierVec μ hf)).measurableSet
  have hmap : ∀ᵐ ξ ∂(ν.map fun a => (-ω₀) • a), gaussFourierVec μ f ξ = 0 :=
    (ae_map_iff (measurable_const_smul (-ω₀)).aemeasurable hs).mpr hslice
  rw [hν (-ω₀) (neg_ne_zero.mpr hω₀)] at hmap
  have hc : ENNReal.ofReal (|(-ω₀)| ^ (-α)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr (neg_ne_zero.mpr hω₀)) _)).ne'
  have hmap' : ∀ᵐ ξ ∂ν, gaussFourierVec μ f ξ = 0 := by
    rw [ae_iff] at hmap ⊢
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hmap
    exact hmap.resolve_left hc
  have hzero : gaussFourierVec μ f = 0 :=
    ((continuous_gaussFourierVec μ hf).ae_eq_iff_eq ν continuous_const).mp hmap'
  exact ae_eq_zero_of_gaussFourierVec_eq_zero μ hf fun ξ => congrFun hzero ξ

end InjectivityVec

/-! ### Backprojection of the `Y`-valued Fourier-slice representative -/

section BackprojectionVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- `Λ_ρ` applied to the continuous Fourier-slice representative `(a, ω) ↦ ρ̂(ω) • 𝒢_μ f(-ωa)`
of `R_ρ f` gives `C^{(α)}_ρ • 𝒢_μ f(ξ)` pointwise. -/
theorem backprojectionOfVec_biasFourierVec_ridgeletVec (μ : Measure H) [IsProbabilityMeasure μ]
    (α : ℝ) (ρ : SchwartzMap ℝ ℝ) {f : H → Y} (hf : Integrable f μ) (ξ : H) :
    backprojectionOfVec α ρ (biasFourierVec (ridgeletVec μ ρ f)) ξ =
      (admissibilityConst α ρ : ℂ) • gaussFourierVec μ f ξ := by
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have key : ∀ᵐ ω : ℝ ∂volume,
      ((starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) •
          biasFourierVec (ridgeletVec μ ρ f) (-(ω⁻¹ • ξ)) ω =
        ((‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ) • gaussFourierVec μ f ξ := by
    filter_upwards [h0] with ω hω
    rw [biasFourierVec_ridgeletVec μ ρ hf]
    have hξ : -(ω • -(ω⁻¹ • ξ)) = ξ := by
      rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
    rw [hξ, smul_smul]
    congr 1
    push_cast
    rw [← Complex.conj_mul']
    ring
  unfold backprojectionOfVec admissibilityConst
  rw [integral_congr_ae key, integral_smul_const, integral_complex_ofReal, ← smul_assoc,
    Complex.real_smul, ← Complex.ofReal_mul]

end BackprojectionVec

end OperatorRidgelet
