import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.FiniteDim.Defs
import OperatorRidgelet.Filters.Defs
import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.Transform.Mixture
import OperatorRidgelet.Transform.Plancherel
import OperatorRidgelet.ToMathlib.Logic
import OperatorRidgelet.ToMathlib.GaussianFourier

/-!
# Statements of Section 3 (the Gaussian-weighted ridgelet transform) and Appendices A, G, H, I

Each item is `theorem OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, identical to its twin in
`Challenge.Transform`, proved from the library or left as `sorry`.

The core theory is stated for the abstract pair `(μ, ν)` of Appendix H (`μ` a probability
measure, `ν` σ-finite with full support and homogeneous of degree `α`); the Gaussian case
`(μ_Q, ν_α)` is the instance with `IsCenteredGaussian Q μ` and `ν = gaussianMixture N α`.
Theorem `thm:B` is stated in the Gaussian case, Theorem `thm:general-weights` is the same set of
claims for the abstract pair.  The design choices for `ν_α`, `μ_Q`, trace class, `𝓔_α`, and
`W_ρ` are documented in `OperatorRidgelet.Transform.Defs`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Lemma `lem:homogeneous-mixture` -/

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  In infinite dimension the
mixture `ν_α` is σ-finite. -/
theorem lem_homogeneous_mixture_i (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    SigmaFinite (gaussianMixture N α) := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` is
finite on bounded Borel sets. -/
theorem lem_homogeneous_mixture_ii (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E → Bornology.IsBounded E → gaussianMixture N α E < ⊤ := by
  sorry

set_option linter.unusedVariables false in
/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` is
infinite on `H`. -/
theorem lem_homogeneous_mixture_iii (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    gaussianMixture N α Set.univ = ⊤ :=
  hN.gaussianMixture_univ α

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` has
full support: it charges every nonempty open set. -/
theorem lem_homogeneous_mixture_iv (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    (gaussianMixture N α).IsOpenPosMeasure := by
  sorry

set_option linter.unusedVariables false in
/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  Homogeneity:
`(D_ω)_# ν_α = |ω|^{-α} ν_α` for `ω ≠ 0`. -/
theorem lem_homogeneous_mixture_v (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    IsHomogeneous α (gaussianMixture N α) :=
  hN.isHomogeneous_gaussianMixture α

set_option linter.unusedVariables false in
/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The integrated form of
homogeneity: `∫ F(ωa) ν_α(da) = |ω|^{-α} ∫ F dν_α` for every nonnegative Borel `F`. -/
theorem lem_homogeneous_mixture_vi (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    ∀ ω : ℝ, ω ≠ 0 → ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ a, F (ω • a) ∂gaussianMixture N α =
        ENNReal.ofReal (|ω| ^ (-α)) * ∫⁻ ξ, F ξ ∂gaussianMixture N α := by
  intro ω hω F hF
  rw [← lintegral_map hF (measurable_const_smul ω), hN.isHomogeneous_gaussianMixture α ω hω,
    lintegral_smul_measure, smul_eq_mul]

/-! ### Definition `def:admissible-filter` -/

/-- **Definition [def:admissible-filter]** Admissible analysis filter.  A band-pass filter is
`α`-admissible for every `α > 0`. -/
theorem def_admissible_filter (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ α : ℝ, 0 < α → IsAdmissible α ρ := by
  intro α hα
  have hcont : Continuous (filterFourier ρ) := hρ.contDiff.continuous
  have hev : filterFourier ρ =ᶠ[𝓝 0] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hρ.zero_notMem_tsupport
  have hg_cont : Continuous fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) := by
    rw [continuous_iff_continuousAt]
    intro ω
    by_cases hω : ω = 0
    · subst hω
      have : (fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α)) =ᶠ[𝓝 (0 : ℝ)]
          fun _ => (0 : ℝ) := by
        filter_upwards [hev] with ω hω
        simp [hω]
      exact this.continuousAt
    · exact ((hcont.norm.pow 2).continuousAt).mul
        ((Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.mpr hω))).comp
          continuous_abs.continuousAt)
  have hg_supp : HasCompactSupport fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) :=
    (hρ.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_right
  have hint : Integrable fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) :=
    hg_cont.integrable_of_hasCompactSupport hg_supp
  refine ⟨hint, ?_⟩
  unfold admissibilityConst
  refine mul_pos (inv_pos.mpr (by positivity)) ?_
  rw [integral_pos_iff_support_of_nonneg (fun ω => by positivity) hint]
  have hsub : Function.support (filterFourier ρ) ⊆
      Function.support fun ω : ℝ => ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) := by
    intro ω hω
    have hω0 : ω ≠ 0 := fun h => hρ.zero_notMem_tsupport (h ▸ subset_tsupport _ hω)
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hω))
      (Real.rpow_pos_of_pos (abs_pos.mpr hω0) _).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  exact hcont.isOpen_support.measure_pos volume
    (Function.support_nonempty_iff.mpr (filterFourier_ne_zero hρ.ne_zero))

/-! ### Lemma `lem:fourier-slice` -/

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  `R_ρ f` is bounded on `H × ℝ`. -/
theorem lem_fourier_slice_i (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∃ M : ℝ, ∀ p : H × ℝ, ‖ridgelet μ ρ f p‖ ≤ M := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  refine ⟨(∫ x, ‖f x‖ ∂μ) * C, fun p => ?_⟩
  unfold ridgelet
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hf.norm.mul_const C)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hC.2 _) (norm_nonneg _)

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  `R_ρ f` is jointly continuous on
`H × ℝ`. -/
theorem lem_fourier_slice_ii (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    Continuous (ridgelet μ ρ f) := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  unfold ridgelet
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hf.norm.mul_const C) ?_
  · intro p
    exact hf.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun x : H => ⟪p.1, x⟫ + p.2))).aestronglyMeasurable
  · intro p
    filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hC.2 _) (norm_nonneg _)
  · filter_upwards with x
    fun_prop

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  For every direction `a`, the bias
function `R_ρ f (a, ·)` is integrable with `‖R_ρ f(a,·)‖_{L¹} ≤ ‖f‖_{L¹(μ)} ‖ρ‖_{L¹}`. -/
theorem lem_fourier_slice_iii (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∀ a : H, Integrable (fun c : ℝ => ridgelet μ ρ f (a, c)) ∧
      ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ≤ (∫ x, ‖f x‖ ∂μ) * ∫ t : ℝ, ‖ρ t‖ := by
  intro a
  have hF := integrable_ridgelet_kernel μ ρ hf a
  refine ⟨hF.integral_prod_right, ?_⟩
  calc ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖
      ≤ ∫ c : ℝ, (∫ x, ‖f x * (ρ (⟪a, x⟫ + c) : ℂ)‖ ∂μ) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun c => norm_nonneg _)
          hF.integral_norm_prod_right (Eventually.of_forall fun c => ?_)
        exact norm_integral_le_integral_norm _
    _ = ∫ x, (∫ c : ℝ, ‖f x * (ρ (⟪a, x⟫ + c) : ℂ)‖) ∂μ :=
        (integral_integral_swap hF.norm).symm
    _ = ∫ x, (‖f x‖ * ∫ t : ℝ, ‖ρ t‖) ∂μ := by
        congr 1
        funext x
        simp_rw [norm_mul, Complex.norm_real]
        rw [integral_const_mul, integral_add_left_eq_self (f := fun t => ‖ρ t‖) ⟪a, x⟫]
    _ = (∫ x, ‖f x‖ ∂μ) * ∫ t : ℝ, ‖ρ t‖ := integral_mul_const _ _

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  If moreover `f ∈ L²(μ)`, then for every
direction `a` the bias function is square integrable with
`‖R_ρ f(a,·)‖²_{L²} ≤ ‖f‖²_{L²(μ)} ‖ρ‖²_{L²}`. -/
theorem lem_fourier_slice_iv (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    ∀ a : H, MemLp (fun c : ℝ => ridgelet μ ρ f (a, c)) 2 volume ∧
      ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
  intro a
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  have hA : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  -- pointwise Cauchy–Schwarz in the probability measure `μ`
  have hpt : ∀ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
    intro c
    have hρc : MemLp (fun x : H => (ρ (⟪a, x⟫ + c) : ℂ)) (ENNReal.ofReal 2) μ :=
      MemLp.of_bound (Complex.continuous_ofReal.comp (ρ.continuous.comp
        (by fun_prop : Continuous fun x : H => ⟪a, x⟫ + c))).aestronglyMeasurable C
        (Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hC.2 _)
    have h1 : ‖ridgelet μ ρ f (a, c)‖ ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp_rw [norm_mul, Complex.norm_real]
    have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (by simpa using hf₂) hρc
    simp_rw [Real.rpow_two, Complex.norm_real] at h2
    have hB : 0 ≤ ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    have h0 : 0 ≤ ∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ := integral_nonneg fun x => by positivity
    calc ‖ridgelet μ ρ f (a, c)‖ ^ 2
        ≤ (∫ x, ‖f x‖ * ‖ρ (⟪a, x⟫ + c)‖ ∂μ) ^ 2 := by gcongr
      _ ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA,
            ← Real.rpow_mul hB]
          norm_num
  -- Tonelli for the square of the filter
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
  have hswap : ∫ c : ℝ, (∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) = ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
    rw [← integral_integral_swap hG]
    have : (fun x : H => ∫ c : ℝ, ‖ρ (⟪a, x⟫ + c)‖ ^ 2) = fun _ => ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
      funext x
      exact integral_add_left_eq_self (f := fun t => ‖ρ t‖ ^ 2) ⟪a, x⟫
    rw [this, integral_const, probReal_univ, one_smul]
  have hGc : Integrable (fun c : ℝ => (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ) :=
    hG.integral_prod_right.const_mul _
  have hmeasR : AEStronglyMeasurable (fun c : ℝ => ridgelet μ ρ f (a, c)) volume :=
    ((lem_fourier_slice_ii μ ρ f hf).comp (by fun_prop : Continuous fun c : ℝ => (a, c)))
      |>.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hmeasR]
    refine hGc.mono' (hmeasR.norm.pow 2) (Eventually.of_forall fun c => ?_)
    rw [norm_pow, norm_norm]
    exact hpt c
  · calc ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ^ 2
        ≤ ∫ c : ℝ, (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖ρ (⟪a, x⟫ + c)‖ ^ 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun c => by positivity) hGc
            (Eventually.of_forall hpt)
      _ = (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ t : ℝ, ‖ρ t‖ ^ 2 := by rw [integral_const_mul, hswap]

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  The partial Fourier transform in the
bias is `\widehat{R_ρ f}(a,ω) = ρ̂(ω) 𝒢_μ f(-ωa)`. -/
theorem lem_fourier_slice_v (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∀ (a : H) (ω : ℝ),
      biasFourier (ridgelet μ ρ f) a ω = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
  intro a ω
  have hF := integrable_ridgelet_kernel μ ρ hf a
  have hF' : Integrable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ) *
      Complex.exp (-((ω * q.2 : ℝ) * Complex.I))) (μ.prod volume) := by
    refine hF.mul_unimodular ?_ (Eventually.of_forall fun q => ?_)
    · exact (by fun_prop : Continuous fun q : H × ℝ =>
        Complex.exp (-((ω * q.2 : ℝ) * Complex.I))).aestronglyMeasurable
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

/-! ### Definition `def:spectral-coefficient` and Lemma `lem:coefficient-isometry` -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Definition [def:spectral-coefficient]** The coefficient operator.  For
`G ∈ L¹(ν) ∩ L²(ν)` the coefficient `W_ρ G` is given by the explicit formula
`γ_G(a,c) = (2π)⁻¹ ∫ ρ̂(ω) G(-ωa) e^{iωc} dω`, `λ`-almost everywhere. -/
theorem def_spectral_coefficient {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    (spectralCoefficient ν ρ G : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] coefficientFormula ρ G := by
  rw [spectralCoefficient_eq_toLp hν hα hρ hG hG₂]
  exact MemLp.coeFn_toLp _

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  `W_ρ G`
is well defined: there is exactly one element of `L²(λ)` whose partial Fourier transform in the
bias is `ρ̂(ω) G(-ωa)`. -/
theorem lem_coefficient_isometry_i {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∃! γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) :=
  existsUnique_hasBiasFourier hν hα hρ hG hG₂

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  `W_ρ G`
does not depend on the Borel representative of `G`. -/
theorem lem_coefficient_isometry_ii {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G G' : H → ℂ)
    (hG : Measurable G) (hG' : Measurable G') (hG₂ : MemLp G 2 ν) (hGG' : G =ᵐ[ν] G') :
    spectralCoefficient ν ρ G = spectralCoefficient ν ρ G' := by
  have key : ∀ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) ↔
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) := by
    intro γ
    have hae := hν.ae_ae_eq_neg_smul hG hG' hGG'
    unfold HasBiasFourier
    constructor
    · intro h
      filter_upwards [h, hae] with a ha haa φ
      rw [ha φ]
      congr 1
      apply integral_congr_ae
      filter_upwards [haa] with ω hω
      rw [hω]
    · intro h
      filter_upwards [h, hae] with a ha haa φ
      rw [ha φ]
      congr 1
      apply integral_congr_ae
      filter_upwards [haa] with ω hω
      rw [hω]
  unfold spectralCoefficient
  by_cases h : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a)))
  · have h' : ∃ γ : Lp ℂ 2 (parameterMeasure ν),
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) :=
      h.imp fun γ => (key γ).mp
    rw [dif_pos h, dif_pos h']
    exact Exists.choose_congr (funext fun γ => propext (key γ)) h h'
  · have h' : ¬ ∃ γ : Lp ℂ 2 (parameterMeasure ν),
        HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G' (-(ω • a))) :=
      fun h' => h (h'.imp fun γ => (key γ).mpr)
    rw [dif_neg h, dif_neg h']

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.
`‖W_ρ G‖²_{L²(λ)} = C^{(α)}_ρ ‖G‖²_{L²(ν)}`. -/
theorem lem_coefficient_isometry_iii {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖(spectralCoefficient ν ρ G : H × ℝ → ℂ) p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν :=
  integral_spectralCoefficient_norm_sq hν hα hρ hG hG₂

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  If
`G ∈ L¹(ν)`, then `ω ↦ G(-ωa)` is integrable on compact subsets of `ℝ ∖ {0}` for `ν`-almost
every `a`. -/
theorem lem_coefficient_isometry_iv {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) :
    ∀ᵐ a ∂ν, ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I →
      IntegrableOn (fun ω : ℝ => G (-(ω • a))) I :=
  hν.ae_integrableOn_neg_smul hα hG hG₁

/-! ### Lemma `lem:spectral-unitary` -/

/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  The spectral form is
positive definite on `𝒟`: `⟨f,f⟩_𝓔 = 0` forces `f = 0` in `L²(μ)`. -/
theorem lem_spectral_unitary_i (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    ∀ f : Lp ℂ 2 μ, f ∈ spectralCore μ ν → spectralInner μ ν f f = 0 → f = 0 := by
  intro f hf h
  rw [spectralInner, integral_mul_conj_self, Complex.ofReal_eq_zero] at h
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_eq_zero_of_integral_norm_gaussFourier_sq_eq_zero μ
    ((Lp.memLp f).integrable one_le_two) hf h)

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  `𝒢_μ` is an
isometry from `(𝒟, ⟨·,·⟩_𝓔)` into `𝒦`: the `L²(ν)` inner product of `U f` and `U g` (which in
Mathlib is conjugate linear in the first argument) is `⟨g,f⟩_𝓔`. -/
theorem lem_spectral_unitary_ii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    ∀ f g : spectralCore μ ν,
      inner ℂ (spectralEmbed μ ν f) (spectralEmbed μ ν g) =
        spectralInner μ ν ((g : Lp ℂ 2 μ) : H → ℂ) ((f : Lp ℂ 2 μ) : H → ℂ) := by
  intro f g
  change inner ℂ (gaussFourierLp μ ν f) (gaussFourierLp μ ν g) = _
  rw [MeasureTheory.L2.inner_def]
  unfold spectralInner gaussFourierLp
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp f.2, MemLp.coeFn_toLp g.2] with ξ hf hg
  rw [hf, hg, RCLike.inner_apply, mul_comm]

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  The image of `𝒟`
under `𝒢_μ` is dense in `𝒦`, so the isometry extends uniquely to a unitary `U_α : 𝓔_α → 𝒦_α`
(the identity of `𝒦` in this representation). -/
theorem lem_spectral_unitary_iii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    Dense (Set.range (spectralEmbed μ ν)) := by
  have key : (spectralRange μ ν : Set (Lp ℂ 2 ν)) ⊆ closure (Set.range (gaussFourierLp μ ν)) := by
    rw [← coe_gaussFourierRange, spectralRange_eq_topologicalClosure,
      Submodule.topologicalClosure_coe]
  rw [Subtype.dense_iff]
  convert key using 2
  ext g
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨spectralEmbed μ ν f, ⟨f, rfl⟩, rfl⟩

/-! ### Lemma `lem:gaussian-decay` and Example `ex:core-elements` -/

/-- **Lemma [lem:gaussian-decay]** Gaussian decay with polynomial weights.  For `t > 0` and every
integer `m ≥ 0`, `∫ ‖ξ‖^{2m} e^{-t⟨Qξ,ξ⟩} ν_α(dξ) < ∞`. -/
theorem lem_gaussian_decay_i (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫))
        (gaussianMixture N α) := by
  sorry

/-- **Lemma [lem:gaussian-decay]** Gaussian decay with polynomial weights.  If `f ∈ L²(μ_Q)` and
`|𝒢_Q f(ξ)| ≤ C (1+‖ξ‖)^p e^{-t⟨Qξ,ξ⟩/2}`, then `f ∈ 𝒟_α` for every `α > 0`. -/
theorem lem_gaussian_decay_ii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : Lp ℂ 2 μ) (C p t : ℝ)
    (hC : 0 < C) (hp : 0 ≤ p) (ht : 0 < t)
    (hdecay : ∀ ξ : H,
      ‖gaussFourier μ f ξ‖ ≤ C * (1 + ‖ξ‖) ^ p * Real.exp (-t * ⟪Q ξ, ξ⟫ / 2)) :
    f ∈ spectralCore μ (gaussianMixture N α) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The constant function has
`𝒢_Q 1 (ξ) = e^{-⟨Qξ,ξ⟩/2}`. -/
theorem ex_core_elements_i {Q : H →L[ℝ] H} (μ : Measure H) [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) :
    ∀ ξ : H, gaussFourier μ (fun _ => (1 : ℂ)) ξ = Complex.exp (-((⟪Q ξ, ξ⟫ / 2 : ℝ) : ℂ)) := by
  intro ξ
  rw [gaussFourier_one, hμ.charFun_eq, map_neg, inner_neg_neg]

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The constant function belongs to `𝒟_α`
for every `α > 0`. -/
theorem ex_core_elements_ii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) ∈ spectralCore μ (gaussianMixture N α) := by
  sorry

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  Consequently `𝓔_α ≠ {0}`. -/
theorem ex_core_elements_iii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    spectralRange μ (gaussianMixture N α) ≠ ⊥ := by
  sorry

/-! ### Theorem `thm:B` (Gaussian case) -/

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  For `f ∈ 𝒟_α` and an
`α`-admissible `ρ`, the transform `R_ρ f` belongs to `L²(λ_α)`. -/
theorem thm_B_i_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ (gaussianMixture N α)) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure (gaussianMixture N α)) := by
  haveI := hN.sfinite_gaussianMixture α
  exact memLp_ridgelet μ (hN.isHomogeneous_gaussianMixture α) hρ
    ((Lp.memLp f).integrable one_le_two) (Lp.memLp f) hf

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ_α)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_α}` for `f, g ∈ 𝒟_α`. -/
theorem thm_B_i_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ₁ ρ₂ : SchwartzMap ℝ ℝ)
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) (f g : Lp ℂ 2 μ)
    (hf : f ∈ spectralCore μ (gaussianMixture N α))
    (hg : g ∈ spectralCore μ (gaussianMixture N α)) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p)
        ∂parameterMeasure (gaussianMixture N α) =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ (gaussianMixture N α) f g := by
  haveI := hN.sfinite_gaussianMixture α
  exact integral_ridgelet_mul_conj μ (hN.isHomogeneous_gaussianMixture α) hρ₁ hρ₂
    ((Lp.memLp f).integrable one_le_two) (Lp.memLp f) ((Lp.memLp g).integrable one_le_two)
    (Lp.memLp g) hf hg

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  An `α`-admissible `ρ` determines a
unique bounded extension `R_ρ : 𝓔_α → L²(λ_α)` of `f ↦ R_ρ f` from `𝒟_α`. -/
theorem thm_B_ii_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRange μ (gaussianMixture N α) →L[ℂ]
        Lp ℂ 2 (parameterMeasure (gaussianMixture N α)),
      ∀ f : spectralCore μ (gaussianMixture N α),
        (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
          =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f := by
  haveI := hN.sfinite_gaussianMixture α
  exact existsUnique_ridgeletExtensionCLM (hN.isHomogeneous_gaussianMixture α) hρ

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension satisfies
`‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_α}`. -/
theorem thm_B_ii_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    ∀ G : spectralRange μ (gaussianMixture N α), ‖R G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  haveI := hN.sfinite_gaussianMixture α
  intro G
  rw [eq_ridgeletExtensionCLM (hN.isHomogeneous_gaussianMixture α) hρ R hR]
  exact norm_ridgeletExtensionCLM_sq (hN.isHomogeneous_gaussianMixture α) hρ G

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension has closed range. -/
theorem thm_B_ii_c (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    IsClosed (Set.range R) := by
  haveI := hN.sfinite_gaussianMixture α
  rw [eq_ridgeletExtensionCLM (hN.isHomogeneous_gaussianMixture α) hρ R hR]
  exact isClosed_range_ridgeletExtensionCLM (hN.isHomogeneous_gaussianMixture α) hρ

set_option linter.unusedVariables false in
/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension factors as
`R_ρ = W_ρ U_α`: on `𝒦_α` it is the coefficient operator. -/
theorem thm_B_ii_d (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    ∀ G : spectralRange μ (gaussianMixture N α),
      R G = spectralCoefficient (gaussianMixture N α) ρ
        ((G : Lp ℂ 2 (gaussianMixture N α)) : H → ℂ) := by
  haveI := hN.sfinite_gaussianMixture α
  intro G
  rw [eq_ridgeletExtensionCLM (hN.isHomogeneous_gaussianMixture α) hρ R hR]
  exact ridgeletExtensionCLM_eq_spectralCoefficient (hN.isHomogeneous_gaussianMixture α) hα hρ μ G

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  Injectivity: if `ρ` is
`α`-admissible and `f ∈ L²(μ_Q)`, then `R_ρ f = 0` `λ_α`-almost everywhere implies `f = 0`
`μ_Q`-almost everywhere. -/
theorem thm_B_iii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure (gaussianMixture N α)] 0) :
    f =ᵐ[μ] 0 := by
  -- `ae_eq_zero_of_ridgelet_ae_eq_zero` proves this once the full support of `ν_α`
  -- (`lem_homogeneous_mixture_iv`, `IsOpenPosMeasure (gaussianMixture N α)`) is available.
  sorry

/-! ### Lemma `lem:mixture-integration` -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For every
Borel set `E`, the map `s ↦ 𝒩(0,2sP)(E)` is Borel measurable on `(0,∞)`. -/
theorem lem_mixture_integration_i {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E → Measurable fun s : Set.Ioi (0 : ℝ) => N s E := by
  intro E hE
  have : (fun s : Set.Ioi (0 : ℝ) => N s E) = fun s : Set.Ioi (0 : ℝ) => scaledLayer N s E := by
    funext s
    rw [hN.eq_scaledLayer s.2]
  rw [this]
  exact ((Measure.measurable_coe hE).comp hN.measurable_scaledLayer).comp measurable_subtype_coe

set_option linter.unusedVariables false in
/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  The
mixture is a countably additive Borel measure given on Borel sets by
`ν_α(E) = ∫₀^∞ 𝒩(0,2sP)(E) s^{α/2-1} ds`. -/
theorem lem_mixture_integration_ii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E →
      gaussianMixture N α E =
        ∫⁻ s in Set.Ioi (0 : ℝ), N s E * ENNReal.ofReal (s ^ (α / 2 - 1)) :=
  fun E hE => hN.gaussianMixtureOn_apply α measurableSet_Ioi le_rfl hE

set_option linter.unusedVariables false in
/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For every
nonnegative Borel `F`, `∫ F dν_α = ∫₀^∞ (∫ F d𝒩(0,2sP)) s^{α/2-1} ds`, both sides possibly
infinite. -/
theorem lem_mixture_integration_iii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ ξ, F ξ ∂gaussianMixture N α =
        ∫⁻ s in Set.Ioi (0 : ℝ), (∫⁻ ξ, F ξ ∂N s) * ENNReal.ofReal (s ^ (α / 2 - 1)) :=
  fun F hF => hN.lintegral_gaussianMixtureOn α measurableSet_Ioi le_rfl hF

set_option linter.unusedVariables false in
/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For
complex `F` the integration formula holds when `∫ |F| dν_α < ∞`. -/
theorem lem_mixture_integration_iv {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ F : H → ℂ, Integrable F (gaussianMixture N α) →
      ∫ ξ, F ξ ∂gaussianMixture N α =
        ∫ s in Set.Ioi (0 : ℝ), (∫ ξ, F ξ ∂N s) * ((s ^ (α / 2 - 1) : ℝ) : ℂ) :=
  fun F hF => hN.integral_gaussianMixtureOn α measurableSet_Ioi le_rfl hF

/-! ### Lemma `lem:mixture-character` -/

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  For `z ≠ 0` the quadratic
form `q = ⟨Pz,z⟩` is positive. -/
theorem lem_mixture_character_i {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) (z : H)
    (hz : z ≠ 0) :
    0 < ⟪P z, z⟫ :=
  hP.inner_pos hz

set_option linter.unusedVariables false in
/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  The characteristic
functionals of the truncated mixtures `ν_α^{ε,M} = ∫_ε^M 𝒩(0,2sP) s^{α/2-1} ds` converge, as
`ε ↓ 0` and `M ↑ ∞`, to `Γ(α/2) q^{-α/2}`. -/
theorem lem_mixture_character_ii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (z : H)
    (hz : z ≠ 0) :
    Tendsto (fun εM : ℝ × ℝ => charFun (gaussianMixtureOn N α (Set.Ioo εM.1 εM.2)) z)
      ((𝓝[>] (0 : ℝ)) ×ˢ atTop)
      (𝓝 ((Real.Gamma (α / 2) * ⟪P z, z⟫ ^ (-(α / 2)) : ℝ) : ℂ)) := by
  set q : ℝ := ⟪P z, z⟫ with hq_def
  have hq : 0 < q := hP.inner_pos hz
  -- the integrand of the Gamma integral
  set g : ℝ → ℂ := fun s => ((Real.exp (-s * q) * s ^ (α / 2 - 1) : ℝ) : ℂ) with hg_def
  have hreal : IntegrableOn (fun s : ℝ => Real.exp (-s * q) * s ^ (α / 2 - 1)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := α / 2 - 1) (p := 1) (b := q)
      (by linarith) le_rfl hq
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring_nf
  have hg_int : IntegrableOn g (Set.Ioi 0) := hreal.ofReal
  -- the truncated mixtures have the truncated Gamma integrals as characteristic functionals
  have hform : ∀ ε M : ℝ, 0 < ε →
      charFun (gaussianMixtureOn N α (Set.Ioo ε M)) z =
        ∫ s in Set.Ioi (0 : ℝ), (Set.Ioo ε M).indicator g s := by
    intro ε M hε
    have hsub : Set.Ioo ε M ⊆ Set.Ioi 0 := fun s hs => lt_trans hε hs.1
    -- finiteness of the truncated mixture
    have hfin : IsFiniteMeasure (gaussianMixtureOn N α (Set.Ioo ε M)) := by
      constructor
      rw [hN.gaussianMixtureOn_univ α measurableSet_Ioo hsub]
      have hint : IntegrableOn (fun s : ℝ => s ^ (α / 2 - 1)) (Set.Ioo ε M) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioo_subset_Icc_self
        exact continuousOn_id.rpow_const fun s hs => Or.inl (lt_of_lt_of_le hε hs.1).ne'
      have := hint.hasFiniteIntegral
      rwa [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioo
        fun s hs => Real.rpow_nonneg (lt_trans hε hs.1).le _)] at this
    have hchar : Integrable (fun ξ : H => Complex.exp (((⟪ξ, z⟫ : ℝ) : ℂ) * Complex.I))
        (gaussianMixtureOn N α (Set.Ioo ε M)) := by
      refine (integrable_const (1 : ℝ) (μ := gaussianMixtureOn N α (Set.Ioo ε M))).mono'
        (by fun_prop : Continuous fun ξ : H =>
        Complex.exp (((⟪ξ, z⟫ : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    rw [charFun_apply, hN.integral_gaussianMixtureOn α measurableSet_Ioo hsub hchar,
      integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr hsub]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs' : 0 < s := lt_trans hε hs.1
    rw [← charFun_apply, hN.charFun_eq hs', hg_def]
    simp only [← hq_def]
    push_cast
    ring_nf
  -- the limit of the truncated Gamma integrals
  have hlim : Tendsto (fun εM : ℝ × ℝ => ∫ s in Set.Ioi (0 : ℝ), (Set.Ioo εM.1 εM.2).indicator g s)
      ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 (∫ s in Set.Ioi (0 : ℝ), g s)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖g s‖)
      (Eventually.of_forall fun εM => hg_int.aestronglyMeasurable.indicator measurableSet_Ioo)
      (Eventually.of_forall fun εM => Eventually.of_forall fun s => norm_indicator_le_norm_self _ _)
      hg_int.norm ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have h1 : ∀ᶠ εM : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ atTop, εM.1 < s :=
      ((eventually_lt_nhds hs).filter_mono nhdsWithin_le_nhds).prod_inl atTop
    have h2 : ∀ᶠ εM : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ atTop, s < εM.2 :=
      (eventually_gt_atTop s).prod_inr (𝓝[>] (0 : ℝ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1, h2] with εM hε hM
    rw [Set.indicator_of_mem (show s ∈ Set.Ioo εM.1 εM.2 from ⟨hε, hM⟩)]
  have hval : ∫ s in Set.Ioi (0 : ℝ), g s =
      ((Real.Gamma (α / 2) * ⟪P z, z⟫ ^ (-(α / 2)) : ℝ) : ℂ) := by
    have hc := Complex.ofRealCLM.integral_comp_comm hreal
    simp only [Complex.ofRealCLM_apply] at hc
    rw [hg_def, hc, ← hq_def]
    congr 1
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := α / 2) (r := q) (by positivity) hq
    have hfun : (fun s : ℝ => Real.exp (-s * q) * s ^ (α / 2 - 1)) =
        fun t : ℝ => t ^ (α / 2 - 1) * Real.exp (-(q * t)) := by
      funext t
      rw [mul_comm, neg_mul, mul_comm t]
    rw [hfun, h, Real.rpow_neg hq.le, one_div, Real.inv_rpow hq.le, mul_comm]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [(eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).prod_inl atTop]
    with εM hε
  exact (hform εM.1 εM.2 hε).symm

set_option linter.unusedSectionVars false in
/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  The limit is the Gamma
integral `∫₀^∞ e^{-sq} s^{α/2-1} ds = Γ(α/2) q^{-α/2}`. -/
theorem lem_mixture_character_iii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) {α : ℝ}
    (hα : 0 < α) (z : H) (hz : z ≠ 0) :
    ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * ⟪P z, z⟫) * s ^ (α / 2 - 1) =
      Real.Gamma (α / 2) * ⟪P z, z⟫ ^ (-(α / 2)) := by
  have hq : 0 < ⟪P z, z⟫ := hP.inner_pos hz
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := α / 2) (r := ⟪P z, z⟫)
    (by positivity) hq
  have hfun : (fun s : ℝ => Real.exp (-s * ⟪P z, z⟫) * s ^ (α / 2 - 1)) =
      fun t : ℝ => t ^ (α / 2 - 1) * Real.exp (-(⟪P z, z⟫ * t)) := by
    funext t
    rw [mul_comm, neg_mul, mul_comm t]
  rw [hfun, h, Real.rpow_neg hq.le, one_div, Real.inv_rpow hq.le, mul_comm]

set_option linter.unusedVariables false in
/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  In contrast, the character
`ξ ↦ e^{i⟨z,ξ⟩}` is not integrable against `ν_α`, so the limit is not a Lebesgue integral. -/
theorem lem_mixture_character_iv (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) (z : H) (hz : z ≠ 0) :
    ¬ Integrable (fun ξ : H => Complex.exp ((⟪z, ξ⟫ : ℝ) * Complex.I)) (gaussianMixture N α) := by
  intro h
  have h1 := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h1
  have h2 : (fun ξ : H => ‖Complex.exp ((⟪z, ξ⟫ : ℝ) * Complex.I)‖ₑ) = fun _ => 1 := by
    funext ξ
    rw [← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
  rw [h2, lintegral_const, hN.gaussianMixture_univ α, one_mul] at h1
  exact lt_irrefl _ h1

/-! ### Corollary `cor:finite-backprojection` -/

section FiniteDim

open OperatorRidgelet.FiniteDim

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  If
`f ∈ L²(p dx)` with `g = f p ∈ 𝒮(ℝ^m)`, then `f ∈ 𝒟_α`. -/
theorem cor_finite_backprojection_i {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    hf.toLp f ∈ spectralCore (densityMeasure p) (directionMeasure m α) := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  The
representative of the frame operator against the pivot measure is the Riesz potential
`t_f = ∫ e^{i⟨x,ξ⟩} ĝ(ξ) ν_α(dξ) = k_{m,α} (-Δ)^{-(m-α)/2} g`. -/
theorem cor_finite_backprojection_ii {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    ∀ x, frameRepresentative (directionMeasure m α) g x =
      frameConst m α * fracLaplacian (-((m - α) / 2)) g x := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  For a
band-pass `ρ`, the synthesis `S_ρ R_ρ f`, i.e. the functional `h ↦ ⟨R_ρ f, R_ρ h⟩_{L²(λ_α)}` on
`𝒟_α`, is represented against the pivot measure by `C^{(α)}_ρ t_f`. -/
theorem cor_finite_backprojection_iii {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ h : Lp ℂ 2 (densityMeasure p), h ∈ spectralCore (densityMeasure p) (directionMeasure m α) →
      ∫ q, ridgelet (densityMeasure p) ρ f q * (starRingEnd ℂ) (ridgelet (densityMeasure p) ρ h q)
          ∂parameterMeasure (directionMeasure m α) =
        admissibilityConst α ρ *
          ∫ x, frameRepresentative (directionMeasure m α) g x * (starRingEnd ℂ) (h x)
            ∂densityMeasure p := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  The
distributional reconstruction `f = p^{-1} (k_{m,α} C^{(α)}_ρ)^{-1} (-Δ)^{(m-α)/2} S_ρ R_ρ f`,
with `S_ρ R_ρ f` represented by `C^{(α)}_ρ t_f`: tested against Schwartz functions `φ`,
`∫ f φ p dx = (k C)^{-1} ∫ (C t_f) (-Δ)^{(m-α)/2} φ dx`. -/
theorem cor_finite_backprojection_iv {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ φ : SchwartzMap (Euclid m) ℂ,
      ∫ x, f x * φ x ∂densityMeasure p =
        ((frameConst m α * admissibilityConst α ρ)⁻¹ : ℝ) *
          ∫ x, (admissibilityConst α ρ * frameRepresentative (directionMeasure m α) g x) *
            fracLaplacian ((m - α) / 2) φ x := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  With
Lebesgue direction measure and `α = m`, the multiplier is one and `k = (2π)^m`:
`t_f = (2π)^m g`. -/
theorem cor_finite_backprojection_v {m : ℕ} (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x)
    (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m} (hQ : IsTraceClassCovariance Q)
    [IsProbabilityMeasure (densityMeasure p)] (hpQ : IsCenteredGaussian Q (densityMeasure p))
    (f : Euclid m → ℂ) (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    ∀ x, frameRepresentative volume g x = ((2 * Real.pi) ^ m : ℝ) * (f x * p x) := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  With
Lebesgue direction measure and `α = m`, `S_ρ R_ρ f` is represented against the pivot measure by
`(2π)^m C^{(m)}_ρ f p`, that is `f = (2π)^{-m} (C^{(m)}_ρ)^{-1} p^{-1} S_ρ R_ρ f`. -/
theorem cor_finite_backprojection_vi {m : ℕ} (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x)
    (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m} (hQ : IsTraceClassCovariance Q)
    [IsProbabilityMeasure (densityMeasure p)] (hpQ : IsCenteredGaussian Q (densityMeasure p))
    (f : Euclid m → ℂ) (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ h : Lp ℂ 2 (densityMeasure p), h ∈ spectralCore (densityMeasure p) volume →
      ∫ q, ridgelet (densityMeasure p) ρ f q * (starRingEnd ℂ) (ridgelet (densityMeasure p) ρ h q)
          ∂parameterMeasure (volume : Measure (Euclid m)) =
        ∫ x, (((2 * Real.pi) ^ m * admissibilityConst m ρ : ℝ) : ℂ) * (f x * p x) *
          (starRingEnd ℂ) (h x) ∂densityMeasure p := by
  sorry

end FiniteDim

/-! ### Proposition `prop:dilation-obstruction` -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  The sets `E_t` are Borel. -/
theorem prop_dilation_obstruction_i_a (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) :
    ∀ t : ℝ, MeasurableSet (strongLawSet e w t) := by
  intro t
  unfold strongLawSet
  refine measurableSet_tendsto (𝓝 t)
    (f := fun n : ℕ => fun x : H => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ⟪x, e j⟫ ^ 2 / w j) ?_
  intro n
  apply Continuous.measurable
  fun_prop

set_option linter.unusedVariables false in
omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  The sets `E_t` are pairwise
disjoint. -/
theorem prop_dilation_obstruction_i_b (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) :
    ∀ t t' : ℝ, t ≠ t' → Disjoint (strongLawSet e w t) (strongLawSet e w t') := by
  intro t t' htt'
  exact Set.disjoint_left.mpr fun x hx hx' => htt' (tendsto_nhds_unique hx hx')

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  For `t > 0`,
`𝒩(0,tW)(E_t) = 1`. -/
theorem prop_dilation_obstruction_i_c (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γ : ℝ → Measure H)
    (hγ : ∀ t : ℝ, 0 < t → IsCenteredGaussian (t • W) (γ t)) :
    ∀ t : ℝ, 0 < t → γ t (strongLawSet e w t) = 1 := by
  sorry

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  Consequently a σ-finite
measure dominates `𝒩(0,tW)` for at most countably many `t > 0`. -/
theorem prop_dilation_obstruction_i_d (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γ : ℝ → Measure H)
    (hγ : ∀ t : ℝ, 0 < t → IsCenteredGaussian (t • W) (γ t)) :
    ∀ ν : Measure H, SigmaFinite ν → Set.Countable {t : ℝ | 0 < t ∧ γ t ≪ ν} := by
  sorry

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  For a bounded Borel `r`
with `{r ≠ 0}` of positive Lebesgue measure, no finite complex Borel measure `Γ = h m` on
`H × ℝ` (a finite measure `m` with an integrable density `h`) has bias slices
`Γ⁺_ω(E) = ∫_{E×ℝ} e^{iωc} Γ(da,dc) = r(ω) (D_{1/ω})_# 𝒩(0,W)(E)` for almost every `ω ≠ 0`. -/
theorem prop_dilation_obstruction_ii (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γW : Measure H) (hγW : IsCenteredGaussian W γW)
    (r : ℝ → ℝ) (hr : Measurable r) (hrb : ∃ M : ℝ, ∀ ω, |r ω| ≤ M)
    (hr0 : 0 < volume {ω : ℝ | r ω ≠ 0}) :
    ¬ ∃ m : Measure (H × ℝ), IsFiniteMeasure m ∧ ∃ h : H × ℝ → ℂ, Integrable h m ∧
      ∀ᵐ ω ∂(volume : Measure ℝ), ω ≠ 0 → ∀ E : Set H, MeasurableSet E →
        ∫ q in E ×ˢ Set.univ, Complex.exp ((ω * q.2 : ℝ) * Complex.I) * h q ∂m =
          (r ω : ℂ) * (((γW.map fun a => ω⁻¹ • a) E).toReal : ℂ) := by
  sorry

/-! ### Theorem `thm:general-weights` -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(i) for the
abstract pair: `R_ρ f ∈ L²(λ)` for `f ∈ 𝒟_{μ,ν}` and `α`-admissible `ρ`. -/
theorem thm_general_weights_plancherel_memLp (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure ν) :=
  memLp_ridgelet μ hν hρ ((Lp.memLp f).integrable one_le_two) (Lp.memLp f) hf

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(i) for the
abstract pair: the Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_{μ,ν}}`. -/
theorem thm_general_weights_plancherel (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂)
    (f g : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) (hg : g ∈ spectralCore μ ν) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ ν f g :=
  integral_ridgelet_mul_conj μ hν hρ₁ hρ₂ ((Lp.memLp f).integrable one_le_two) (Lp.memLp f)
    ((Lp.memLp g).integrable one_le_two) (Lp.memLp g) hf hg

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: the unique bounded extension `R_ρ : 𝓔_{μ,ν} → L²(λ)`. -/
theorem thm_general_weights_extension (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f :=
  existsUnique_ridgeletExtensionCLM hν hρ

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: `‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_{μ,ν}}`. -/
theorem thm_general_weights_extension_norm (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, ‖R G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  intro G
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact norm_ridgeletExtensionCLM_sq hν hρ G

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: the extension has closed range. -/
theorem thm_general_weights_extension_closed_range (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    IsClosed (Set.range R) := by
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact isClosed_range_ridgeletExtensionCLM hν hρ

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: `R_ρ = W_ρ U`. -/
theorem thm_general_weights_extension_coefficient (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, R G = spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ) := by
  intro G
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact ridgeletExtensionCLM_eq_spectralCoefficient hν hα hρ μ G

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(iii) for the
abstract pair: `R_ρ f = 0` `λ`-a.e. implies `f = 0` `μ`-a.e. for `f ∈ L²(μ)`. -/
theorem thm_general_weights_injective (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure ν] 0) :
    f =ᵐ[μ] 0 :=
  ae_eq_zero_of_ridgelet_ae_eq_zero μ hα hν hρ (hf.integrable one_le_two) h

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:general-weights]** Abstract-weight extension.  `1 ∈ 𝒟_{μ,ν}` if and only if
`∫ |μ̂(ξ)|² ν(dξ) < ∞`. -/
theorem thm_general_weights_one_mem_iff (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) :
    MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) ∈ spectralCore μ ν ↔
      Integrable (fun ξ : H => ‖charFun μ ξ‖ ^ 2) ν := by
  rw [mem_spectralCore_iff]
  have h1 : gaussFourier μ
      ((MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) : Lp ℂ 2 μ) : H → ℂ) =
      fun ξ => charFun μ (-ξ) := by
    funext ξ
    rw [← gaussFourier_one]
    simp only [gaussFourier]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := μ) (p := 2))] with x hx
    rw [hx]
  have h2 : (fun ξ : H => ‖charFun μ (-ξ)‖ ^ 2) = fun ξ => ‖charFun μ ξ‖ ^ 2 := by
    funext ξ
    rw [charFun_neg, Complex.norm_conj]
  rw [h1, memLp_two_iff_integrable_sq_norm (f := fun ξ => charFun μ (-ξ))
    (stronglyMeasurable_charFun.comp_measurable measurable_neg).aestronglyMeasurable, h2]

/-! ### Example `ex:bandlimited-filter` -/

section Filters

open OperatorRidgelet.Filters

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The prescribed
Fourier transform `ρ̂_bp` is smooth. -/
theorem ex_bandlimited_filter_i : ContDiff ℝ (⊤ : ℕ∞) bandPassHat :=
  contDiff_bandPassHat

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
nonpositive. -/
theorem ex_bandlimited_filter_ii : ∀ ω : ℝ, bandPassHat ω ≤ 0 := by
  intro ω
  unfold bandPassHat bump
  split_ifs
  · exact neg_nonpos.mpr (Real.exp_pos _).le
  · simp

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
nonzero. -/
theorem ex_bandlimited_filter_iii : bandPassHat ≠ 0 := by
  intro h
  have := congrFun h (3 / 2)
  norm_num [bandPassHat, bump] at this

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
supported in `{1 ≤ |ω| ≤ 2}`. -/
theorem ex_bandlimited_filter_iv : tsupport bandPassHat ⊆ {ω : ℝ | 1 ≤ |ω| ∧ |ω| ≤ 2} := by
  apply closure_minimal
  · intro ω hω
    simp only [Function.mem_support, bandPassHat, bump] at hω
    by_cases h : |2 * |ω| - 3| < 1
    · rw [abs_lt] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rw [if_neg h] at hω
      simp at hω
  · have : {ω : ℝ | 1 ≤ |ω| ∧ |ω| ≤ 2} = {ω : ℝ | 1 ≤ |ω|} ∩ {ω : ℝ | |ω| ≤ 2} := rfl
    rw [this]
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The inverse
Fourier transform `ρ_bp` of `ρ̂_bp` is a real Schwartz function. -/
theorem ex_bandlimited_filter_v : ⇑bandPass = bandPassFun :=
  coe_bandPass

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` is even. -/
theorem ex_bandlimited_filter_vi : ∀ t : ℝ, bandPass (-t) = bandPass t := by
  intro t
  rw [coe_bandPass]
  unfold bandPassFun
  congr 2
  have h := Measure.integral_comp_mul_left
    (fun ω : ℝ => (bandPassHat ω : ℂ) * Complex.exp ((t * ω : ℝ) * Complex.I)) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul, bandPassHat_neg] at h
  rw [← h]
  congr 1
  funext ω
  congr 2
  push_cast
  ring

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The Fourier
transform of `ρ_bp` is the prescribed `ρ̂_bp`. -/
theorem ex_bandlimited_filter_vii : ∀ ω : ℝ, filterFourier bandPass ω = (bandPassHat ω : ℂ) :=
  filterFourier_bandPass

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` satisfies
the band-pass condition. -/
theorem ex_bandlimited_filter_viii : IsBandPass bandPass := by
  have hF : filterFourier bandPass = fun ω => (bandPassHat ω : ℂ) := funext filterFourier_bandPass
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply ex_bandlimited_filter_iii
    funext ω
    have h1 := filterFourier_bandPass ω
    rw [h, FunLike.coe_zero, filterFourier_zero] at h1
    exact_mod_cast h1.symm
  · rw [hF]
    exact Complex.ofRealCLM.contDiff.comp ex_bandlimited_filter_i
  · rw [hF]
    exact hasCompactSupport_bandPassHat.comp_left Complex.ofReal_zero
  · rw [hF]
    intro h0
    have hsub : tsupport (fun ω => (bandPassHat ω : ℂ)) ⊆ tsupport bandPassHat :=
      closure_mono (Function.support_comp_subset Complex.ofReal_zero bandPassHat)
    have := (ex_bandlimited_filter_iv (hsub h0)).1
    norm_num at this

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` is
`α`-admissible for every `α > 0`. -/
theorem ex_bandlimited_filter_ix : ∀ α : ℝ, 0 < α → IsAdmissible α bandPass :=
  def_admissible_filter bandPass ex_bandlimited_filter_viii

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  Multiplying by
`(C^{(α)}_{ρ_bp})^{-1/2}` normalizes the admissibility constant to one. -/
theorem ex_bandlimited_filter_x :
    ∀ α : ℝ, 0 < α →
      admissibilityConst α ((Real.sqrt (admissibilityConst α bandPass))⁻¹ • bandPass) = 1 := by
  intro α hα
  have hpos : 0 < admissibilityConst α bandPass := (ex_bandlimited_filter_ix α hα).pos
  rw [admissibilityConst_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-! ### Example `ex:mexican-hat` -/

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ_MH(t) = (1 - t²) e^{-t²/2}` is a Schwartz
function. -/
theorem ex_mexican_hat_i : ⇑mexicanHat = mexicanHatFun := by
  have h : ∃ ρ : SchwartzMap ℝ ℝ, ⇑ρ = mexicanHatFun :=
    ⟨Real.polynomialGaussianSchwartz (1 - Polynomial.X ^ 2), by
      funext t
      simp [mexicanHatFun]⟩
  unfold mexicanHat
  rw [dif_pos h]
  exact h.choose_spec

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ̂_MH(ω) = √(2π) ω² e^{-ω²/2}`. -/
theorem ex_mexican_hat_ii :
    ∀ ω : ℝ, filterFourier mexicanHat ω =
      ((Real.sqrt (2 * Real.pi) * ω ^ 2 * Real.exp (-ω ^ 2 / 2) : ℝ) : ℂ) := by
  intro ω
  rw [filterFourier_eq_fourier, ex_mexican_hat_i]
  have hfun : (fun t : ℝ => (mexicanHatFun t : ℂ)) =
      fun t => (((1 - t ^ 2) * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) := rfl
  rw [hfun, Real.fourier_one_sub_sq_mul_gaussian]
  have h2π : 2 * Real.pi * ((2 * Real.pi)⁻¹ * ω) = ω := by
    field_simp
  rw [h2π]

/-- **Example [ex:mexican-hat]** Mexican hat.  Under the standing assumption `α > 0`, `ρ_MH` is
`α`-admissible exactly for `α < 5`. -/
theorem ex_mexican_hat_iii : ∀ α : ℝ, 0 < α → (IsAdmissible α mexicanHat ↔ α < 5) := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  For `0 < α < 5`,
`C^{(α)}_{ρ_MH} = Γ((5-α)/2)`. -/
theorem ex_mexican_hat_iv :
    ∀ α : ℝ, 0 < α → α < 5 → admissibilityConst α mexicanHat = Real.Gamma ((5 - α) / 2) := by
  intro α hα hα5
  unfold admissibilityConst
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have hae : (fun ω : ℝ => ‖filterFourier mexicanHat ω‖ ^ 2 * |ω| ^ (-α)) =ᵐ[volume]
      fun ω => (2 * Real.pi) * (|ω| ^ (4 - α) * Real.exp (-ω ^ 2)) := by
    filter_upwards [h0] with ω hω
    rw [ex_mexican_hat_ii ω, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _), abs_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity), ← pow_mul, ← Real.exp_nat_mul]
    have e1 : (|ω| ^ (2 * 2) : ℝ) = |ω| ^ (4 : ℝ) := by
      rw [← Real.rpow_natCast]
      norm_num
    have e2 : |ω| ^ (4 : ℝ) * |ω| ^ (-α) = |ω| ^ (4 - α) := by
      rw [← Real.rpow_add (abs_pos.mpr hω)]
      ring_nf
    have e3 : Real.exp (((2 : ℕ) : ℝ) * (-ω ^ 2 / 2)) = Real.exp (-ω ^ 2) := by
      congr 1
      push_cast
      ring
    rw [e1, e3, ← e2]
    ring
  rw [integral_congr_ae hae, integral_const_mul,
    Real.integral_abs_rpow_mul_exp_neg_sq (by linarith)]
  have h5 : (4 - α + 1) / 2 = (5 - α) / 2 := by ring
  rw [h5]
  field_simp

/-- **Example [ex:mexican-hat]** Mexican hat.  In particular `C^{(1)}_{ρ_MH} = 1`. -/
theorem ex_mexican_hat_v : admissibilityConst 1 mexicanHat = 1 := by
  rw [ex_mexican_hat_iv 1 one_pos (by norm_num)]
  have : ((5 : ℝ) - 1) / 2 = ((1 : ℕ) : ℝ) + 1 := by norm_num
  rw [this, Real.Gamma_nat_eq_factorial]
  simp

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ_MH` is not band pass. -/
theorem ex_mexican_hat_vi : ¬ IsBandPass mexicanHat := by
  intro h
  have hcs := h.hasCompactSupport
  have hsub : {ω : ℝ | ω ≠ 0} ⊆ Function.support (filterFourier mexicanHat) := by
    intro ω hω
    rw [Function.mem_support, ex_mexican_hat_ii]
    have : (Real.sqrt (2 * Real.pi) * ω ^ 2 * Real.exp (-ω ^ 2 / 2) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne' (pow_ne_zero 2 hω))
        (Real.exp_pos _).ne'
    exact_mod_cast this
  have huniv : (Set.univ : Set ℝ) ⊆ tsupport (filterFourier mexicanHat) := by
    have hd : Dense {ω : ℝ | ω ≠ 0} := by
      have : {ω : ℝ | ω ≠ 0} = ({0} : Set ℝ)ᶜ := by
        ext ω
        simp
      rw [this]
      exact dense_compl_singleton 0
    calc (Set.univ : Set ℝ) = closure {ω : ℝ | ω ≠ 0} := hd.closure_eq.symm
      _ ⊆ tsupport (filterFourier mexicanHat) := closure_mono hsub
  exact noncompact_univ ℝ (hcs.of_isClosed_subset isClosed_univ huniv)

end Filters

end OperatorRidgelet.Paper
