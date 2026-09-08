import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Filters.Defs
import OperatorRidgelet.ToMathlib.PositiveOperator
import OperatorRidgelet.ToMathlib.SchwartzFourier
import OperatorRidgelet.ToMathlib.FourierEven

/-!
# Auxiliary lemmas for Section 3 (the Gaussian-weighted ridgelet transform)

Ridgelet-specific facts used by the proofs of `OperatorRidgelet.Paper.Transform`: positivity of
the quadratic form of a trace-class covariance, the bridge between the manuscript's Fourier
transform `ρ̂(ω) = ∫ ρ(t) e^{-itω} dt` and Mathlib's `𝓕`, the nonvanishing of the Fourier
transform of a nonzero filter, the joint integrability of the ridgelet kernel, the integrated
forms of the homogeneity `(D_ω)_# ν = |ω|^{-α} ν`, and the smoothness of the explicit band-pass
Fourier transform of Appendix I.  General-purpose tools live in `OperatorRidgelet.ToMathlib`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace FourierTransform

/-! ### Trace-class covariances -/

section Covariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The quadratic form of an injective positive self-adjoint operator is positive definite. -/
theorem IsTraceClassCovariance.inner_pos {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) {z : H}
    (hz : z ≠ 0) : 0 < ⟪P z, z⟫ :=
  hP.isSelfAdjoint.isSymmetric.inner_map_self_pos_of_injective hP.inner_nonneg hP.injective hz

end Covariance

/-! ### The Fourier transform of a filter -/

section Fourier

/-- The manuscript's Fourier transform `ρ̂(ω) = ∫ ρ(t) e^{-itω} dt` is Mathlib's `𝓕` at the
rescaled frequency `ω / 2π`. -/
theorem filterFourier_eq_fourier (ρ : ℝ → ℝ) (ω : ℝ) :
    filterFourier ρ ω = 𝓕 (fun t => (ρ t : ℂ)) ((2 * Real.pi)⁻¹ * ω) := by
  unfold filterFourier lineFourier
  rw [LeanRidgelet.Fourier.angularFourierIntegralInner_eq_mathlib]
  rfl

/-- The Fourier transform of a nonzero real Schwartz function is nonzero. -/
theorem filterFourier_ne_zero {ρ : SchwartzMap ℝ ℝ} (hρ : ρ ≠ 0) : filterFourier ρ ≠ 0 := by
  intro h
  refine hρ (SchwartzMap.eq_zero_of_fourier_ofReal_eq_zero fun ω => ?_)
  have hω := congrFun h (2 * Real.pi * ω)
  rw [filterFourier_eq_fourier, Pi.zero_apply] at hω
  have h2 : (2 * Real.pi)⁻¹ * (2 * Real.pi * ω) = ω := by
    field_simp
  rwa [h2] at hω

end Fourier

/-! ### The ridgelet kernel -/

section Kernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- The kernel `(x, c) ↦ f(x) ρ(⟪a, x⟫ + c)` of the ridgelet transform is jointly integrable
against `μ ⊗ dc` for integrable `f` and Schwartz `ρ`. -/
theorem integrable_ridgelet_kernel (μ : Measure H) [IsFiniteMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    {f : H → ℂ} (hf : Integrable f μ) (a : H) :
    Integrable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ)) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun q : H × ℝ => f q.1 * (ρ (⟪a, q.1⟫ + q.2) : ℂ))
      (μ.prod volume) :=
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (Complex.continuous_ofReal.comp (ρ.continuous.comp
        (by fun_prop : Continuous fun q : H × ℝ => ⟪a, q.1⟫ + q.2))).aestronglyMeasurable
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

end Kernel

/-! ### Homogeneous direction measures -/

section Homogeneous

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The integrated form of homogeneity: `∫ F(ca) ν(da) = |c|^{-α} ∫ F dν` for `c ≠ 0`. -/
theorem IsHomogeneous.lintegral_smul {α : ℝ} {ν : Measure H} (hν : IsHomogeneous α ν) {c : ℝ}
    (hc : c ≠ 0) {F : H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ a, F (c • a) ∂ν = ENNReal.ofReal (|c| ^ (-α)) * ∫⁻ ξ, F ξ ∂ν := by
  rw [← lintegral_map hF (measurable_const_smul c), hν c hc, lintegral_smul_measure, smul_eq_mul]

/-- Homogeneity on preimages: `ν(D_c⁻¹ E) = |c|^{-α} ν(E)` for `c ≠ 0`. -/
theorem IsHomogeneous.measure_preimage_smul {α : ℝ} {ν : Measure H} (hν : IsHomogeneous α ν)
    {c : ℝ} (hc : c ≠ 0) {E : Set H} (hE : MeasurableSet E) :
    ν ((fun a => c • a) ⁻¹' E) = ENNReal.ofReal (|c| ^ (-α)) * ν E := by
  rw [← Measure.map_apply (measurable_const_smul c) hE, hν c hc, Measure.smul_apply, smul_eq_mul]

/-- Changing a Borel function on a `ν`-null set changes `(a, ω) ↦ G(-ωa)` only on a
`ν ⊗ dω`-null set: for `ν`-almost every direction the two ray functions agree almost
everywhere. -/
theorem IsHomogeneous.ae_ae_eq_neg_smul {α : ℝ} {ν : Measure H} [SigmaFinite ν]
    (hν : IsHomogeneous α ν) {G G' : H → ℂ} (hG : Measurable G) (hG' : Measurable G')
    (hGG' : G =ᵐ[ν] G') :
    ∀ᵐ a ∂ν, (fun ω : ℝ => G (-(ω • a))) =ᵐ[volume] fun ω : ℝ => G' (-(ω • a)) := by
  set E : Set H := {ξ | G ξ ≠ G' ξ} with hE_def
  have hE : MeasurableSet E := (measurableSet_eq_fun hG hG').compl
  have hE0 : ν E = 0 := ae_iff.mp hGG'
  set S : Set (H × ℝ) := (fun p : H × ℝ => -(p.2 • p.1)) ⁻¹' E with hS_def
  have hS : MeasurableSet S :=
    (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable hE
  have hnull : (ν.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
      rw [ae_iff]
      simp
    rw [← lintegral_zero (μ := (volume : Measure ℝ))]
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with ω hω
    have : (fun a : H => (a, ω)) ⁻¹' S = (fun a : H => (-ω) • a) ⁻¹' E := by
      ext a
      simp [hS_def, neg_smul]
    rw [this, hν.measure_preimage_smul (neg_ne_zero.mpr hω) hE, hE0, mul_zero]
  have := (Measure.measure_prod_null hS).mp hnull
  filter_upwards [this] with a ha
  rw [Pi.zero_apply] at ha
  rw [Filter.EventuallyEq, ae_iff]
  exact ha

/-- For `G ∈ L¹(ν)`, the ray function `ω ↦ G(-ωa)` is integrable on compact subsets of
`ℝ ∖ {0}` for `ν`-almost every direction `a`. -/
theorem IsHomogeneous.ae_integrableOn_neg_smul {α : ℝ} (hα : 0 < α) {ν : Measure H}
    [SigmaFinite ν] (hν : IsHomogeneous α ν) {G : H → ℂ} (hG : Measurable G)
    (hG₁ : Integrable G ν) :
    ∀ᵐ a ∂ν, ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I →
      IntegrableOn (fun ω : ℝ => G (-(ω • a))) I := by
  set J : ℕ → Set ℝ := fun n => {ω | 1 / ((n : ℝ) + 1) ≤ |ω| ∧ |ω| ≤ (n : ℝ) + 1} with hJ_def
  have hJmeas : ∀ n, MeasurableSet (J n) := fun n =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hGm : Measurable fun p : H × ℝ => G (-(p.2 • p.1)) :=
    hG.comp (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable
  have hJint : ∀ n, ∀ᵐ a ∂ν, IntegrableOn (fun ω : ℝ => G (-(ω • a))) (J n) := by
    intro n
    have hprod : Integrable (fun p : H × ℝ => G (-(p.2 • p.1)))
        (ν.prod (volume.restrict (J n))) := by
      refine ⟨hGm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hGm.enorm.aemeasurable]
      have hbound : ∀ ω ∈ J n, ∫⁻ a, ‖G (-(ω • a))‖ₑ ∂ν ≤
          ENNReal.ofReal (((n : ℝ) + 1) ^ α) * ∫⁻ ξ, ‖G ξ‖ₑ ∂ν := by
        intro ω hω
        have hpos : 0 < |ω| := lt_of_lt_of_le (by positivity) hω.1
        have hω0 : ω ≠ 0 := abs_pos.mp hpos
        have : (fun a : H => ‖G (-(ω • a))‖ₑ) = fun a => (fun ξ => ‖G ξ‖ₑ) ((-ω) • a) := by
          funext a
          simp [neg_smul]
        rw [this, hν.lintegral_smul (neg_ne_zero.mpr hω0) hG.enorm]
        gcongr
        rw [abs_neg]
        calc |ω| ^ (-α) ≤ (1 / ((n : ℝ) + 1)) ^ (-α) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hω.1 (by linarith)
          _ = ((n : ℝ) + 1) ^ α := by
              rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg]
      calc ∫⁻ ω in J n, ∫⁻ a, ‖G (-(ω • a))‖ₑ ∂ν
          ≤ ∫⁻ ω in J n, ENNReal.ofReal (((n : ℝ) + 1) ^ α) * ∫⁻ ξ, ‖G ξ‖ₑ ∂ν :=
            setLIntegral_mono' (hJmeas n) hbound
        _ = ENNReal.ofReal (((n : ℝ) + 1) ^ α) * (∫⁻ ξ, ‖G ξ‖ₑ ∂ν) * volume (J n) :=
            setLIntegral_const _ _
        _ < ⊤ := by
            refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) ?_
            · exact hasFiniteIntegral_iff_enorm.mp hG₁.hasFiniteIntegral
            · refine lt_of_le_of_lt (measure_mono (t := Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
                fun ω hω => abs_le.mp hω.2) ?_
              rw [Real.volume_Icc]
              exact ENNReal.ofReal_lt_top
    exact hprod.prod_right_ae
  rw [← ae_all_iff] at hJint
  filter_upwards [hJint] with a ha I hI hI0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, I ⊆ J n := by
    rcases I.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, Set.empty_subset _⟩
    obtain ⟨ω₀, hω₀I, hmin⟩ := hI.exists_isMinOn hne continuous_abs.continuousOn
    obtain ⟨ω₁, hω₁I, hmax⟩ := hI.exists_isMaxOn hne continuous_abs.continuousOn
    have hpos : 0 < |ω₀| := abs_pos.mpr fun h => hI0 (h ▸ hω₀I)
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hpos
    obtain ⟨n₂, hn₂⟩ := exists_nat_gt |ω₁|
    refine ⟨n₁ + n₂, fun ω hω => ⟨?_, ?_⟩⟩
    · calc 1 / ((↑(n₁ + n₂) : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
            gcongr
            linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]
        _ ≤ |ω₀| := hn₁.le
        _ ≤ |ω| := hmin hω
    · calc |ω| ≤ |ω₁| := hmax hω
        _ ≤ n₂ := hn₂.le
        _ ≤ (↑(n₁ + n₂) : ℝ) + 1 := by
            push_cast
            linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)]
  exact (ha n).mono_set hn

end Homogeneous

/-! ### The explicit band-pass filter -/

namespace Filters

/-- The bump `η` is `expNegInvGlue ∘ (1 - u²)`. -/
theorem bump_eq_expNegInvGlue (u : ℝ) : bump u = expNegInvGlue (1 - u ^ 2) := by
  unfold bump
  by_cases h : |u| < 1
  · rw [if_pos h]
    have hpos : 0 < 1 - u ^ 2 := by
      have := (sq_lt_one_iff_abs_lt_one u).mpr h
      linarith
    rw [expNegInvGlue, if_neg (not_le.mpr hpos)]
    congr 1
    rw [neg_div, one_div]
  · rw [if_neg h]
    have hle : 1 - u ^ 2 ≤ 0 := by
      have := (one_le_sq_iff_one_le_abs u).mpr (not_lt.mp h)
      linarith
    rw [expNegInvGlue.zero_of_nonpos hle]

/-- The bump `η` is smooth. -/
theorem contDiff_bump : ContDiff ℝ (⊤ : ℕ∞) bump := by
  have : bump = expNegInvGlue ∘ fun u : ℝ => 1 - u ^ 2 := funext bump_eq_expNegInvGlue
  rw [this]
  exact expNegInvGlue.contDiff.comp (by fun_prop)

/-- The prescribed Fourier transform `ρ̂_bp(ω) = -η(2|ω| - 3)` is smooth: away from the origin
`|ω|` is smooth, and near the origin `ρ̂_bp` vanishes identically. -/
theorem contDiff_bandPassHat : ContDiff ℝ (⊤ : ℕ∞) bandPassHat := by
  rw [contDiff_iff_contDiffAt]
  intro ω
  by_cases hω : ω = 0
  · subst hω
    have hev : bandPassHat =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with ω hω
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hω
      simp only [bandPassHat, bump]
      rw [if_neg]
      · simp
      · rw [abs_lt]
        push Not
        intro h
        linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have habs : ContDiffAt ℝ (⊤ : ℕ∞) (fun ω : ℝ => |ω|) ω := by
      have h : (fun ω : ℝ => |ω|) = (norm : ℝ → ℝ) := funext fun x => (Real.norm_eq_abs x).symm
      rw [h]
      exact contDiffAt_norm ℝ hω
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ω : ℝ => 2 * |ω| - 3) ω :=
      (contDiffAt_const.mul habs).sub contDiffAt_const
    exact (contDiff_bump.contDiffAt.comp ω h1).neg

end Filters

/-! ### The band-pass filter as a Schwartz function -/

namespace Filters

open scoped FourierTransform

theorem bandPassHat_neg (ω : ℝ) : bandPassHat (-ω) = bandPassHat ω := by
  simp [bandPassHat]

theorem bandPassHat_eq_zero_of_two_lt {ω : ℝ} (h : 2 < |ω|) : bandPassHat ω = 0 := by
  simp only [bandPassHat, bump]
  rw [if_neg]
  · simp
  · rw [abs_lt]
    push Not
    intro h1
    linarith

theorem hasCompactSupport_bandPassHat : HasCompactSupport bandPassHat :=
  HasCompactSupport.intro isCompact_Icc fun ω hω =>
    bandPassHat_eq_zero_of_two_lt (by
      by_contra h
      exact hω (abs_le.mp (not_lt.mp h)))

/-- The rescaled Fourier data `u ↦ ρ̂_bp(2πu)` is smooth with compact support. -/
theorem hasCompactSupport_bandPassHat_ofReal_comp :
    HasCompactSupport fun u : ℝ => (bandPassHat (2 * Real.pi * u) : ℂ) :=
  HasCompactSupport.intro isCompact_Icc fun u hu => by
    rw [bandPassHat_eq_zero_of_two_lt, Complex.ofReal_zero]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hu1 : 1 < |u| := by
      by_contra h
      exact hu (abs_le.mp (not_lt.mp h))
    nlinarith [Real.two_le_pi]

theorem contDiff_bandPassHat_ofReal_comp :
    ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ => (bandPassHat (2 * Real.pi * u) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_bandPassHat.comp (contDiff_const.mul contDiff_id))

/-- The rescaled Fourier data `u ↦ ρ̂_bp(2πu)` as a complex Schwartz function. -/
def bandPassHatSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_bandPassHat_ofReal_comp.toSchwartzMap contDiff_bandPassHat_ofReal_comp

theorem bandPassHatSchwartz_apply (u : ℝ) :
    bandPassHatSchwartz u = (bandPassHat (2 * Real.pi * u) : ℂ) := rfl

theorem bandPassHatSchwartz_even (u : ℝ) : bandPassHatSchwartz (-u) = bandPassHatSchwartz u := by
  rw [bandPassHatSchwartz_apply, bandPassHatSchwartz_apply, mul_neg, bandPassHat_neg]

/-- The band-pass filter as a real Schwartz function: the real part of the inverse Fourier
transform of the rescaled Fourier data. -/
def bandPassSchwartz : SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM (𝓕⁻ bandPassHatSchwartz)

/-- The inverse Fourier transform of the rescaled Fourier data is real. -/
theorem conj_fourierInv_bandPassHatSchwartz (t : ℝ) :
    (starRingEnd ℂ) (𝓕⁻ bandPassHatSchwartz t) = 𝓕⁻ bandPassHatSchwartz t := by
  rw [SchwartzMap.fourierInv_coe]
  exact Real.conj_fourierInv_ofReal_of_even (f := fun u => bandPassHat (2 * Real.pi * u))
    (fun u => by rw [mul_neg, bandPassHat_neg]) t

theorem ofReal_bandPassSchwartz_apply (t : ℝ) :
    (bandPassSchwartz t : ℂ) = 𝓕⁻ bandPassHatSchwartz t :=
  Complex.conj_eq_iff_re.mp (conj_fourierInv_bandPassHatSchwartz t)

/-- The Schwartz band-pass filter has the manuscript's values
`ρ_bp(t) = (2π)⁻¹ ∫ ρ̂_bp(ω) e^{itω} dω`. -/
theorem bandPassSchwartz_apply (t : ℝ) : bandPassSchwartz t = bandPassFun t := by
  unfold bandPassFun
  show Complex.reCLM (𝓕⁻ bandPassHatSchwartz t) = _
  rw [Complex.reCLM_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  have h := Measure.integral_comp_mul_left
    (fun ω : ℝ => (bandPassHat ω : ℂ) * Complex.exp ((t * ω : ℝ) * Complex.I)) (2 * Real.pi)
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [bandPassHatSchwartz_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem exists_schwartz_eq_bandPassFun : ∃ ρ : SchwartzMap ℝ ℝ, ⇑ρ = bandPassFun :=
  ⟨bandPassSchwartz, funext bandPassSchwartz_apply⟩

theorem coe_bandPass : ⇑bandPass = bandPassFun := by
  unfold bandPass
  rw [dif_pos exists_schwartz_eq_bandPassFun]
  exact exists_schwartz_eq_bandPassFun.choose_spec

/-- The Fourier transform of the band-pass filter is the prescribed `ρ̂_bp`. -/
theorem filterFourier_bandPass (ω : ℝ) : filterFourier bandPass ω = (bandPassHat ω : ℂ) := by
  rw [filterFourier_eq_fourier, coe_bandPass]
  have hreal : (fun t : ℝ => (bandPassFun t : ℂ)) =
      ((𝓕⁻ bandPassHatSchwartz : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext t
    rw [← bandPassSchwartz_apply, ofReal_bandPassSchwartz_apply]
  rw [hreal, ← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq,
    bandPassHatSchwartz_apply, mul_inv_cancel_left₀ (by positivity)]

end Filters

/-! ### The range of the weighted Fourier transform on the core -/

section Range

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

theorem gaussFourierLp_add (μ ν : Measure H) [IsFiniteMeasure μ] (f g : spectralCore μ ν) :
    gaussFourierLp μ ν (f + g) = gaussFourierLp μ ν f + gaussFourierLp μ ν g := by
  unfold gaussFourierLp
  rw [← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourier μ ((f + g : Lp ℂ 2 μ) : H → ℂ) ξ = _
  rw [gaussFourier_add]

theorem gaussFourierLp_zero (μ ν : Measure H) [IsFiniteMeasure μ] :
    gaussFourierLp μ ν 0 = 0 := by
  unfold gaussFourierLp
  rw [← MemLp.toLp_zero (MemLp.zero : MemLp (0 : H → ℂ) 2 ν)]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourier μ ((0 : Lp ℂ 2 μ) : H → ℂ) ξ = _
  rw [gaussFourier_zero']

theorem gaussFourierLp_smul (μ ν : Measure H) [IsFiniteMeasure μ] (c : ℂ)
    (f : spectralCore μ ν) :
    gaussFourierLp μ ν (c • f) = c • gaussFourierLp μ ν f := by
  unfold gaussFourierLp
  rw [← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  show gaussFourier μ ((c • f : Lp ℂ 2 μ) : H → ℂ) ξ = _
  rw [gaussFourier_smul]

/-- The range `𝒢_μ(𝒟)` of the weighted Fourier transform on the core, as a submodule of
`L²(ν)`. -/
def gaussFourierRange (μ ν : Measure H) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 ν) where
  carrier := Set.range (gaussFourierLp μ ν)
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, gaussFourierLp_add μ ν f g⟩
  zero_mem' := ⟨0, gaussFourierLp_zero μ ν⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨c • f, gaussFourierLp_smul μ ν c f⟩

theorem coe_gaussFourierRange (μ ν : Measure H) [IsFiniteMeasure μ] :
    (gaussFourierRange μ ν : Set (Lp ℂ 2 ν)) = Set.range (gaussFourierLp μ ν) := rfl

/-- `𝒦 = closure 𝒢_μ(𝒟)`: the span in the definition of `spectralRange` is redundant. -/
theorem spectralRange_eq_topologicalClosure (μ ν : Measure H) [IsFiniteMeasure μ] :
    spectralRange μ ν = (gaussFourierRange μ ν).topologicalClosure := by
  unfold spectralRange
  rw [← coe_gaussFourierRange, Submodule.span_eq]

end Range

/-! ### Scaling a filter -/

section Scaling

theorem filterFourier_smul (c : ℝ) (ρ : SchwartzMap ℝ ℝ) (ω : ℝ) :
    filterFourier (c • ρ) ω = (c : ℂ) * filterFourier ρ ω := by
  simp only [filterFourier, lineFourier, LeanRidgelet.Fourier.angularFourierIntegralInner,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem admissibilityConst_smul (α c : ℝ) (ρ : SchwartzMap ℝ ℝ) :
    admissibilityConst α (c • ρ) = c ^ 2 * admissibilityConst α ρ := by
  simp only [admissibilityConst, filterFourier_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc]
  rw [integral_const_mul]
  ring

end Scaling

end OperatorRidgelet
