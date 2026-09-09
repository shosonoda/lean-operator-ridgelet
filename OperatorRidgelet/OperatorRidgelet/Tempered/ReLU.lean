import OperatorRidgelet.Tempered.Basic
import OperatorRidgelet.Tempered.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Fourier transform of ReLU away from the origin

For a Schwartz function `φ` supported away from `0`, write `φ = ω² ψ` with `ψ = φ/ω²` Schwartz
(`SchwartzMap.exists_eq_inv_sq_mul`).  In the manuscript convention the Fourier transform of
`ω² ψ` is `-(ψ̂)''`, so that
`⟨ReLU^, φ⟩ = ∫ ReLU(x) φ̂(x) dx = -∫_0^∞ x (ψ̂)''(x) dx = -ψ̂(0) = -∫ φ(ω) ω^{-2} dω`,
by two integrations by parts on `(0, ∞)`.  This is Corollary `cor:relu-admissible`(ii); the
formula and the positivity of the ReLU admissibility constant `C^{(α)}_{ReLU,ρ}` for even
nonpositive band-pass `ρ̂` (parts (iii)–(v)) and the instance `ρ = ρ_bp` follow.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform

/-! ### The angular Fourier transform and derivatives -/

/-- `x ↦ xⁿ φ(x)` is integrable for Schwartz `φ`. -/
theorem integrable_pow_real_smul_schwartz (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n • φ x := by
  refine (φ.integrable_pow_mul volume n).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_id.pow n).smul φ.continuous).aestronglyMeasurable
  · simp

/-- For `φ = ω² ψ`, the angular Fourier transform of `φ` is `-(ψ̂)''`. -/
theorem angularFourierSchwartz_eq_neg_iteratedDeriv_two {ψ φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ ω : ℝ, φ ω = (ω : ℂ) ^ 2 * ψ ω) (x : ℝ) :
    angularFourierSchwartz φ x = -iteratedDeriv 2 (angularFourierSchwartz ψ) x := by
  have h2 := Real.iteratedDeriv_fourier (f := ⇑ψ) (N := ⊤) (n := 2)
    (fun n _ => integrable_pow_real_smul_schwartz ψ n) le_top
  have h3 : (fun ω : ℝ => (-2 * (Real.pi : ℂ) * I * ω) ^ 2 • ψ ω) =
      (-2 * (Real.pi : ℂ) * I) ^ 2 • (⇑φ) := by
    funext ω
    rw [Pi.smul_apply, hφ ω, smul_eq_mul, smul_eq_mul]
    ring
  have h4 : 𝓕 ((-2 * (Real.pi : ℂ) * I) ^ 2 • (⇑φ)) = (-2 * (Real.pi : ℂ) * I) ^ 2 • 𝓕 (⇑φ) :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [h3, h4] at h2
  have hang : angularFourierSchwartz ψ = fun x => 𝓕 (⇑ψ) ((2 * Real.pi)⁻¹ * x) :=
    funext (angularFourierSchwartz_eq_fourier ψ)
  have hsm : ContDiff ℝ 2 (𝓕 (⇑ψ)) := (𝓕 ψ).smooth 2
  rw [hang, iteratedDeriv_comp_const_smul hsm (2 * Real.pi)⁻¹, h2,
    angularFourierSchwartz_eq_fourier]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (-2 * (Real.pi : ℂ) * I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
    rw [mul_pow, I_sq]
    ring
  rw [hI]
  push_cast
  field_simp
  ring

/-! ### Integration by parts on the half-line -/

/-- `x ↦ x φ(x)` as a Schwartz function. -/
def coordMulSchwartz (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) φ

theorem coordMulSchwartz_apply (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordMulSchwartz φ x = (x : ℂ) * φ x := by
  have hg : Function.HasTemperateGrowth fun x : ℝ => (x : ℂ) :=
    Function.Complex.hasTemperateGrowth_ofReal
  rw [coordMulSchwartz, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

/-- `deriv φ` as a Schwartz function. -/
theorem coe_derivCLM (φ : SchwartzMap ℝ ℂ) : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ :=
  funext (SchwartzMap.derivCLM_apply ℂ φ)

/-- `∫_0^∞ x φ''(x) dx = φ(0)` for Schwartz `φ`. -/
theorem integral_Ioi_coord_mul_iteratedDeriv_two (φ : SchwartzMap ℝ ℂ) :
    ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) * iteratedDeriv 2 φ x = φ 0 := by
  have h2 : iteratedDeriv 2 (⇑φ) = deriv (deriv φ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * deriv φ x - φ x)
      ((x : ℂ) * iteratedDeriv 2 φ x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    have hφ1 : HasDerivAt (⇑φ) (deriv φ x) x :=
      ((φ.smooth 1).differentiable one_ne_zero x).hasDerivAt
    have hφ2 : HasDerivAt (deriv φ) (deriv (deriv φ) x) x := by
      have := (φ.smooth 2).differentiable_iteratedDeriv 1 (by norm_num) x
      rw [iteratedDeriv_one] at this
      exact this.hasDerivAt
    rw [h2]
    exact ((h1.mul hφ2).sub hφ1).congr_deriv (by ring)
  have hschwartz : (fun x : ℝ => (x : ℂ) * iteratedDeriv 2 φ x) =
      coordMulSchwartz (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ φ)) := by
    funext x
    rw [coordMulSchwartz_apply, coe_derivCLM, coe_derivCLM, h2]
  have hschwartz' : (fun x : ℝ => (x : ℂ) * deriv φ x) =
      coordMulSchwartz (SchwartzMap.derivCLM ℂ ℂ φ) := by
    funext x
    rw [coordMulSchwartz_apply, coe_derivCLM]
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) * iteratedDeriv 2 φ x) (Set.Ioi 0) := by
    rw [hschwartz]
    exact (coordMulSchwartz _).integrable.integrableOn
  have htend : Tendsto (fun x : ℝ => (x : ℂ) * deriv φ x - φ x) atTop (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => (x : ℂ) * deriv φ x) atTop (𝓝 0) := by
      rw [hschwartz']
      exact (coordMulSchwartz _).tendsto_cocompact.mono_left atTop_le_cocompact
    have hb : Tendsto (⇑φ) atTop (𝓝 0) := φ.tendsto_cocompact.mono_left atTop_le_cocompact
    simpa using ha.sub hb
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint htend]
  simp

/-! ### The Fourier transform of ReLU away from the origin -/

/-- **Corollary `cor:relu-admissible`(ii)**: `⟨ReLU^, φ⟩ = ∫ (-ω^{-2}) φ(ω) dω` for Schwartz `φ`
supported away from the origin. -/
theorem angularFourierDistribution_reluDistribution_apply (φ : SchwartzMap ℝ ℂ)
    (hφ : (0 : ℝ) ∉ tsupport φ) :
    angularFourierDistribution reluDistribution φ = ∫ ω : ℝ, -((ω : ℂ) ^ 2)⁻¹ * φ ω := by
  obtain ⟨ψ, hψ⟩ := SchwartzMap.exists_eq_inv_sq_mul φ hφ
  have hφψ : ∀ ω : ℝ, φ ω = (ω : ℂ) ^ 2 * ψ ω := by
    intro ω
    rw [hψ ω]
    by_cases hω : ω = 0
    · subst hω
      simp [image_eq_zero_of_notMem_tsupport hφ]
    · have : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
      field_simp
  have hF := angularFourierSchwartz_eq_neg_iteratedDeriv_two hφψ
  rw [angularFourierDistribution_apply]
  unfold reluDistribution
  rw [reluTemperedDistribution_apply]
  calc ∫ x : ℝ, angularFourierSchwartz φ x * (relu x : ℂ)
      = ∫ x in Set.Ioi (0 : ℝ), -((x : ℂ) * iteratedDeriv 2 (angularFourierSchwartz ψ) x) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
        · apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          dsimp only
          rw [hF, relu, max_eq_left (le_of_lt hx)]
          ring
        · intro x hx
          rw [Set.mem_Ioi, not_lt] at hx
          rw [relu, max_eq_right hx]
          simp
    _ = -angularFourierSchwartz ψ 0 := by
        rw [integral_neg, integral_Ioi_coord_mul_iteratedDeriv_two]
    _ = ∫ ω : ℝ, -((ω : ℂ) ^ 2)⁻¹ * φ ω := by
        rw [angularFourierSchwartz_apply, ← integral_neg]
        congr 1
        funext ω
        rw [hψ ω]
        simp

/-! ### The ReLU admissibility constant -/

/-- **Corollary `cor:relu-admissible`(iii)**: for even real band-pass `ρ̂`,
`C^{(α)}_{ReLU,ρ} = -(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω`. -/
theorem temperedAdmissibilityConst_reluDistribution {α : ℝ} (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω) :
    temperedAdmissibilityConst α reluDistribution ρ = (reluAdmissibilityScale α ρ : ℂ) := by
  unfold temperedAdmissibilityConst reluAdmissibilityScale
  rw [angularFourierDistribution_reluDistribution_apply _
    (hρ.zero_notMem_tsupport_temperedTestFilter α)]
  have hint : ∀ ω : ℝ, -((ω : ℂ) ^ 2)⁻¹ * temperedTestFilter α ρ ω =
      ((-((filterFourier ρ ω).re * |ω| ^ (-α - 2)) : ℝ) : ℂ) := by
    intro ω
    rw [hρ.temperedTestFilter_apply, hρ_even]
    have hre : filterFourier ρ ω = ((filterFourier ρ ω).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hρ_real ω]
    by_cases hω : ω = 0
    · subst hω
      simp [Real.zero_rpow (show -α - 2 ≠ 0 by linarith)]
    · have habs : 0 < |ω| := abs_pos.mpr hω
      have hsq : |ω| ^ (-α - 2) = |ω| ^ (-α) * (ω ^ 2)⁻¹ := by
        rw [Real.rpow_sub habs, Real.rpow_two, sq_abs, div_eq_mul_inv]
      rw [hsq]
      push_cast
      rw [hre]
      simp only [Complex.ofReal_re]
      ring
  simp only [hint]
  rw [integral_complex_ofReal, integral_neg]
  push_cast
  ring

/-- The integrand `ω ↦ ρ̂(ω).re |ω|^s` of the ReLU admissibility constant is continuous for
band-pass `ρ` (it vanishes near the origin). -/
theorem continuous_filterFourier_re_mul_abs_rpow {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (s : ℝ) : Continuous fun ω : ℝ => (filterFourier ρ ω).re * |ω| ^ s := by
  have hcont : Continuous fun ω : ℝ => (filterFourier ρ ω).re :=
    Complex.continuous_re.comp (continuous_filterFourier ρ)
  have hev : filterFourier ρ =ᶠ[𝓝 0] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hρ.zero_notMem_tsupport
  rw [continuous_iff_continuousAt]
  intro ω
  by_cases hω : ω = 0
  · subst hω
    have : (fun ω : ℝ => (filterFourier ρ ω).re * |ω| ^ s) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with ω hω
      simp [hω]
    exact this.continuousAt
  · exact hcont.continuousAt.mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.mpr hω))).comp
        continuous_abs.continuousAt)

/-- The integrand of the ReLU admissibility constant has compact support. -/
theorem hasCompactSupport_filterFourier_re_mul_abs_rpow {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) (s : ℝ) :
    HasCompactSupport fun ω : ℝ => (filterFourier ρ ω).re * |ω| ^ s :=
  (hρ.hasCompactSupport.comp_left (g := Complex.re) Complex.zero_re).mul_right

/-- **Corollary `cor:relu-admissible`(iv)**: for nonzero even nonpositive band-pass `ρ̂`, the
constant `-(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω` is positive. -/
theorem reluAdmissibilityScale_pos (α : ℝ) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) :
    0 < reluAdmissibilityScale α ρ := by
  unfold reluAdmissibilityScale
  rw [neg_pos]
  apply mul_neg_of_pos_of_neg (by positivity)
  rw [← neg_pos, ← integral_neg]
  set G : ℝ → ℝ := fun ω => -((filterFourier ρ ω).re * |ω| ^ (-α - 2)) with hG
  have hG_nonneg : 0 ≤ G := fun ω => by
    simp only [hG, Pi.zero_apply, neg_nonneg]
    exact mul_nonpos_of_nonpos_of_nonneg (hρ_nonpos ω) (Real.rpow_nonneg (abs_nonneg ω) _)
  have hG_cont : Continuous G := (continuous_filterFourier_re_mul_abs_rpow hρ (-α - 2)).neg
  have hG_supp : HasCompactSupport G :=
    (hasCompactSupport_filterFourier_re_mul_abs_rpow hρ (-α - 2)).neg
  rw [integral_pos_iff_support_of_nonneg hG_nonneg
    (hG_cont.integrable_of_hasCompactSupport hG_supp)]
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : ℝ, filterFourier ρ ω₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact filterFourier_ne_zero hρ.ne_zero (funext h)
  have hω₀0 : ω₀ ≠ 0 := by
    rintro rfl
    exact hω₀ (image_eq_zero_of_notMem_tsupport hρ.zero_notMem_tsupport)
  have hre : (filterFourier ρ ω₀).re < 0 := by
    refine lt_of_le_of_ne (hρ_nonpos ω₀) fun h => hω₀ ?_
    apply Complex.ext
    · simpa using h
    · simpa using hρ_real ω₀
  have hGpos : 0 < G ω₀ := by
    simp only [hG, neg_pos]
    exact mul_neg_of_neg_of_pos hre (Real.rpow_pos_of_pos (abs_pos.mpr hω₀0) _)
  exact hG_cont.isOpen_support.measure_pos volume ⟨ω₀, hGpos.ne'⟩

/-- The constant `-(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω` is homogeneous in the filter. -/
theorem reluAdmissibilityScale_smul (α c : ℝ) (ρ : SchwartzMap ℝ ℝ) :
    reluAdmissibilityScale α (c • ρ) = c * reluAdmissibilityScale α ρ := by
  unfold reluAdmissibilityScale
  simp only [filterFourier_smul', Complex.re_ofReal_mul, mul_assoc]
  rw [integral_const_mul]
  ring

/-- **Corollary `cor:relu-admissible`(v)**: the rescaled filter is band-pass with
`C^{(α)}_{ReLU,ρ} = 1`. -/
theorem reluNormalizedFilter_spec {α : ℝ} (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) :
    IsBandPass (reluNormalizedFilter α ρ) ∧
      temperedAdmissibilityConst α reluDistribution (reluNormalizedFilter α ρ) = 1 := by
  have hpos := reluAdmissibilityScale_pos α hρ hρ_real hρ_nonpos
  refine ⟨hρ.smul (inv_ne_zero hpos.ne'), ?_⟩
  unfold reluNormalizedFilter
  rw [hρ.temperedAdmissibilityConst_smul,
    temperedAdmissibilityConst_reluDistribution hα hρ hρ_real hρ_even, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]

/-! ### The band-pass filter `ρ_bp` -/

section BandPass

open OperatorRidgelet.Filters

/-- `ρ̂_bp` is nonpositive. -/
theorem bandPassHat_nonpos (ω : ℝ) : bandPassHat ω ≤ 0 := by
  unfold bandPassHat bump
  split_ifs
  · exact neg_nonpos.mpr (Real.exp_pos _).le
  · simp

/-- `ρ_bp` is band-pass. -/
theorem isBandPass_bandPass : IsBandPass bandPass := by
  have hF : filterFourier bandPass = fun ω => (bandPassHat ω : ℂ) := funext filterFourier_bandPass
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := filterFourier_bandPass (3 / 2)
    rw [h, FunLike.coe_zero, filterFourier_zero] at h1
    norm_num [bandPassHat, bump] at h1
  · rw [hF]
    exact Complex.ofRealCLM.contDiff.comp contDiff_bandPassHat
  · rw [hF]
    exact hasCompactSupport_bandPassHat.comp_left Complex.ofReal_zero
  · rw [hF, notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with ω hω
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hω
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero, bandPassHat, bump]
    rw [if_neg]
    · simp
    · rw [abs_lt]
      push Not
      intro h
      linarith

theorem filterFourier_bandPass_im (ω : ℝ) : (filterFourier bandPass ω).im = 0 := by
  rw [filterFourier_bandPass, Complex.ofReal_im]

theorem filterFourier_bandPass_neg (ω : ℝ) :
    filterFourier bandPass (-ω) = filterFourier bandPass ω := by
  rw [filterFourier_bandPass, filterFourier_bandPass, bandPassHat_neg]

theorem filterFourier_bandPass_re_nonpos (ω : ℝ) : (filterFourier bandPass ω).re ≤ 0 := by
  rw [filterFourier_bandPass, Complex.ofReal_re]
  exact bandPassHat_nonpos ω

/-- The rescaled band-pass filter `ρ_bp` has `C^{(α)}_{ReLU,ρ} = 1`, hence `≠ 0`. -/
theorem exists_isBandPass_temperedAdmissibilityConst_reluDistribution_ne_zero {α : ℝ}
    (hα : 0 < α) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α reluDistribution ρ ≠ 0 := by
  have h := reluNormalizedFilter_spec hα isBandPass_bandPass filterFourier_bandPass_im
    filterFourier_bandPass_neg filterFourier_bandPass_re_nonpos
  exact ⟨_, h.1, by rw [h.2]; exact one_ne_zero⟩

end BandPass

end OperatorRidgelet
