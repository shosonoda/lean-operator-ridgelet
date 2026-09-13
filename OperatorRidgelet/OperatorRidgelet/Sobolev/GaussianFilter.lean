import OperatorRidgelet.Sobolev.GaussianDefs
import OperatorRidgelet.Sobolev.Homogeneous
import OperatorRidgelet.Sobolev.Uniqueness
import OperatorRidgelet.Tempered.Fourier
import OperatorRidgelet.ToMathlib.PolynomialGaussianSchwartz
import OperatorRidgelet.ToMathlib.FourierEven
import OperatorRidgelet.ToMathlib.SchwartzFourier
import OperatorRidgelet.ToMathlib.AbsRpowGaussian

/-!
# The Gaussian-derivative filters of Appendix I

The non-band-pass filters of `prop:nonbandpass-sobolev` are the real Schwartz functions whose
Fourier transform is `ρ̂(ω) = ω^{2k} e^{-ω²}`.  This module builds the filter from the
polynomial-times-Gaussian Schwartz functions and the angular Fourier inversion, and records the
two elementary properties that separate it from the band-pass filters of Appendix I: its
transform vanishes only at the origin, so it is not band pass, while `|ρ̂|² |ω|^{-α}` is still
integrable for `α < 4k + 1`, so it is `α`-admissible.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex LeanRidgelet LeanRidgelet.Fourier
open scoped Polynomial FourierTransform

/-- The value `ρ̂_k(ω) = ω^{2k} e^{-ω²}` of the Gaussian-derivative symbol. -/
@[simp]
theorem gaussDerivHat_apply (k : ℕ) (ω : ℝ) :
    gaussDerivHat k ω = ω ^ (2 * k) * Real.exp (-ω ^ 2) := by
  rw [gaussDerivHat, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    realDilationCLE_apply, Real.polynomialGaussianSchwartz_apply]
  have hsq : (Real.sqrt 2 * ω) ^ 2 = 2 * ω ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hpow : (Real.sqrt 2 * ω) ^ (2 * k) = 2 ^ k * ω ^ (2 * k) := by
    rw [mul_pow, pow_mul, Real.sq_sqrt (by norm_num)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hpow, hsq]
  field_simp

/-- The value of the symbol in Mathlib's frequency variable. -/
@[simp]
theorem gaussDerivDilatedHat_apply (k : ℕ) (ξ : ℝ) :
    gaussDerivDilatedHat k ξ = gaussDerivHat k (2 * Real.pi * ξ) := by
  rw [gaussDerivDilatedHat, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    realDilationCLE_apply]

/-- The complex filter is invariant under conjugation: its frequency profile is real and
even. -/
theorem gaussDerivFilterC_conj (k : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (gaussDerivFilterC k t) = gaussDerivFilterC k t := by
  have heven : ∀ ξ : ℝ, gaussDerivDilatedHat k (-ξ) = gaussDerivDilatedHat k ξ := by
    intro ξ
    simp only [gaussDerivDilatedHat_apply, gaussDerivHat_apply]
    rw [show 2 * Real.pi * -ξ = -(2 * Real.pi * ξ) by ring]
    rw [neg_pow, neg_pow]
    simp [pow_mul]
  have hcoe : ⇑(gaussDerivFilterC k) = 𝓕⁻ fun ξ : ℝ => ((gaussDerivDilatedHat k ξ : ℝ) : ℂ) := by
    rw [gaussDerivFilterC, SchwartzMap.fourierInv_coe]
    rfl
  rw [hcoe]
  exact Real.conj_fourierInv_ofReal_of_even heven t

/-- The real filter is the complex one. -/
theorem gaussDerivFilter_ofReal (k : ℕ) (t : ℝ) :
    ((gaussDerivFilter k t : ℝ) : ℂ) = gaussDerivFilterC k t := by
  rw [gaussDerivFilter, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply]
  exact Complex.conj_eq_iff_re.mp (gaussDerivFilterC_conj k t)

/-- The Fourier transform of a real filter is the profile of its complexification. -/
theorem filterFourier_eq_rayProfile (ρ : ℝ → ℝ) (ω : ℝ) :
    filterFourier ρ ω = rayProfile (fun t => (ρ t : ℂ)) ω := by
  rw [filterFourier, lineFourier, angularFourierIntegralInner, rayProfile]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Complex.exp (-Complex.I * ((inner ℝ t ω : ℝ) : ℂ)) * (ρ t : ℂ)
      = Complex.exp (((-(ω * t) : ℝ) : ℂ) * Complex.I) • (ρ t : ℂ)
  rw [smul_eq_mul]
  congr 2
  rw [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The profile of the complex filter is the symbol `ρ̂_k`. -/
theorem rayProfile_gaussDerivFilterC (k : ℕ) (ω : ℝ) :
    rayProfile (gaussDerivFilterC k) ω = ((ω ^ (2 * k) * Real.exp (-ω ^ 2) : ℝ) : ℂ) := by
  have hprof : rayProfile (⇑(gaussDerivFilterC k)) ω
      = SchwartzMap.ofReal (gaussDerivDilatedHat k) (ω / (2 * Real.pi)) := by
    rw [rayProfile_eq_fourier, ← SchwartzMap.fourier_coe, gaussDerivFilterC,
      FourierTransform.fourier_fourierInv_eq]
  rw [hprof]
  simp only [SchwartzMap.ofReal_apply, gaussDerivDilatedHat_apply, gaussDerivHat_apply]
  rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)]

/-- **The defining property of the Gaussian-derivative filter**: `ρ̂_k(ω) = ω^{2k} e^{-ω²}`. -/
theorem filterFourier_gaussDerivFilter (k : ℕ) (ω : ℝ) :
    filterFourier (gaussDerivFilter k) ω = ((ω ^ (2 * k) * Real.exp (-ω ^ 2) : ℝ) : ℂ) := by
  have hfun : (fun t => ((gaussDerivFilter k t : ℝ) : ℂ)) = ⇑(gaussDerivFilterC k) :=
    funext (gaussDerivFilter_ofReal k)
  rw [filterFourier_eq_rayProfile, hfun, rayProfile_gaussDerivFilterC]

/-! ### The filter is not band pass, but is still admissible -/

/-- The transform `ρ̂_k` vanishes only at the origin. -/
theorem filterFourier_gaussDerivFilter_ne_zero {k : ℕ} {ω : ℝ} (hω : ω ≠ 0) :
    filterFourier (gaussDerivFilter k) ω ≠ 0 := by
  rw [filterFourier_gaussDerivFilter]
  simp only [ne_eq, Complex.ofReal_eq_zero, mul_eq_zero, pow_eq_zero_iff', not_or]
  exact ⟨fun h => hω h.1, (Real.exp_pos _).ne'⟩

/-- **The Gaussian-derivative filter is not band pass**: its transform is nonzero away from the
origin, so the origin lies in the closed support. -/
theorem not_isBandPass_gaussDerivFilter (k : ℕ) : ¬ IsBandPass (gaussDerivFilter k) := by
  intro h
  refine h.zero_notMem_tsupport ?_
  have hsub : ({(0 : ℝ)}ᶜ : Set ℝ) ⊆ Function.support (filterFourier (gaussDerivFilter k)) :=
    fun ω hω => filterFourier_gaussDerivFilter_ne_zero hω
  have : closure ({(0 : ℝ)}ᶜ : Set ℝ) ⊆ tsupport (filterFourier (gaussDerivFilter k)) :=
    closure_mono hsub
  exact this (by rw [(dense_compl_singleton (0 : ℝ)).closure_eq]; trivial)

/-- Away from the origin the admissibility integrand is the even Gaussian weight
`|ω|^{4k-α} e^{-2ω²}`. -/
theorem admissibility_integrand_gaussDerivFilter (k : ℕ) (α : ℝ) :
    (fun ω : ℝ => ‖filterFourier (gaussDerivFilter k) ω‖ ^ 2 * |ω| ^ (-α)) =ᵐ[volume]
      fun ω : ℝ => |ω| ^ ((4 * k : ℕ) - α) * Real.exp (-2 * ω ^ 2) := by
  have h0 : ∀ᵐ ω : ℝ, ω ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with ω hω
  have habs : (0 : ℝ) < |ω| := abs_pos.mpr hω
  rw [filterFourier_gaussDerivFilter, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.exp_pos _).le, mul_pow, ← abs_pow, ← pow_mul]
  rw [Real.rpow_sub habs, Real.rpow_natCast, abs_pow]
  have hexp : Real.exp (-ω ^ 2) ^ 2 = Real.exp (-2 * ω ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show 2 * k * 2 = 4 * k by ring, hexp]
  field_simp
  rw [← Real.rpow_add habs]
  simp

/-- **The Gaussian-derivative filter is `α`-admissible** for `α < 4k + 1`: the weight
`|ρ̂_k|² |ω|^{-α}` is integrable and its integral is positive. -/
theorem isAdmissible_gaussDerivFilter {k : ℕ} {α : ℝ} (hk : α < 4 * k + 1) :
    IsAdmissible α (gaussDerivFilter k) where
  integrable := by
    refine (Real.integrable_abs_rpow_mul_exp_neg_mul_sq (b := 2) (by norm_num) ?_).congr
      (admissibility_integrand_gaussDerivFilter k α).symm
    push_cast
    linarith
  pos := by
    rw [admissibilityConst]
    refine mul_pos (by positivity) ?_
    rw [integral_congr_ae (admissibility_integrand_gaussDerivFilter k α)]
    have hint := Real.integrable_abs_rpow_mul_exp_neg_mul_sq (b := 2) (c := (4 * k : ℕ) - α)
      (by norm_num) (by push_cast; linarith)
    rw [integral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le ?_ (measure_mono (fun ω (hω : ω ∈ Set.Ioi (1 : ℝ)) => ?_))
      · rw [Real.volume_Ioi]
        exact ENNReal.zero_lt_top
      · have h1 : (0 : ℝ) < |ω| := abs_pos.mpr (by linarith [Set.mem_Ioi.mp hω] : ω ≠ 0)
        exact mul_ne_zero (Real.rpow_pos_of_pos h1 _).ne' (Real.exp_pos _).ne'
    · filter_upwards with ω
      positivity
    · exact hint
