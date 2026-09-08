import OperatorRidgelet.Tempered.Basic
import OperatorRidgelet.Tempered.Fourier
import OperatorRidgelet.ToMathlib.TemperedDistributionPointSupport
import LeanRidgelet.ToMathlib.Lizorkin
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.Algebra.Polynomial

/-!
# Non-polynomial activations pair nontrivially with some band-pass filter

The last statement of Theorem `thm:tempered-reconstruction` and of Lemma
`lem:standard-activation-class`: if `β ∈ 𝒮'(ℝ)` is not a polynomial, then there is a band-pass
`ρ` with `C^{(α)}_{β,ρ} ≠ 0`, and (for real `β`) one with `C^{(α)}_{β,ρ} = 1`.

Every Hermitian symmetric `ψ ∈ C_c^∞(ℝ ∖ {0})` is the test filter `ρ̂(-·)|·|^{-α}` of the real
band-pass filter `ρ` with `ρ̂(ω) = ψ(-ω)|ω|^α` (`exists_isBandPass_temperedTestFilter_eq`), and
every `φ ∈ C_c^∞(ℝ ∖ {0})` is a combination `ψ₁ + i ψ₂` of two Hermitian symmetric ones.  So if
all the constants vanish, `β̂` vanishes on `C_c^∞(ℝ ∖ {0})`, hence is a combination of
derivatives of `δ₀`
(`TemperedDistribution.exists_sum_iteratedDeriv_zero_of_forall_hasCompactSupport`), and
`β = F⁻¹ β̂` acts by integration against a polynomial
(`isPolynomialDistribution_of_forall_angularFourierDistribution_eq_zero`).  For real `β` the
constant is real (`IsRealDistribution.temperedAdmissibilityConst_eq_re`), so a real rescaling of
`ρ` normalizes it to one.  Finally, a bounded continuous nonconstant function is not a
polynomial distribution (`not_isPolynomialDistribution_of_bounded`), which covers `tanh`, `Φ`,
and the Gaussian.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier FourierTransform
open scoped FourierTransform ComplexConjugate

/-! ### The inverse angular Fourier transform on Schwartz functions -/

/-- The inverse angular Fourier transform `(2π)⁻¹ ∫ g(ω) e^{itω} dω` of a Schwartz function. -/
def angularFourierInvSchwartz (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) (𝓕⁻ g)

theorem angularFourierInvSchwartz_apply (g : SchwartzMap ℝ ℂ) (t : ℝ) :
    angularFourierInvSchwartz g t =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ ω : ℝ, g ω * Complex.exp (Complex.I * (ω * t)) := by
  rw [angularFourierInvSchwartz, smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, realDilationCLE_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, Real.fourierChar_apply, mul_comm (g v)]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  field_simp

/-- The inverse angular transform of a Hermitian symmetric function is real. -/
theorem conj_angularFourierInvSchwartz (g : SchwartzMap ℝ ℂ) (hg : ∀ ω : ℝ, conj (g (-ω)) = g ω)
    (t : ℝ) : conj (angularFourierInvSchwartz g t) = angularFourierInvSchwartz g t := by
  rw [angularFourierInvSchwartz_apply, map_mul, ← integral_conj]
  have hc : (2 * (Real.pi : ℂ))⁻¹ = conj (2 * (Real.pi : ℂ))⁻¹ := by
    rw [map_inv₀, map_mul, Complex.conj_ofReal, map_ofNat]
  rw [← hc]
  congr 1
  have h := Measure.integral_comp_mul_left (fun ω : ℝ => g ω * Complex.exp (Complex.I * (ω * t)))
    (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with ω
  rw [map_mul, ← Complex.exp_conj, ← hg ω]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, conj_conj]
  push_cast
  ring_nf

/-- The real Schwartz function whose Fourier transform is the Hermitian symmetric `g`. -/
def realFilterOfHermitian (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM (angularFourierInvSchwartz g)

theorem coe_realFilterOfHermitian (g : SchwartzMap ℝ ℂ) (hg : ∀ ω : ℝ, conj (g (-ω)) = g ω)
    (t : ℝ) : ((realFilterOfHermitian g t : ℝ) : ℂ) = angularFourierInvSchwartz g t := by
  rw [realFilterOfHermitian, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply]
  exact Complex.conj_eq_iff_re.mp (conj_angularFourierInvSchwartz g hg t)

/-- The Fourier transform of `realFilterOfHermitian g` is `g`. -/
theorem filterFourier_realFilterOfHermitian (g : SchwartzMap ℝ ℂ)
    (hg : ∀ ω : ℝ, conj (g (-ω)) = g ω) (ω : ℝ) :
    filterFourier (realFilterOfHermitian g) ω = g ω := by
  have hinv := angularFourier_inversion_of_integrable (f := ⇑g)
    (g := ⇑(angularFourierInvSchwartz g)) g.continuous g.integrable
    (angularFourierInvSchwartz g).integrable
    (fun ω => by rw [angularFourierInvSchwartz_apply]) ω
  rw [hinv]
  unfold filterFourier lineFourier angularFourierIntegralInner
  apply integral_congr_ae
  filter_upwards with z
  rw [coe_realFilterOfHermitian g hg, mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-! ### Real band-pass filters from Hermitian symmetric test functions -/

/-- The Schwartz function `ω ↦ |ω|^α ψ(-ω)` for `ψ` supported away from the origin. -/
theorem exists_schwartz_abs_rpow_mul_neg (ψ : SchwartzMap ℝ ℂ) (hψ : (0 : ℝ) ∉ tsupport ψ)
    (α : ℝ) : ∃ g : SchwartzMap ℝ ℂ, ∀ ω : ℝ, g ω = ((|ω| ^ α : ℝ) : ℂ) * ψ (-ω) := by
  obtain ⟨g, hg⟩ := SchwartzMap.exists_eq_abs_rpow_mul (reflectSchwartz ψ)
    (zero_notMem_tsupport_reflectSchwartz hψ) α
  exact ⟨g, fun ω => by rw [hg ω, reflectSchwartz_apply]⟩

/-- For a nonzero Hermitian symmetric `ψ ∈ C_c^∞(ℝ ∖ {0})` and `α > 0` there is a real band-pass
filter whose test filter `ρ̂(-·)|·|^{-α}` is `ψ`. -/
theorem exists_isBandPass_temperedTestFilter_eq {α : ℝ} (hα : 0 < α) (ψ : SchwartzMap ℝ ℂ)
    (hψc : HasCompactSupport ψ) (hψ0 : (0 : ℝ) ∉ tsupport ψ)
    (hψh : ∀ ω : ℝ, conj (ψ (-ω)) = ψ ω) (hne : ψ ≠ 0) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedTestFilter α ρ = ψ := by
  obtain ⟨g, hg⟩ := exists_schwartz_abs_rpow_mul_neg ψ hψ0 α
  have hgh : ∀ ω : ℝ, conj (g (-ω)) = g ω := by
    intro ω
    have h := hψh (-ω)
    rw [neg_neg] at h
    rw [hg, hg, neg_neg, map_mul, Complex.conj_ofReal, abs_neg, h]
  have hρF : ∀ ω, filterFourier (realFilterOfHermitian g) ω = g ω :=
    filterFourier_realFilterOfHermitian g hgh
  have hρF' : filterFourier (realFilterOfHermitian g) = ⇑g := funext hρF
  have hg0 : (0 : ℝ) ∉ tsupport g := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have h := zero_notMem_tsupport_reflectSchwartz hψ0
    rw [notMem_tsupport_iff_eventuallyEq] at h
    filter_upwards [h] with ω hω
    rw [hg, ← reflectSchwartz_apply, hω]
    simp
  have hgc : HasCompactSupport g := by
    have h2 : (⇑g) = fun ω => ((|ω| ^ α : ℝ) : ℂ) * reflectSchwartz ψ ω :=
      funext fun ω => by rw [hg, reflectSchwartz_apply]
    rw [h2]
    exact (hasCompactSupport_reflectSchwartz hψc).mul_left
  have hψspec : ∀ ω : ℝ, ψ ω =
      filterFourier (realFilterOfHermitian g) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
    intro ω
    rw [hρF, hg, neg_neg, abs_neg]
    by_cases hω : ω = 0
    · subst hω
      simp [Real.zero_rpow hα.ne', image_eq_zero_of_notMem_tsupport hψ0]
    · have habs : 0 < |ω| := abs_pos.mpr hω
      rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, Real.rpow_neg habs.le,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos habs α).ne', Complex.ofReal_one, one_mul]
  refine ⟨realFilterOfHermitian g, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h
    apply hne
    have hzero : ⇑g = 0 := by
      rw [← hρF', h]
      funext ω
      simp only [Pi.zero_apply]
      rw [← filterFourier_zero ω]
      rfl
    ext ω
    have hω := congrFun hzero (-ω)
    rw [hg, neg_neg, Pi.zero_apply, abs_neg] at hω
    by_cases hω0 : ω = 0
    · subst hω0
      rw [image_eq_zero_of_notMem_tsupport hψ0]
      rfl
    · have habs : 0 < |ω| := abs_pos.mpr hω0
      rw [zero_apply]
      exact (mul_eq_zero.mp hω).resolve_left
        (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos habs α).ne')
  · rw [hρF']
    exact g.smooth ⊤
  · rw [hρF']
    exact hgc
  · rw [hρF']
    exact hg0
  · have hex : ∃ φ : SchwartzMap ℝ ℂ, ∀ ω : ℝ,
        φ ω = filterFourier (realFilterOfHermitian g) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) :=
      ⟨ψ, hψspec⟩
    ext ω
    rw [OperatorRidgelet.temperedTestFilter_apply hex ω, hψspec ω]

/-! ### The Hermitian decomposition -/

/-- If `β̂` vanishes on the Hermitian symmetric functions of `C_c^∞(ℝ ∖ {0})`, it vanishes on
`C_c^∞(ℝ ∖ {0})`. -/
theorem angularFourierDistribution_eq_zero_of_hermitian (β : TemperedDistribution ℝ ℂ)
    (h : ∀ ψ : SchwartzMap ℝ ℂ, HasCompactSupport ψ → (0 : ℝ) ∉ tsupport ψ →
      (∀ ω : ℝ, conj (ψ (-ω)) = ψ ω) → angularFourierDistribution β ψ = 0)
    (φ : SchwartzMap ℝ ℂ) (hφc : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ) :
    angularFourierDistribution β φ = 0 := by
  set φ' := reflectSchwartz (schwartzConjugation φ) with hφ'
  have hφ'apply : ∀ ω, φ' ω = conj (φ (-ω)) := fun ω => by
    rw [hφ', reflectSchwartz_apply, schwartzConjugation_apply]
  have hφ'c : HasCompactSupport φ' := by
    apply hasCompactSupport_reflectSchwartz
    have : ⇑(schwartzConjugation φ) = conj ∘ ⇑φ := funext fun x => by
      rw [schwartzConjugation_apply, Function.comp_apply]
    rw [this]
    exact hφc.comp_left (map_zero _)
  have hφ'0 : (0 : ℝ) ∉ tsupport φ' := by
    apply zero_notMem_tsupport_reflectSchwartz
    rw [notMem_tsupport_iff_eventuallyEq] at hφ0 ⊢
    filter_upwards [hφ0] with ω hω
    rw [schwartzConjugation_apply, hω]
    simp
  obtain ⟨ψ₁, hψ₁apply⟩ : ∃ ψ₁ : SchwartzMap ℝ ℂ, ∀ ω, ψ₁ ω = 2⁻¹ * (φ ω + φ' ω) :=
    ⟨(2⁻¹ : ℂ) • (φ + φ'), fun ω => by rw [smul_apply, add_apply, smul_eq_mul]⟩
  obtain ⟨ψ₂, hψ₂apply⟩ : ∃ ψ₂ : SchwartzMap ℝ ℂ,
      ∀ ω, ψ₂ ω = -(2⁻¹ * Complex.I) * (φ ω - φ' ω) :=
    ⟨(-(2⁻¹ * Complex.I)) • (φ - φ'), fun ω => by rw [smul_apply, sub_apply, smul_eq_mul]⟩
  have hφeq : φ = ψ₁ + Complex.I • ψ₂ := by
    ext ω
    rw [add_apply, smul_apply, hψ₁apply, hψ₂apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hc₁ : HasCompactSupport ψ₁ := by
    have : ⇑ψ₁ = (fun _ : ℝ => (2⁻¹ : ℂ)) • (⇑φ + ⇑φ') := funext fun ω => by
      rw [hψ₁apply]
      rfl
    rw [this]
    exact (hφc.add hφ'c).smul_left
  have hc₂ : HasCompactSupport ψ₂ := by
    have : ⇑ψ₂ = (fun _ : ℝ => -(2⁻¹ * Complex.I)) • (⇑φ - ⇑φ') := funext fun ω => by
      rw [hψ₂apply]
      rfl
    rw [this]
    exact (hφc.sub hφ'c).smul_left
  have h0₁ : (0 : ℝ) ∉ tsupport ψ₁ := by
    rw [notMem_tsupport_iff_eventuallyEq] at hφ0 hφ'0 ⊢
    filter_upwards [hφ0, hφ'0] with ω h1 h2
    rw [hψ₁apply, h1, h2]
    simp
  have h0₂ : (0 : ℝ) ∉ tsupport ψ₂ := by
    rw [notMem_tsupport_iff_eventuallyEq] at hφ0 hφ'0 ⊢
    filter_upwards [hφ0, hφ'0] with ω h1 h2
    rw [hψ₂apply, h1, h2]
    simp
  have hh₁ : ∀ ω : ℝ, conj (ψ₁ (-ω)) = ψ₁ ω := by
    intro ω
    rw [hψ₁apply, hψ₁apply, hφ'apply, hφ'apply, neg_neg]
    simp only [map_mul, map_add, map_inv₀, map_ofNat, conj_conj]
    ring
  have hh₂ : ∀ ω : ℝ, conj (ψ₂ (-ω)) = ψ₂ ω := by
    intro ω
    rw [hψ₂apply, hψ₂apply, hφ'apply, hφ'apply, neg_neg]
    simp only [map_mul, map_sub, map_neg, map_inv₀, map_ofNat, conj_conj, Complex.conj_I]
    ring
  rw [hφeq, map_add, map_smul, h ψ₁ hc₁ h0₁ hh₁, h ψ₂ hc₂ h0₂ hh₂, smul_zero, add_zero]

/-! ### The polynomial conclusion -/

/-- The action of the inverse angular Fourier transform on a test function. -/
theorem angularFourierInvDistribution_apply (u : TemperedDistribution ℝ ℂ)
    (φ : SchwartzMap ℝ ℂ) :
    angularFourierInvDistribution u φ = (2 * (Real.pi : ℂ))⁻¹ *
      u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE (2 * Real.pi) two_mul_pi_ne_zero).symm (𝓕⁻ φ)) := by
  unfold angularFourierInvDistribution
  rw [ContinuousLinearMap.comp_apply, fourierInvCLM_apply, TemperedDistribution.fourierInv_apply,
    temperedDistributionDilation_apply, abs_of_pos (by positivity)]
  push_cast
  rfl

/-- If `β̂` vanishes on `C_c^∞(ℝ ∖ {0})`, then `β` acts by integration against a polynomial. -/
theorem isPolynomialDistribution_of_forall_angularFourierDistribution_eq_zero
    (β : TemperedDistribution ℝ ℂ)
    (h : ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ → (0 : ℝ) ∉ tsupport φ →
      angularFourierDistribution β φ = 0) :
    IsPolynomialDistribution β := by
  obtain ⟨N, c, hc⟩ :=
    TemperedDistribution.exists_sum_iteratedDeriv_zero_of_forall_hasCompactSupport _ h
  refine ⟨∑ k ∈ Finset.range (N + 1),
    Polynomial.C ((2 * (Real.pi : ℂ))⁻¹ * (c k * Complex.I ^ k)) * Polynomial.X ^ k,
    fun φ => ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  conv_lhs => rw [← angularFourierInvDistribution_angularFourierDistribution β]
  rw [angularFourierInvDistribution_apply, hc]
  set χ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realDilationCLE (2 * Real.pi) two_mul_pi_ne_zero).symm (𝓕⁻ φ) with hχdef
  have hχ : ∀ k : ℕ, iteratedDeriv k χ 0 = Complex.I ^ k * ∫ z : ℝ, (z : ℂ) ^ k * φ z := by
    intro k
    have hcoe : ⇑χ = fun x => (𝓕⁻ φ : SchwartzMap ℝ ℂ) ((2 * Real.pi)⁻¹ * x) := by
      funext x
      rw [hχdef, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        realDilationCLE_symm_apply]
    have hsm : ContDiff ℝ k (⇑(𝓕⁻ φ : SchwartzMap ℝ ℂ)) := (𝓕⁻ φ).smooth k
    rw [hcoe]
    simp only [iteratedDeriv_comp_const_smul hsm (2 * Real.pi)⁻¹, mul_zero]
    have h2 : ⇑(𝓕⁻ φ : SchwartzMap ℝ ℂ) = fun x => 𝓕 (⇑φ) (-x) := by
      rw [SchwartzMap.fourierInv_coe]
      exact funext (Real.fourierInv_eq_fourier_neg _)
    rw [h2, iteratedDeriv_comp_neg, neg_zero, Real.iteratedDeriv_fourier_zero]
    simp only [Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
    congr 2
    field_simp
  simp only [hχ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hfun : (fun z : ℝ => φ z * ∑ k ∈ Finset.range (N + 1),
      (2 * (Real.pi : ℂ))⁻¹ * (c k * Complex.I ^ k) * (z : ℂ) ^ k) =
      fun z : ℝ => ∑ k ∈ Finset.range (N + 1),
        ((2 * (Real.pi : ℂ))⁻¹ * (c k * Complex.I ^ k)) * ((z : ℂ) ^ k * φ z) := by
    funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, integral_finsetSum _ fun k _ => (integrable_pow_smul_schwartz φ k).const_mul _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

/-! ### The existence of a band-pass filter with nonzero constant -/

/-- If `β` is not a polynomial, some band-pass `ρ` has `C^{(α)}_{β,ρ} ≠ 0`. -/
theorem exists_isBandPass_temperedAdmissibilityConst_ne_zero {α : ℝ} (hα : 0 < α)
    (β : TemperedDistribution ℝ ℂ) (hpoly : ¬ IsPolynomialDistribution β) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α β ρ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hpoly
  apply isPolynomialDistribution_of_forall_angularFourierDistribution_eq_zero
  intro φ hφc hφ0
  apply angularFourierDistribution_eq_zero_of_hermitian β _ φ hφc hφ0
  intro ψ hψc hψ0 hψh
  by_cases hne : ψ = 0
  · rw [hne, map_zero]
  obtain ⟨ρ, hρ, hT⟩ := exists_isBandPass_temperedTestFilter_eq hα ψ hψc hψ0 hψh hne
  have h := hcon ρ hρ
  unfold temperedAdmissibilityConst at h
  rw [hT] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exfalso
    have : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
    exact this (Complex.ofReal_eq_zero.mp h')
  · exact h'

/-! ### Reality of the constant and normalization -/

/-- `conj ρ̂(ω) = ρ̂(-ω)` for a real filter. -/
theorem conj_filterFourier (ρ : SchwartzMap ℝ ℝ) (ω : ℝ) :
    conj (filterFourier ρ ω) = filterFourier ρ (-ω) := by
  unfold filterFourier lineFourier angularFourierIntegralInner
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, RCLike.inner_apply,
    conj_trivial]
  push_cast
  ring

/-- For real `β`, `conj ⟨β̂, φ⟩ = ⟨β̂, conj φ(-·)⟩`. -/
theorem IsRealDistribution.conj_angularFourierDistribution_apply {β : TemperedDistribution ℝ ℂ}
    (hβ : IsRealDistribution β) (φ : SchwartzMap ℝ ℂ) :
    conj (angularFourierDistribution β φ) =
      angularFourierDistribution β (reflectSchwartz (schwartzConjugation φ)) := by
  rw [angularFourierDistribution_apply, angularFourierDistribution_apply]
  have h := congrArg (fun u : TemperedDistribution ℝ ℂ =>
    u (schwartzConjugation (angularFourierSchwartz φ))) hβ
  simp only [temperedDistributionConjugation_apply, schwartzConjugation_involutive] at h
  rw [h]
  congr 1
  ext ω
  rw [schwartzConjugation_apply, angularFourierSchwartz_apply, angularFourierSchwartz_apply,
    ← integral_conj]
  have hsub := Measure.integral_comp_mul_left (fun b : ℝ =>
    Complex.exp (-Complex.I * (b * ω)) * reflectSchwartz (schwartzConjugation φ) b) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at hsub
  rw [← hsub]
  apply integral_congr_ae
  filter_upwards with b
  rw [map_mul, ← Complex.exp_conj, reflectSchwartz_apply, schwartzConjugation_apply, neg_neg]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- For real `β` and band-pass `ρ`, the constant `C^{(α)}_{β,ρ}` is real. -/
theorem IsRealDistribution.temperedAdmissibilityConst_eq_re {α : ℝ}
    {β : TemperedDistribution ℝ ℂ} (hβ : IsRealDistribution β) {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) :
    temperedAdmissibilityConst α β ρ = ((temperedAdmissibilityConst α β ρ).re : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  unfold temperedAdmissibilityConst
  rw [map_mul, Complex.conj_ofReal, hβ.conj_angularFourierDistribution_apply]
  congr 2
  ext ω
  rw [reflectSchwartz_apply, schwartzConjugation_apply, hρ.temperedTestFilter_apply,
    hρ.temperedTestFilter_apply, map_mul, Complex.conj_ofReal, neg_neg, conj_filterFourier,
    abs_neg]

/-- For real non-polynomial `β`, some band-pass `ρ` has `C^{(α)}_{β,ρ} = 1`. -/
theorem exists_isBandPass_temperedAdmissibilityConst_eq_one {α : ℝ} (hα : 0 < α)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β)
    (hpoly : ¬ IsPolynomialDistribution β) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α β ρ = 1 := by
  obtain ⟨ρ, hρ, hC⟩ := exists_isBandPass_temperedAdmissibilityConst_ne_zero hα β hpoly
  have hre := hβ.temperedAdmissibilityConst_eq_re (α := α) hρ
  set c := (temperedAdmissibilityConst α β ρ).re with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hC
    rw [hre, h, Complex.ofReal_zero]
  refine ⟨c⁻¹ • ρ, hρ.smul (inv_ne_zero hc0), ?_⟩
  rw [hρ.temperedAdmissibilityConst_smul, hre, ← Complex.ofReal_mul, inv_mul_cancel₀ hc0,
    Complex.ofReal_one]

/-! ### Bounded nonconstant functions are not polynomials -/

/-- A tempered distribution acting by integration against a bounded continuous function taking
two different values is not a polynomial distribution. -/
theorem not_isPolynomialDistribution_of_bounded {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ}
    (hβ : ∀ φ : SchwartzMap ℝ ℂ, β φ = ∫ x : ℝ, φ x * (b x : ℂ)) (hb : Continuous b) {M : ℝ}
    (hM : ∀ x, |b x| ≤ M) {x₀ x₁ : ℝ} (hne : b x₀ ≠ b x₁) : ¬ IsPolynomialDistribution β := by
  rintro ⟨p, hp⟩
  have hcont : Continuous fun x : ℝ => (b x : ℂ) - p.eval (x : ℂ) :=
    (Complex.continuous_ofReal.comp hb).sub (p.continuous.comp Complex.continuous_ofReal)
  have hae : ∀ᵐ x : ℝ ∂volume, (b x : ℂ) - p.eval (x : ℂ) = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
    intro g hg_smooth hg_supp
    let ψ : SchwartzMap ℝ ℂ := (hg_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg_smooth)
    have hψ : ∀ x, ψ x = (g x : ℂ) := fun x => rfl
    have h1 := hβ ψ
    rw [hp ψ] at h1
    have hint1 : Integrable fun x : ℝ => ψ x * (b x : ℂ) := by
      have hbC : Continuous fun x : ℝ => (b x : ℂ) := Complex.continuous_ofReal.comp hb
      exact (ψ.continuous.mul hbC).integrable_of_hasCompactSupport
        ((hg_supp.comp_left Complex.ofReal_zero).mul_right)
    have hint2 : Integrable fun x : ℝ => ψ x * p.eval (x : ℂ) :=
      (ψ.continuous.mul
        (p.continuous.comp Complex.continuous_ofReal)).integrable_of_hasCompactSupport
        ((hg_supp.comp_left Complex.ofReal_zero).mul_right)
    have : (∫ x : ℝ, g x • ((b x : ℂ) - p.eval (x : ℂ))) =
        (∫ x : ℝ, ψ x * (b x : ℂ)) - ∫ x : ℝ, ψ x * p.eval (x : ℂ) := by
      rw [← integral_sub hint1 hint2]
      congr 1
      funext x
      rw [hψ, Complex.real_smul]
      ring
    rw [this, h1, sub_self]
  have heq : ∀ x : ℝ, (b x : ℂ) = p.eval (x : ℂ) := by
    have h := (Continuous.ae_eq_iff_eq volume hcont continuous_zero).mp hae
    intro x
    have := congrFun h x
    simpa [sub_eq_zero] using this
  by_cases hdeg : 0 < p.degree
  · have hlead : (RingHom.id ℂ) p.leadingCoeff ≠ 0 := by
      simpa using Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_degree_gt hdeg)
    have hz : Tendsto ((fun z : ℂ => ‖z‖) ∘ fun x : ℝ => (x : ℂ)) atTop atTop := by
      have : ((fun z : ℂ => ‖z‖) ∘ fun x : ℝ => (x : ℂ)) = fun x : ℝ => |x| := by
        funext x
        simp
      rw [this]
      exact tendsto_abs_atTop_atTop
    have ht := Polynomial.tendsto_abv_eval₂_atTop (RingHom.id ℂ) (fun z : ℂ => ‖z‖) p hdeg
      hlead hz
    obtain ⟨x, hx⟩ := (ht.eventually (eventually_gt_atTop M)).exists
    rw [Polynomial.eval₂_id, ← heq, Complex.norm_real, Real.norm_eq_abs] at hx
    exact absurd (hM x) (not_le.mpr hx)
  · rw [not_lt] at hdeg
    have hC := Polynomial.eq_C_of_degree_le_zero hdeg
    apply hne
    apply Complex.ofReal_injective
    rw [heq, heq, hC, Polynomial.eval_C, Polynomial.eval_C]

/-- `tanh` is not a polynomial distribution. -/
theorem not_isPolynomialDistribution_tanhDistribution :
    ¬ IsPolynomialDistribution tanhDistribution :=
  not_isPolynomialDistribution_of_bounded (tanhTemperedDistribution_apply 2 (by norm_num))
    lipschitzWith_tanh.continuous abs_tanh_le_one tanh_zero_ne_tanh_one

/-- The Gaussian distribution function `Φ` is not a polynomial distribution. -/
theorem not_isPolynomialDistribution_gaussianCdfDistribution :
    ¬ IsPolynomialDistribution gaussianCdfDistribution :=
  not_isPolynomialDistribution_of_bounded
    (weightedDistribution_apply (memLp_japaneseBracketPow_mul_of_bounded measurable_gaussianCdf
      abs_gaussianCdf_le_one (by norm_num)))
    lipschitzWith_gaussianCdf.continuous abs_gaussianCdf_le_one
    gaussianCdf_zero_lt_gaussianCdf_one.ne

/-- The Gaussian `e^{-u²/2}` is not a polynomial distribution. -/
theorem not_isPolynomialDistribution_gaussianDistribution :
    ¬ IsPolynomialDistribution gaussianDistribution :=
  not_isPolynomialDistribution_of_bounded
    (weightedDistribution_apply (memLp_japaneseBracketPow_mul_of_bounded
      continuous_gaussianFun.measurable abs_gaussianFun_le_one (by norm_num)))
    continuous_gaussianFun abs_gaussianFun_le_one gaussianFun_zero_ne_gaussianFun_one

end OperatorRidgelet
