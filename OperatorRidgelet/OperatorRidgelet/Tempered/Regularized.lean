import OperatorRidgelet.Tempered.Polynomial
import OperatorRidgelet.ToMathlib.TemperedDistributionTranslate

/-!
# The regularized spectrum and the regularized activation

Definition `def:regularized-synthesis`, parts (iii) and (iv): for a real tempered `β`, a cutoff
`χ`, and an approximate identity `(η_ε)`, the regularized spectrum
`β̂_ε = χ (β̂ * η_ε)` belongs to `C_c^∞(ℝ ∖ {0})`, and there is a real Schwartz function `β_ε`
with Fourier transform `β̂_ε`.

The convolution `(β̂ * η_ε)(ω) = ⟨β̂, η_ε(ω - ·)⟩` (`distributionConvolution`) is
`ω ↦ β̂ (translate η_ε ω)` with the Schwartz translates of
`OperatorRidgelet.ToMathlib.TemperedDistributionTranslate`, hence smooth
(`contDiff_distributionConvolution`); the cutoff provides the compact support away from the
origin.  Since `β` is real and `χ`, `η_ε` are real and even, `β̂_ε` is Hermitian symmetric
(`conj_regularizedSpectrum_neg`), so its inverse Fourier transform `realFilterOfHermitian` is a
real Schwartz function with Fourier transform `β̂_ε` (`filterFourier_regularizedActivation`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform ComplexConjugate

/-! ### The convolution with a test function -/

/-- `schwartzOfFun` picks the Schwartz function with the given values. -/
theorem schwartzOfFun_eq {f : ℝ → ℂ} (φ : SchwartzMap ℝ ℂ) (h : ⇑φ = f) : schwartzOfFun f = φ := by
  classical
  have hex : ∃ φ : SchwartzMap ℝ ℂ, ⇑φ = f := ⟨φ, h⟩
  rw [schwartzOfFun, dif_pos hex]
  exact SchwartzMap.ext fun x => (congrFun hex.choose_spec x).trans (congrFun h x).symm

/-- Embedding a smooth real function into the complex numbers preserves smoothness. -/
theorem contDiff_ofReal_comp {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => (η x : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hη

/-- Embedding a real function into the complex numbers preserves compact support. -/
theorem hasCompactSupport_ofReal_comp {η : ℝ → ℝ} (hc : HasCompactSupport η) :
    HasCompactSupport fun x => (η x : ℂ) :=
  hc.comp_left Complex.ofReal_zero

/-- The convolution `u * η` is `ω ↦ u (η(ω - ·))` with the Schwartz translates. -/
theorem distributionConvolution_eq (u : TemperedDistribution ℝ ℂ) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (ω : ℝ) :
    distributionConvolution u η ω =
      u (TemperedDistribution.translate (fun x => (η x : ℂ)) ω) := by
  unfold distributionConvolution
  congr 1
  exact schwartzOfFun_eq _ (TemperedDistribution.coe_translate (contDiff_ofReal_comp hη)
    (hasCompactSupport_ofReal_comp hc) ω)

/-- The convolution of a tempered distribution with a smooth compactly supported function is
smooth. -/
theorem contDiff_distributionConvolution (u : TemperedDistribution ℝ ℂ) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    ContDiff ℝ (⊤ : ℕ∞) (distributionConvolution u η) := by
  have h : distributionConvolution u η =
      fun ω => u (TemperedDistribution.translate (fun x => (η x : ℂ)) ω) :=
    funext (distributionConvolution_eq u hη hc)
  rw [h]
  exact TemperedDistribution.contDiff_apply_translate u (contDiff_ofReal_comp hη)
    (hasCompactSupport_ofReal_comp hc)

/-! ### The regularized spectrum is in `C_c^∞(ℝ ∖ {0})` -/

/-- **Definition `def:regularized-synthesis`(iii)**, smoothness. -/
theorem IsCutoff.contDiff_regularizedSpectrum {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ} (hη : IsApproximateIdentity η) {ε : ℝ} (hε : 0 < ε)
    (β : TemperedDistribution ℝ ℂ) : ContDiff ℝ (⊤ : ℕ∞) (regularizedSpectrum β χ η ε) := by
  unfold regularizedSpectrum
  exact (Complex.ofRealCLM.contDiff.comp hχ.contDiff).mul
    (contDiff_distributionConvolution _ (hη.contDiff ε hε) (hη.hasCompactSupport ε hε))

/-- **Definition `def:regularized-synthesis`(iii)**, compact support. -/
theorem IsCutoff.hasCompactSupport_regularizedSpectrum {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ) (ε : ℝ) (β : TemperedDistribution ℝ ℂ) :
    HasCompactSupport (regularizedSpectrum β χ η ε) :=
  (hχ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right

/-- **Definition `def:regularized-synthesis`(iii)**, support away from the origin. -/
theorem IsCutoff.zero_notMem_tsupport_regularizedSpectrum {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ}
    (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ) (ε : ℝ) (β : TemperedDistribution ℝ ℂ) :
    (0 : ℝ) ∉ tsupport (regularizedSpectrum β χ η ε) := by
  intro h
  apply hχ.zero_notMem_tsupport
  have h1 : tsupport (regularizedSpectrum β χ η ε) ⊆ tsupport fun ω => (χ ω : ℂ) :=
    tsupport_mul_subset_left
  have h2 : tsupport (fun ω => (χ ω : ℂ)) ⊆ tsupport χ :=
    closure_mono (Function.support_comp_subset Complex.ofReal_zero χ)
  exact h2 (h1 h)

/-! ### Hermitian symmetry and the regularized activation -/

/-- For real `β` and a real even kernel `η`, the convolution `β̂ * η` is Hermitian symmetric. -/
theorem IsRealDistribution.conj_distributionConvolution_neg {β : TemperedDistribution ℝ ℂ}
    (hβ : IsRealDistribution β) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (heven : ∀ x, η (-x) = η x) (ω : ℝ) :
    conj (distributionConvolution (angularFourierDistribution β) η (-ω)) =
      distributionConvolution (angularFourierDistribution β) η ω := by
  rw [distributionConvolution_eq _ hη hc, distributionConvolution_eq _ hη hc,
    hβ.conj_angularFourierDistribution_apply]
  congr 1
  ext x
  have hη' := contDiff_ofReal_comp hη
  have hc' := hasCompactSupport_ofReal_comp hc
  rw [reflectSchwartz_apply, schwartzConjugation_apply,
    TemperedDistribution.translate_apply hη' hc', TemperedDistribution.translate_apply hη' hc',
    Complex.conj_ofReal, show -ω - -x = -(ω - x) by ring, heven]

/-- The regularized spectrum of a real `β` is Hermitian symmetric. -/
theorem conj_regularizedSpectrum_neg {β : TemperedDistribution ℝ ℂ} (hβ : IsRealDistribution β)
    {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ} (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ}
    (hη : IsApproximateIdentity η) {ε : ℝ} (hε : 0 < ε) (ω : ℝ) :
    conj (regularizedSpectrum β χ η ε (-ω)) = regularizedSpectrum β χ η ε ω := by
  unfold regularizedSpectrum
  rw [map_mul, Complex.conj_ofReal, hχ.even,
    hβ.conj_distributionConvolution_neg (hη.contDiff ε hε) (hη.hasCompactSupport ε hε)
      (hη.even ε hε)]

/-- **Definition `def:regularized-synthesis`(iv)**, existence: a real Schwartz function with
Fourier transform `β̂_ε`. -/
theorem exists_regularizedActivation {β : TemperedDistribution ℝ ℂ} (hβ : IsRealDistribution β)
    {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ} (hχ : IsCutoff ρ χ) {η : ℝ → ℝ → ℝ}
    (hη : IsApproximateIdentity η) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : SchwartzMap ℝ ℝ, ∀ ω : ℝ, filterFourier b ω = regularizedSpectrum β χ η ε ω := by
  set ψ : SchwartzMap ℝ ℂ := (hχ.hasCompactSupport_regularizedSpectrum η ε β).toSchwartzMap
    (hχ.contDiff_regularizedSpectrum hη hε β) with hψdef
  have hψ : ∀ ω, ψ ω = regularizedSpectrum β χ η ε ω := fun ω => rfl
  refine ⟨realFilterOfHermitian ψ, fun ω => ?_⟩
  rw [filterFourier_realFilterOfHermitian ψ (fun ω => by
    rw [hψ, hψ]
    exact conj_regularizedSpectrum_neg hβ hχ hη hε ω), hψ]

/-- **Definition `def:regularized-synthesis`(iv)**: the chosen regularized activation has
Fourier transform `β̂_ε`. -/
theorem filterFourier_regularizedActivation {β : TemperedDistribution ℝ ℂ}
    (hβ : IsRealDistribution β) {ρ : SchwartzMap ℝ ℝ} {χ : ℝ → ℝ} (hχ : IsCutoff ρ χ)
    {η : ℝ → ℝ → ℝ} (hη : IsApproximateIdentity η) {ε : ℝ} (hε : 0 < ε) (ω : ℝ) :
    filterFourier (regularizedActivation β χ η ε) ω = regularizedSpectrum β χ η ε ω := by
  classical
  have hex := exists_regularizedActivation hβ hχ hη hε
  rw [regularizedActivation, dif_pos hex]
  exact hex.choose_spec ω

end OperatorRidgelet
