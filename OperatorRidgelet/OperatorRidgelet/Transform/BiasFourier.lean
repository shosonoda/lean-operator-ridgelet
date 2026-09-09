import OperatorRidgelet.Transform.Plancherel
import OperatorRidgelet.ToMathlib.IndicatorTendstoL2

/-!
# The partial Fourier transform in the bias of a square-integrable coefficient

Section 3 material behind Theorem `thm:C`(iv) and Proposition `prop:coefficient-projection`:
the bias-Fourier representatives of `HasBiasFourier` are unique up to null sets on almost every
ray, they satisfy Plancherel and Parseval along rays, and every `γ ∈ L²(λ)` has a jointly
measurable representative.

* **Uniqueness on a ray.**  Two square-integrable functions on `ℝ` with the same pairing against
  `φ̂` for every Schwartz `φ` agree almost everywhere
  (`ae_eq_of_forall_integral_mul_conj_lineFourier_eq`): the Fourier transform is a bijection of
  the Schwartz space, and test functions determine locally integrable functions.  Hence two
  representatives of the same coefficient agree almost everywhere on almost every ray
  (`HasBiasFourier.ae_ae_eq`).
* **The `L²` Fourier transform of a ray.**  `lineFourierL2 u hu` is Mathlib's `L²` Fourier
  transform of `u ∈ L²(ℝ)` at the rescaled frequency `ω / 2π`; it satisfies Parseval against
  Schwartz functions and Plancherel, so it is *the* representative on almost every ray, and every
  representative inherits Plancherel and the polarized Parseval identity
  (`HasBiasFourier.lintegral_enorm_sq_ae`, `HasBiasFourier.integral_mul_conj_ae`).
* **Existence.**  For measurable `γ ∈ L²(ν ⊗ dc)` the Fourier integrals of the truncations
  `γ 1_{|c| ≤ n}` along the bias (`sliceFourier`) are jointly measurable and form a Cauchy
  sequence in `L²(ν ⊗ dω)` (Plancherel along almost every ray); a measurable representative of
  the limit, rescaled to the manuscript's convention, is a bias-Fourier representative of `γ`
  (`exists_measurable_hasBiasFourier`), because along a subsequence almost every ray of it is
  the `L²` limit of the truncated transforms.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal FourierTransform

/-! ### Uniqueness along a ray -/

section Ray

/-- `lineFourier φ` is square integrable for Schwartz `φ`. -/
theorem memLp_lineFourier (φ : SchwartzMap ℝ ℂ) : MemLp (lineFourier φ) 2 volume := by
  have h : lineFourier φ = fun ω => (𝓕 φ : SchwartzMap ℝ ℂ) ((2 * Real.pi)⁻¹ * ω) := by
    funext ω
    rw [lineFourier_eq_fourier, SchwartzMap.fourier_coe]
  rw [h]
  exact ((𝓕 φ : SchwartzMap ℝ ℂ).memLp 2).comp_mul_left (by positivity)

/-- The pairing of a square-integrable function against `conj (lineFourier φ)` is integrable. -/
theorem integrable_mul_conj_lineFourier {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    Integrable fun ω => f ω * (starRingEnd ℂ) (lineFourier φ ω) :=
  hf.integrable_mul_conj (memLp_lineFourier φ)

/-- A smooth compactly supported real function is `lineFourier` of a Schwartz function. -/
theorem exists_schwartz_lineFourier_eq {r : ℝ → ℝ} (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (hrs : HasCompactSupport r) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ ω, lineFourier φ ω = (r ω : ℂ) := by
  set r' : ℝ → ℂ := fun u => (r (2 * Real.pi * u) : ℂ) with hr'
  have h₁ : HasCompactSupport r' :=
    (hrs.comp_homeomorph (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity))).comp_left
      Complex.ofReal_zero
  have h₂ : ContDiff ℝ (⊤ : ℕ∞) r' :=
    Complex.ofRealCLM.contDiff.comp (hr.comp (contDiff_const.mul contDiff_id))
  refine ⟨𝓕⁻ (h₁.toSchwartzMap h₂), fun ω => ?_⟩
  rw [lineFourier_eq_fourier, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  show r' ((2 * Real.pi)⁻¹ * ω) = _
  simp only [hr']
  rw [mul_inv_cancel_left₀ (by positivity)]

/-- **Uniqueness along a ray.**  Two square-integrable functions on `ℝ` with the same pairing
against `conj (lineFourier φ)` for every Schwartz `φ` agree almost everywhere. -/
theorem ae_eq_of_forall_integral_mul_conj_lineFourier_eq {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (h : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ ω, f ω * (starRingEnd ℂ) (lineFourier φ ω) =
        ∫ ω, g ω * (starRingEnd ℂ) (lineFourier φ ω)) :
    f =ᵐ[volume] g := by
  have hloc : LocallyIntegrable (fun ω => f ω - g ω) volume :=
    (hf.sub hg).locallyIntegrable one_le_two
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun r r_diff r_supp => ?_
  · filter_upwards [h0] with ω hω
    exact sub_eq_zero.mp hω
  obtain ⟨φ, hφ⟩ := exists_schwartz_lineFourier_eq r_diff r_supp
  have hval : ∀ ω, r ω • (f ω - g ω) =
      f ω * (starRingEnd ℂ) (lineFourier φ ω) - g ω * (starRingEnd ℂ) (lineFourier φ ω) := by
    intro ω
    rw [hφ ω, Complex.conj_ofReal, Complex.real_smul]
    ring
  simp_rw [hval]
  rw [integral_sub (integrable_mul_conj_lineFourier hf φ) (integrable_mul_conj_lineFourier hg φ),
    h φ, sub_self]

end Ray

/-! ### The `L²` Fourier transform of a ray -/

section LineFourierL2

/-- The pairing of two `L²` Fourier transforms is the pairing of the functions: the `L¹ ∩ L²`
Parseval identity `MeasureTheory.Integrable.integral_fourier_mul_conj_fourier` extended to `L²`
through Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`. -/
theorem integral_fourier_toLp_mul_conj {u v : ℝ → ℂ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    ∫ x, (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) x *
        (starRingEnd ℂ) ((𝓕 (hv.toLp v) : Lp ℂ 2 (volume : Measure ℝ)) x) =
      ∫ c, u c * (starRingEnd ℂ) (v c) := by
  have h1 : ∀ f g : Lp ℂ 2 (volume : Measure ℝ),
      ∫ x, f x * (starRingEnd ℂ) (g x) = inner ℂ g f := by
    intro f g
    rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [RCLike.inner_apply, mul_comm]
  rw [h1, Lp.inner_fourier_eq, ← h1]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Parseval for the `L²` Fourier transform against a Schwartz function. -/
theorem integral_fourier_toLp_mul_conj_fourier_schwartz {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ∫ x, (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) x * (starRingEnd ℂ) (𝓕 (φ : ℝ → ℂ) x) =
      ∫ c, u c * (starRingEnd ℂ) (φ c) := by
  rw [← integral_fourier_toLp_mul_conj hu (φ.memLp 2)]
  refine integral_congr_ae ?_
  filter_upwards [φ.integrable.fourier_toLp_ae_eq (φ.memLp 2)] with x hx
  rw [hx]

/-- The `L²` Fourier transform of `u ∈ L²(ℝ)` in the manuscript's convention
`û(ω) = ∫ u(t) e^{-itω} dt`: Mathlib's `L²` Fourier transform at the rescaled frequency
`ω / 2π`. -/
def lineFourierL2 (u : ℝ → ℂ) (hu : MemLp u 2 volume) (ω : ℝ) : ℂ :=
  (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) ((2 * Real.pi)⁻¹ * ω)

/-- `lineFourierL2 u` is square integrable. -/
theorem memLp_lineFourierL2 {u : ℝ → ℂ} (hu : MemLp u 2 volume) :
    MemLp (lineFourierL2 u hu) 2 volume :=
  (Lp.memLp _).comp_mul_left (by positivity)

/-- The polarized Plancherel identity for `lineFourierL2`:
`∫ û conj(v̂) dω = 2π ∫ u conj v dc`. -/
theorem integral_lineFourierL2_mul_conj {u v : ℝ → ℂ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    ∫ ω, lineFourierL2 u hu ω * (starRingEnd ℂ) (lineFourierL2 v hv ω) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ c, u c * (starRingEnd ℂ) (v c) := by
  unfold lineFourierL2
  rw [Measure.integral_comp_mul_left (fun x => (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) x *
    (starRingEnd ℂ) ((𝓕 (hv.toLp v) : Lp ℂ 2 (volume : Measure ℝ)) x)) (2 * Real.pi)⁻¹,
    inv_inv, abs_of_pos (by positivity), Complex.real_smul, integral_fourier_toLp_mul_conj hu hv]

/-- Parseval against Schwartz test functions for `lineFourierL2`, in the form of
`HasBiasFourier`. -/
theorem integral_mul_conj_eq_lineFourierL2 {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ∫ c, u c * (starRingEnd ℂ) (φ c) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ ω, lineFourierL2 u hu ω * (starRingEnd ℂ) (lineFourier φ ω) := by
  simp_rw [lineFourier_eq_fourier (φ : ℝ → ℂ)]
  unfold lineFourierL2
  rw [Measure.integral_comp_mul_left (fun x => (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) x *
    (starRingEnd ℂ) (𝓕 (φ : ℝ → ℂ) x)) (2 * Real.pi)⁻¹, inv_inv, abs_of_pos (by positivity),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity),
    Complex.ofReal_one, one_mul]
  exact (integral_fourier_toLp_mul_conj_fourier_schwartz hu φ).symm

/-- Plancherel for `lineFourierL2`: `∫⁻ ‖û‖ₑ² dω = 2π ∫⁻ ‖u‖ₑ² dc`. -/
theorem lintegral_lineFourierL2_sq {u : ℝ → ℂ} (hu : MemLp u 2 volume) :
    ∫⁻ ω, ‖lineFourierL2 u hu ω‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * ∫⁻ c, ‖u c‖ₑ ^ 2 := by
  unfold lineFourierL2
  set w : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu.toLp u) with hw
  have hmeas : AEMeasurable (fun x => ‖w x‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable w).enorm.pow_const 2
  rw [lintegral_comp_mul_left_volume hmeas (by positivity), inv_inv, abs_of_pos (by positivity)]
  congr 1
  rw [← eLpNorm_two_sq_eq_lintegral_enorm_sq', ← eLpNorm_two_sq_eq_lintegral_enorm_sq',
    ← eLpNorm_congr_ae hu.coeFn_toLp]
  have h := Lp.norm_fourier_eq (hu.toLp u)
  rw [Lp.norm_def, Lp.norm_def] at h
  rw [(ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp h]

end LineFourierL2

/-! ### Consequences for bias-Fourier representatives -/

section Representatives

variable {H : Type*} [MeasurableSpace H]

/-- **Uniqueness of bias-Fourier representatives**: two representatives of the same coefficient
agree almost everywhere on `ν`-almost every ray. -/
theorem HasBiasFourier.ae_ae_eq {ν : Measure H} {γ : H × ℝ → ℂ} {Φ Φ' : H → ℝ → ℂ}
    (h : HasBiasFourier ν γ Φ) (h' : HasBiasFourier ν γ Φ') :
    ∀ᵐ a ∂ν, Φ a =ᵐ[volume] Φ' a := by
  filter_upwards [h.memLp, h'.memLp, h.parseval, h'.parseval] with a h1 h2 h3 h4
  refine ae_eq_of_forall_integral_mul_conj_lineFourier_eq h1 h2 fun φ => ?_
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity))
    ((h3 φ).symm.trans (h4 φ))

/-- On `ν`-almost every ray, a bias-Fourier representative is the `L²` Fourier transform of the
ray function of the coefficient. -/
theorem HasBiasFourier.ae_ae_eq_lineFourierL2 {ν : Measure H} {γ : H × ℝ → ℂ} {Φ : H → ℝ → ℂ}
    (h : HasBiasFourier ν γ Φ) :
    ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      Φ a =ᵐ[volume] lineFourierL2 (fun c => γ (a, c)) hu := by
  filter_upwards [h.memLp, h.parseval] with a h1 h2 hu
  refine ae_eq_of_forall_integral_mul_conj_lineFourier_eq h1 (memLp_lineFourierL2 hu) fun φ => ?_
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity))
    ((h2 φ).symm.trans (integral_mul_conj_eq_lineFourierL2 hu φ))

variable {ν : Measure H} [SFinite ν]

/-- **Plancherel along rays** for a bias-Fourier representative of `γ ∈ L²(ν ⊗ dc)`:
`∫⁻ ‖Φ(a,ω)‖ₑ² dω = 2π ∫⁻ ‖γ(a,c)‖ₑ² dc` for `ν`-almost every `a`. -/
theorem HasBiasFourier.lintegral_enorm_sq_ae {γ : H × ℝ → ℂ} (hγ : MemLp γ 2 (ν.prod volume))
    {Φ : H → ℝ → ℂ} (h : HasBiasFourier ν γ Φ) :
    ∀ᵐ a ∂ν, ∫⁻ ω, ‖Φ a ω‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * ∫⁻ c, ‖γ (a, c)‖ₑ ^ 2 := by
  filter_upwards [h.ae_ae_eq_lineFourierL2, ae_memLp_slice hγ] with a ha hu
  refine (lintegral_congr_ae ?_).trans (lintegral_lineFourierL2_sq hu)
  filter_upwards [ha hu] with ω hω
  rw [hω]

/-- **Parseval along rays** for bias-Fourier representatives of `γ, γ' ∈ L²(ν ⊗ dc)`:
`∫ γ(a,c) conj(γ'(a,c)) dc = (2π)⁻¹ ∫ Φ(a,ω) conj(Φ'(a,ω)) dω` for `ν`-almost every `a`. -/
theorem HasBiasFourier.integral_mul_conj_ae {γ γ' : H × ℝ → ℂ} (hγ : MemLp γ 2 (ν.prod volume))
    (hγ' : MemLp γ' 2 (ν.prod volume)) {Φ Φ' : H → ℝ → ℂ} (h : HasBiasFourier ν γ Φ)
    (h' : HasBiasFourier ν γ' Φ') :
    ∀ᵐ a ∂ν, ∫ c, γ (a, c) * (starRingEnd ℂ) (γ' (a, c)) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ ω, Φ a ω * (starRingEnd ℂ) (Φ' a ω) := by
  filter_upwards [h.ae_ae_eq_lineFourierL2, h'.ae_ae_eq_lineFourierL2, ae_memLp_slice hγ,
    ae_memLp_slice hγ'] with a ha ha' hu hu'
  have hint : ∫ ω, Φ a ω * (starRingEnd ℂ) (Φ' a ω) =
      ∫ ω, lineFourierL2 _ hu ω * (starRingEnd ℂ) (lineFourierL2 _ hu' ω) := by
    apply integral_congr_ae
    filter_upwards [ha hu, ha' hu'] with ω h1 h2
    rw [h1, h2]
  rw [hint, integral_lineFourierL2_mul_conj hu hu', ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

end Representatives

/-! ### Existence of a jointly measurable representative -/

section Existence

variable {H : Type*} [MeasurableSpace H]

/-- The Fourier integral of the bias slices in Mathlib's convention,
`(a, ω) ↦ 𝓕 (γ(a,·)) ω`, as a function on `H × ℝ`. -/
def sliceFourier (γ : H × ℝ → ℂ) (p : H × ℝ) : ℂ :=
  ∫ c : ℝ, Complex.exp (((-2 * Real.pi * c * p.2 : ℝ) : ℂ) * Complex.I) * γ (p.1, c)

omit [MeasurableSpace H] in
theorem sliceFourier_eq (γ : H × ℝ → ℂ) (a : H) (ω : ℝ) :
    sliceFourier γ (a, ω) = 𝓕 (fun c => γ (a, c)) ω :=
  (Real.fourier_real_eq_integral_exp_smul _ _).symm

omit [MeasurableSpace H] in
/-- The Fourier integrand of a bias slice is integrable when the slice is. -/
theorem integrable_exp_mul_slice {γ : H × ℝ → ℂ} {a : H} (h : Integrable fun c => γ (a, c))
    (ω : ℝ) :
    Integrable fun c : ℝ => Complex.exp (((-2 * Real.pi * c * ω : ℝ) : ℂ) * Complex.I) * γ (a, c) :=
  h.bdd_mul (c := 1)
    (by fun_prop : Continuous fun c : ℝ =>
      Complex.exp (((-2 * Real.pi * c * ω : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
    (Eventually.of_forall fun c => (Complex.norm_exp_ofReal_mul_I _).le)

/-- `sliceFourier` is jointly measurable. -/
theorem measurable_sliceFourier {γ : H × ℝ → ℂ} (hγ : Measurable γ) :
    Measurable (sliceFourier γ) := by
  have hF : StronglyMeasurable fun q : (H × ℝ) × ℝ =>
      Complex.exp (((-2 * Real.pi * q.2 * q.1.2 : ℝ) : ℂ) * Complex.I) * γ (q.1.1, q.2) := by
    refine Measurable.stronglyMeasurable (Measurable.mul ?_ (hγ.comp
      (measurable_fst.fst.prodMk measurable_snd)))
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((measurable_const.mul measurable_snd).mul measurable_fst.snd)).mul measurable_const)
  exact hF.integral_prod_right'.measurable

omit [MeasurableSpace H] in
/-- `sliceFourier` is additive on coefficients with integrable slices. -/
theorem sliceFourier_sub {γ γ' : H × ℝ → ℂ} {p : H × ℝ} (h : Integrable fun c => γ (p.1, c))
    (h' : Integrable fun c => γ' (p.1, c)) :
    sliceFourier (γ - γ') p = sliceFourier γ p - sliceFourier γ' p := by
  unfold sliceFourier
  simp only [Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_exp_mul_slice h p.2) (integrable_exp_mul_slice h' p.2)

omit [MeasurableSpace H] in
/-- Plancherel along a bias line for a coefficient whose slice is in `L¹ ∩ L²`. -/
theorem lintegral_sliceFourier_sq {γ : H × ℝ → ℂ} {a : H} (h₁ : Integrable fun c => γ (a, c))
    (h₂ : MemLp (fun c => γ (a, c)) 2 volume) :
    ∫⁻ ω, ‖sliceFourier γ (a, ω)‖ₑ ^ 2 = ∫⁻ c, ‖γ (a, c)‖ₑ ^ 2 := by
  simp_rw [sliceFourier_eq]
  exact h₁.lintegral_enorm_fourier_sq h₂

variable {ν : Measure H} [SFinite ν]

/-- Plancherel on `H × ℝ` for a coefficient in `L²(ν ⊗ dc)` with `ν`-almost every slice in
`L¹`. -/
theorem lintegral_sliceFourier_prod_sq {γ : H × ℝ → ℂ} (hγ : Measurable γ)
    (h₁ : ∀ᵐ a ∂ν, Integrable fun c => γ (a, c)) (h₂ : MemLp γ 2 (ν.prod volume)) :
    ∫⁻ p, ‖sliceFourier γ p‖ₑ ^ 2 ∂ν.prod volume = ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂ν.prod volume := by
  rw [lintegral_prod _ ((measurable_sliceFourier hγ).enorm.pow_const 2).aemeasurable,
    lintegral_prod _ (hγ.enorm.pow_const 2).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, ae_memLp_slice h₂] with a ha hm
  exact lintegral_sliceFourier_sq ha hm

/-- **Existence of a jointly measurable bias-Fourier representative** for a measurable
coefficient in `L²(ν ⊗ dc)`. -/
theorem exists_measurable_hasBiasFourier {γ : H × ℝ → ℂ} (hγ : Measurable γ)
    (hγ₂ : MemLp γ 2 (ν.prod volume)) :
    ∃ Φ : H → ℝ → ℂ, Measurable (Function.uncurry Φ) ∧ HasBiasFourier ν γ Φ := by
  -- truncations in the bias
  set S : ℕ → Set (H × ℝ) := fun n => {p | |p.2| ≤ n} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  have hSmem : ∀ p : H × ℝ, ∀ᶠ n in atTop, p ∈ S n := fun p => by
    filter_upwards [eventually_ge_atTop ⌈|p.2|⌉₊] with n hn
    show |p.2| ≤ (n : ℝ)
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  set γn : ℕ → H × ℝ → ℂ := fun n => (S n).indicator γ with hγn
  have hγnm : ∀ n, Measurable (γn n) := fun n => hγ.indicator (hSm n)
  have hγn₂ : ∀ n, MemLp (γn n) 2 (ν.prod volume) := fun n => hγ₂.indicator (hSm n)
  have hS' : ∀ n : ℕ, MeasurableSet {c : ℝ | |c| ≤ n} := fun n =>
    measurableSet_le continuous_abs.measurable measurable_const
  have heq : ∀ n (a : H), (fun c => γn n (a, c)) = {c : ℝ | |c| ≤ n}.indicator fun c => γ (a, c) :=
    fun n a => rfl
  have hslice₂ : ∀ n (a : H), MemLp (fun c => γ (a, c)) 2 volume →
      MemLp (fun c => γn n (a, c)) 2 volume := fun n a ha => by
    rw [heq]
    exact ha.indicator (hS' n)
  have hslice₁ : ∀ n (a : H), MemLp (fun c => γ (a, c)) 2 volume →
      Integrable fun c => γn n (a, c) := fun n a ha => by
    rw [heq, integrable_indicator_iff (hS' n)]
    have hfin : volume {c : ℝ | |c| ≤ n} < ⊤ := by
      have : {c : ℝ | |c| ≤ n} = Set.Icc (-(n : ℝ)) n := by
        ext c
        simp [abs_le]
      rw [this]
      exact measure_Icc_lt_top
    haveI : IsFiniteMeasure (volume.restrict {c : ℝ | |c| ≤ n}) :=
      isFiniteMeasure_restrict.mpr hfin.ne
    exact (ha.restrict _).integrable one_le_two
  have hslice_ae : ∀ n, ∀ᵐ a ∂ν, Integrable fun c => γn n (a, c) := fun n => by
    filter_upwards [ae_memLp_slice hγ₂] with a ha
    exact hslice₁ n a ha
  -- the transforms of the truncations
  set Φn : ℕ → H × ℝ → ℂ := fun n => sliceFourier (γn n) with hΦn
  have hΦnm : ∀ n, Measurable (Φn n) := fun n => measurable_sliceFourier (hγnm n)
  have hΦn₂ : ∀ n, MemLp (Φn n) 2 (ν.prod volume) := fun n =>
    memLp_two_of_lintegral_enorm_sq_lt_top (hΦnm n).aestronglyMeasurable (by
      rw [lintegral_sliceFourier_prod_sq (hγnm n) (hslice_ae n) (hγn₂ n)]
      exact (hγn₂ n).lintegral_enorm_sq_lt_top)
  -- the transform is an isometry on the truncations
  have hdist : ∀ n m, dist ((hΦn₂ n).toLp _) ((hΦn₂ m).toLp _) =
      dist ((hγn₂ n).toLp _) ((hγn₂ m).toLp _) := by
    intro n m
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae ((hΦn₂ n).sub (hΦn₂ m)).coeFn_toLp,
      eLpNorm_congr_ae ((hγn₂ n).sub (hγn₂ m)).coeFn_toLp]
    have hsub : Φn n - Φn m =ᵐ[(ν.prod volume)] sliceFourier (γn n - γn m) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((hslice_ae n).and (hslice_ae m))]
        with p hp
      rw [Pi.sub_apply, ← sliceFourier_sub hp.1 hp.2]
    rw [eLpNorm_congr_ae hsub, eLpNorm_two_eq_lintegral_enorm_sq,
      eLpNorm_two_eq_lintegral_enorm_sq, lintegral_sliceFourier_prod_sq ((hγnm n).sub (hγnm m))
      (by
        filter_upwards [hslice_ae n, hslice_ae m] with a h1 h2
        exact h1.sub h2) ((hγn₂ n).sub (hγn₂ m))]
  -- the truncations converge to `γ`, hence their transforms converge
  have hγlim : Tendsto (fun n => (hγn₂ n).toLp (γn n)) atTop (𝓝 (hγ₂.toLp γ)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hγn₂ γ hγ₂).mpr
      (tendsto_eLpNorm_indicator_sub hγ₂ hSm hSmem)
  have hcauchy : CauchySeq fun n => (hΦn₂ n).toLp (Φn n) := by
    have h := Metric.cauchySeq_iff.mp hγlim.cauchySeq
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => by
      rw [hdist]
      exact hN m hm n hn⟩
  obtain ⟨Φlim, hΦlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  set Φ : H × ℝ → ℂ := (Lp.aestronglyMeasurable Φlim).mk _ with hΦdef
  have hΦm : Measurable Φ := (Lp.aestronglyMeasurable Φlim).stronglyMeasurable_mk.measurable
  have hΦeq : ⇑Φlim =ᵐ[(ν.prod volume)] Φ := (Lp.aestronglyMeasurable Φlim).ae_eq_mk
  have hΦ₂ : MemLp Φ 2 (ν.prod volume) := (Lp.memLp Φlim).ae_eq hΦeq
  have hΦlim : Tendsto (fun n => eLpNorm (Φn n - Φ) 2 (ν.prod volume)) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hΦlim).congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hΦn₂ n).coeFn_toLp, hΦeq] with p h1 h2
    simp only [Pi.sub_apply, h1, h2]
  -- a subsequence with summable squared errors
  have hsub : ∀ k : ℕ, ∃ N, ∀ n ≥ N, eLpNorm (Φn n - Φ) 2 (ν.prod volume) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    ENNReal.tendsto_atTop_zero.mp hΦlim _
      (ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) k)
  choose N hN using hsub
  set nk : ℕ → ℕ := fun k => max (N k) k with hnk
  have hnk_le : ∀ k, eLpNorm (Φn (nk k) - Φ) 2 (ν.prod volume) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    hN k _ (le_max_left _ _)
  have hnk_tendsto : Tendsto nk atTop atTop :=
    tendsto_atTop_mono (fun k => le_max_right _ _) tendsto_id
  -- the squared errors along rays are summable for almost every ray
  set e : ℕ → H → ℝ≥0∞ := fun k a => ∫⁻ ω, ‖Φn (nk k) (a, ω) - Φ (a, ω)‖ₑ ^ 2 with he
  have hem : ∀ k, Measurable (e k) := fun k =>
    (((hΦnm (nk k)).sub hΦm).enorm.pow_const 2).lintegral_prod_right'
  have hesum : ∫⁻ a, ∑' k, e k a ∂ν < ⊤ := by
    rw [lintegral_tsum fun k => (hem k).aemeasurable]
    calc ∑' k, ∫⁻ a, e k a ∂ν = ∑' k, ∫⁻ p, ‖Φn (nk k) p - Φ p‖ₑ ^ 2 ∂(ν.prod volume) := by
          congr 1
          funext k
          rw [lintegral_prod (fun p => ‖Φn (nk k) p - Φ p‖ₑ ^ 2)
            (((hΦnm (nk k)).sub hΦm).enorm.pow_const 2).aemeasurable]
      _ ≤ ∑' k, ((2⁻¹ : ℝ≥0∞) ^ 2) ^ k := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [← eLpNorm_two_sq_eq_lintegral_enorm_sq', ← pow_mul, mul_comm, pow_mul]
          exact ENNReal.pow_le_pow_left (hnk_le k)
      _ < ⊤ := by
          rw [ENNReal.tsum_geometric]
          refine ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr ?_)
          rw [← ENNReal.inv_pow]
          exact ENNReal.inv_lt_one.mpr (by norm_num)
  have hae : ∀ᵐ a ∂ν, Tendsto (fun k => e k a) atTop (𝓝 0) := by
    filter_upwards [ae_lt_top (Measurable.tsum hem) hesum.ne] with a ha
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne
  -- identification of the rays of the limit with the `L²` Fourier transforms of the rays of `γ`
  have hkey : ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      (fun ω => Φ (a, ω)) =ᵐ[volume] ⇑(𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) := by
    filter_upwards [hae, ae_memLp_slice hΦ₂, ae_memLp_slice hγ₂] with a ha hΦa hua hu
    -- the truncated rays converge in `L²(dc)`
    have hv : Tendsto (fun n => (hslice₂ n a hu).toLp _) atTop (𝓝 (hu.toLp _)) := by
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hslice₂ n a hu) _ hu).mpr ?_
      simp only [heq]
      exact tendsto_eLpNorm_indicator_sub hu hS' fun c => by
        filter_upwards [eventually_ge_atTop ⌈|c|⌉₊] with n hn
        show |c| ≤ (n : ℝ)
        exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    have hΦnv : ∀ n, (fun ω => Φn n (a, ω)) =ᵐ[volume]
        ⇑(𝓕 ((hslice₂ n a hu).toLp _) : Lp ℂ 2 (volume : Measure ℝ)) := fun n => by
      filter_upwards [(hslice₁ n a hu).fourier_toLp_ae_eq (hslice₂ n a hu)] with ω hω
      rw [hω]
      exact sliceFourier_eq _ a ω
    -- the errors of the two approximations tend to zero
    have h1 : Tendsto (fun k => eLpNorm ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) 2 volume)
        atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp ha
      rw [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num)] at h
      refine h.congr fun k => ?_
      rw [eLpNorm_sub_comm, eLpNorm_two_eq_lintegral_enorm_sq]
      rfl
    have h2 : Tendsto (fun k => eLpNorm ((fun ω => Φn (nk k) (a, ω)) -
        ⇑(𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure ℝ))) 2 volume) atTop (𝓝 0) := by
      have hF : Tendsto (fun k => (𝓕 ((hslice₂ (nk k) a hu).toLp _) : Lp ℂ 2 (volume : Measure ℝ)))
          atTop (𝓝 (𝓕 (hu.toLp _))) :=
        ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto _).comp (hv.comp hnk_tendsto)
      refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hF).congr fun k =>
        eLpNorm_congr_ae ?_
      filter_upwards [hΦnv (nk k)] with ω hω
      simp only [Pi.sub_apply, hω]
    have hmeas1 : ∀ k, AEStronglyMeasurable
        ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) volume := fun k =>
      hΦa.1.sub ((hΦnm (nk k)).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have h3 : ∀ k, eLpNorm ((fun ω => Φ (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure ℝ)))
        2 volume ≤
        eLpNorm ((fun ω => Φ (a, ω)) - fun ω => Φn (nk k) (a, ω)) 2 volume +
          eLpNorm ((fun ω => Φn (nk k) (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure ℝ)))
            2 volume := by
      intro k
      rw [← sub_add_sub_cancel (fun ω => Φ (a, ω)) (fun ω => Φn (nk k) (a, ω))]
      exact eLpNorm_add_le (hmeas1 k)
        ((((hΦnm (nk k)).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).sub
          (Lp.aestronglyMeasurable _)) one_le_two
    have h5 : eLpNorm ((fun ω => Φ (a, ω)) - ⇑(𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure ℝ)))
        2 volume = 0 :=
      le_antisymm (ge_of_tendsto' (by simpa using h1.add h2) h3) zero_le
    have h6 := (eLpNorm_eq_zero_iff (hΦa.1.sub (Lp.aestronglyMeasurable _)) two_ne_zero).mp h5
    filter_upwards [h6] with ω hω
    exact sub_eq_zero.mp hω
  -- rescale to the manuscript's convention
  have hkey' : ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      (fun ω => Φ (a, (2 * Real.pi)⁻¹ * ω)) =ᵐ[volume] lineFourierL2 (fun c => γ (a, c)) hu := by
    filter_upwards [hkey] with a ha hu
    exact (quasiMeasurePreserving_mul_left_volume (by positivity)).ae_eq_comp (ha hu)
  refine ⟨fun a ω => Φ (a, (2 * Real.pi)⁻¹ * ω),
    hΦm.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)), ?_, ?_⟩
  · filter_upwards [hkey', ae_memLp_slice hγ₂] with a ha hu
    exact (memLp_lineFourierL2 hu).ae_eq (ha hu).symm
  · filter_upwards [hkey', ae_memLp_slice hγ₂] with a ha hu φ
    rw [integral_mul_conj_eq_lineFourierL2 hu φ]
    congr 1
    apply integral_congr_ae
    filter_upwards [ha hu] with ω hω
    rw [hω]

end Existence

end OperatorRidgelet
