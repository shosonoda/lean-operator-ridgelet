import OperatorRidgelet.Sobolev.GaussianRays
import OperatorRidgelet.ToMathlib.RpowOneAddRpow

/-!
# The Sobolev test `q_{α,ρ}` of the Gaussian-derivative filters

The third hypothesis of `thm:weak-sobolev-synthesis` is that
`q_{α,ρ}(ω) = ρ̂(-ω) |ω|^{-α}` lies in `H^s_ω(ℝ)`.  For the Gaussian-derivative filters this is
proved by subordination: the Gamma integral

`|ω|^{-α} = Γ(α/2)^{-1} ∫_0^∞ u^{α/2-1} e^{-uω²} du`

writes `q_{α,ρ_k}` as a superposition of the symbols `ω^{2k} e^{-(1+u)ω²}` of the rays at the
scales `B(u) = (1+u)^{1/2}`, so its coefficient is the corresponding superposition of the
dilated filters.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Set
open scoped ENNReal

/-- The subordination scale is at least one. -/
theorem one_le_subScale {u : ℝ} (hu : 0 ≤ u) : 1 ≤ subScale u := by
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + u) := Real.sqrt_le_sqrt (by linarith)

/-- The subordination scale is positive. -/
theorem subScale_pos {u : ℝ} (hu : 0 ≤ u) : 0 < subScale u :=
  lt_of_lt_of_le zero_lt_one (one_le_subScale hu)

/-- The square of the subordination scale. -/
theorem subScale_sq {u : ℝ} (hu : 0 ≤ u) : subScale u ^ 2 = 1 + u := by
  rw [subScale, Real.sq_sqrt (by linarith)]

/-- Powers of the subordination scale. -/
theorem subScale_rpow {u : ℝ} (hu : 0 ≤ u) (x : ℝ) : subScale u ^ x = (1 + u) ^ (x / 2) := by
  rw [subScale, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
  congr 1
  ring

/-- **The Gamma subordination formula** `∫_0^∞ u^{α/2-1} e^{-uω²} du = |ω|^{-α} Γ(α/2)`. -/
theorem integral_subordination {α : ℝ} (hα : 0 < α) {ω : ℝ} (hω : ω ≠ 0) :
    ∫ u in Ioi (0 : ℝ), u ^ (α / 2 - 1) * Real.exp (-(ω ^ 2 * u)) =
      |ω| ^ (-α) * Real.Gamma (α / 2) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < α / 2)
    (by positivity : 0 < ω ^ 2)]
  congr 1
  have habs : (0 : ℝ) < |ω| := abs_pos.mpr hω
  have hsq : ω ^ 2 = |ω| ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [one_div, hsq, ← Real.rpow_neg_one (|ω| ^ (2 : ℝ)), ← Real.rpow_mul habs.le,
    ← Real.rpow_mul habs.le]
  congr 1
  ring

/-! ### The `L¹` size of a dilated filter -/

/-- A dilated filter is integrable. -/
theorem integrable_gaussRayFun (k : ℕ) {A : ℝ} (hA : 0 < A) :
    Integrable (gaussRayFun k A) volume := by
  have h : Integrable (fun b : ℝ => gaussDerivFilterC k (b / A)) volume :=
    MeasureTheory.Integrable.comp_div
      ((gaussDerivFilterC k).integrable (μ := (volume : Measure ℝ))) hA.ne'
  exact MeasureTheory.Integrable.smul (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) h

/-- The `L¹` norm of a dilated filter: `‖ρ_k(·/A) A^{-2k-1}‖₁ = A^{-2k} ‖ρ_k‖₁`. -/
theorem integral_norm_gaussRayFun (k : ℕ) {A : ℝ} (hA : 0 < A) :
    ∫ b : ℝ, ‖gaussRayFun k A b‖ = A ^ (-(2 * (k : ℝ))) * ∫ b : ℝ, ‖gaussDerivFilterC k b‖ := by
  have hdiv := Measure.integral_comp_div (fun b : ℝ => ‖gaussDerivFilterC k b‖) A
  rw [smul_eq_mul, abs_of_pos hA] at hdiv
  have hnorm : ∀ b : ℝ, ‖gaussRayFun k A b‖ =
      A ^ (-(2 * (k : ℝ) + 1)) * ‖gaussDerivFilterC k (b / A)‖ := by
    intro b
    unfold gaussRayFun
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  simp only [hnorm]
  rw [integral_const_mul, hdiv, ← mul_assoc]
  congr 1
  have h1 : A ^ (-(2 * (k : ℝ) + 1)) * A = A ^ (-(2 * (k : ℝ))) := by
    nth_rewrite 2 [show (A : ℝ) = A ^ (1 : ℝ) from (Real.rpow_one A).symm]
    rw [← Real.rpow_add hA]
    congr 1
    ring
  exact h1

/-! ### The subordination superposition -/

/-- The dilated filters depend measurably on the scale parameter and the bias. -/
theorem measurable_subScale_gaussRayFun (k : ℕ) :
    Measurable fun z : ℝ × ℝ => gaussRayFun k (subScale z.1) z.2 := by
  have hsub : Measurable fun u : ℝ => subScale u := by
    unfold subScale
    fun_prop
  have h2 : Measurable fun z : ℝ × ℝ => ((subScale z.1) ^ (-(2 * (k : ℝ) + 1)) : ℝ) := by
    fun_prop
  have h3 : Measurable fun z : ℝ × ℝ => gaussDerivFilterC k (z.2 / subScale z.1) :=
    (gaussDerivFilterC k).continuous.measurable.comp (by fun_prop)
  unfold gaussRayFun
  exact h2.smul h3

/-- The subordination integrand is jointly measurable. -/
theorem stronglyMeasurable_subordination (k : ℕ) (α : ℝ) :
    StronglyMeasurable
      (fun z : ℝ × ℝ => (z.1 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.1) z.2) := by
  refine Measurable.stronglyMeasurable ?_
  have h1 : Measurable fun z : ℝ × ℝ => (z.1 ^ (α / 2 - 1) : ℝ) := by fun_prop
  have hsub : Measurable fun u : ℝ => subScale u := by
    unfold subScale
    fun_prop
  have h2 : Measurable fun z : ℝ × ℝ => ((subScale z.1) ^ (-(2 * (k : ℝ) + 1)) : ℝ) := by
    fun_prop
  have h3 : Measurable fun z : ℝ × ℝ => gaussDerivFilterC k (z.2 / subScale z.1) := by
    have hcont : Measurable fun z : ℝ × ℝ => z.2 / subScale z.1 := by fun_prop
    exact (gaussDerivFilterC k).continuous.measurable.comp hcont
  have heq : (fun z : ℝ × ℝ => (z.1 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.1) z.2) =
      fun z : ℝ × ℝ => ((z.1 ^ (α / 2 - 1) : ℝ) * ((subScale z.1) ^ (-(2 * (k : ℝ) + 1)) : ℝ)) •
        gaussDerivFilterC k (z.2 / subScale z.1) := by
    funext z
    unfold gaussRayFun
    rw [smul_smul]
  rw [heq]
  exact (h1.mul h2).smul h3

/-- The subordination integrand is jointly measurable for the product measure. -/
theorem aestronglyMeasurable_subordination (k : ℕ) (α : ℝ) :
    AEStronglyMeasurable
      (fun z : ℝ × ℝ => (z.1 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.1) z.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
  (stronglyMeasurable_subordination k α).aestronglyMeasurable

/-- The subordination integrand is jointly integrable when `0 < α < 2k`. -/
theorem integrable_subordination (k : ℕ) {α : ℝ} (hα : 0 < α) (hk : α < 2 * k) :
    Integrable (fun z : ℝ × ℝ => (z.1 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.1) z.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  set M : ℝ := ∫ b : ℝ, ‖gaussDerivFilterC k b‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  rw [integrable_prod_iff (aestronglyMeasurable_subordination k α)]
  constructor
  · refine Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun u hu => ?_
    exact MeasureTheory.Integrable.smul (u ^ (α / 2 - 1) : ℝ)
      (integrable_gaussRayFun k (subScale_pos (le_of_lt hu)))
  · have hval : ∀ u ∈ Ioi (0 : ℝ),
        (∫ b : ℝ, ‖(u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b‖) =
          u ^ (α / 2 - 1) * (1 + u) ^ (-(k : ℝ)) * M := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      have hB := subScale_pos hu0.le
      have hnorm : ∀ b : ℝ, ‖(u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b‖ =
          u ^ (α / 2 - 1) * ‖gaussRayFun k (subScale u) b‖ := by
        intro b
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      simp only [hnorm]
      rw [integral_const_mul, integral_norm_gaussRayFun k hB, subScale_rpow hu0.le, ← hM,
        ← mul_assoc]
      congr 2
      push_cast
      ring_nf
    have hmain : Integrable (fun u : ℝ => u ^ (α / 2 - 1) * (1 + u) ^ (-(k : ℝ)) * M)
        (volume.restrict (Ioi (0 : ℝ))) :=
      MeasureTheory.Integrable.mul_const
        (Real.integrableOn_rpow_mul_one_add_rpow (a := α / 2 - 1) (c := -(k : ℝ))
          (by linarith) (by push_cast; linarith)) M
    refine MeasureTheory.Integrable.congr hmain ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hval u hu).symm

/-! ### The profile of the subordination superposition -/

/-- **The profile of `q_{α,ρ_k}`**: the superposition has the profile
`ρ̂_k(-ω) |ω|^{-α}` of `thm:weak-sobolev-synthesis`. -/
theorem rayProfile_gaussSobolevRay {k : ℕ} (hk1 : 1 ≤ k) {α : ℝ} (hα : 0 < α)
    (hk : α < 2 * k) (ω : ℝ) :
    rayProfile (gaussSobolevRay k α) ω =
      filterFourier (gaussDerivFilter k) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set f : ℝ → ℝ → ℂ := fun u b =>
    Complex.exp (((-(ω * b) : ℝ) : ℂ) * Complex.I) •
      ((u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b) with hf
  have hI : Integrable (Function.uncurry f) (μ.prod volume) := by
    refine MeasureTheory.Integrable.mono' (integrable_subordination k hα hk).norm ?_ ?_
    · have hexp : AEStronglyMeasurable
          (fun z : ℝ × ℝ => Complex.exp (((-(ω * z.2) : ℝ) : ℂ) * Complex.I)) (μ.prod volume) :=
        (Complex.continuous_exp.comp
          (by fun_prop : Continuous fun z : ℝ × ℝ =>
            ((-(ω * z.2) : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
      exact hexp.smul (aestronglyMeasurable_subordination k α)
    · refine Filter.Eventually.of_forall fun z => ?_
      show ‖Complex.exp (((-(ω * z.2) : ℝ) : ℂ) * Complex.I) •
        ((z.1 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.1) z.2)‖ ≤ _
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hswap : ∫ b : ℝ, (∫ u : ℝ, f u b ∂μ) = ∫ u : ℝ, (∫ b : ℝ, f u b) ∂μ :=
    (integral_integral_swap hI).symm
  have hinner : ∀ u : ℝ, ∫ b : ℝ, f u b = (u ^ (α / 2 - 1) : ℝ) •
      rayProfile (gaussRayFun k (subScale u)) ω := by
    intro u
    rw [rayProfile, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    show Complex.exp (((-(ω * b) : ℝ) : ℂ) * Complex.I) •
        ((u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b) =
      (u ^ (α / 2 - 1) : ℝ) •
        (Complex.exp (((-(ω * b) : ℝ) : ℂ) * Complex.I) • gaussRayFun k (subScale u) b)
    rw [smul_comm]
  have houter : rayProfile (fun b => ∫ u : ℝ, (u ^ (α / 2 - 1) : ℝ) •
      gaussRayFun k (subScale u) b ∂μ) ω =
      ∫ u : ℝ, (u ^ (α / 2 - 1) : ℝ) • rayProfile (gaussRayFun k (subScale u)) ω ∂μ := by
    rw [rayProfile]
    have hstep : ∀ b : ℝ, Complex.exp (((-(ω * b) : ℝ) : ℂ) * Complex.I) •
        (∫ u : ℝ, (u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b ∂μ) =
        ∫ u : ℝ, f u b ∂μ := by
      intro b
      rw [hf, ← integral_smul]
    simp only [hstep]
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact hinner u
  unfold gaussSobolevRay
  rw [rayProfile_const_smul, houter]
  have hprof : ∀ u : ℝ, 0 ≤ u → (u ^ (α / 2 - 1) : ℝ) •
      rayProfile (gaussRayFun k (subScale u)) ω =
      (((u ^ (α / 2 - 1) *
        (ω ^ (2 * k) * Real.exp (-(ω ^ 2 * u)) * Real.exp (-ω ^ 2)) : ℝ)) : ℂ) := by
    intro u hu
    rw [rayProfile_gaussRayFun (subScale_pos hu) k ω, subScale_sq hu]
    rw [Complex.real_smul]
    push_cast
    have hexp : Complex.exp (-((1 + (u : ℂ)) * (ω : ℂ) ^ 2))
        = Complex.exp (-((ω : ℂ) ^ 2 * (u : ℂ))) * Complex.exp (-(ω : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  have hcongr : ∫ u : ℝ, (u ^ (α / 2 - 1) : ℝ) • rayProfile (gaussRayFun k (subScale u)) ω ∂μ
      = ∫ u : ℝ, (((u ^ (α / 2 - 1) *
          (ω ^ (2 * k) * Real.exp (-(ω ^ 2 * u)) * Real.exp (-ω ^ 2)) : ℝ)) : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact hprof u (le_of_lt hu)
  have hreal : ∫ u : ℝ, (u ^ (α / 2 - 1) *
        (ω ^ (2 * k) * Real.exp (-(ω ^ 2 * u)) * Real.exp (-ω ^ 2))) ∂μ
      = ω ^ (2 * k) * Real.exp (-ω ^ 2) *
        ∫ u : ℝ, (u ^ (α / 2 - 1) * Real.exp (-(ω ^ 2 * u))) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  rw [hcongr, integral_complex_ofReal, hreal, filterFourier_gaussDerivFilter]
  rw [show (-ω) ^ (2 * k) = ω ^ (2 * k) by rw [pow_mul, pow_mul, neg_pow]; simp,
    show (-ω) ^ 2 = ω ^ 2 from neg_pow_two ω]
  rcases eq_or_ne ω 0 with rfl | hω
  · have hzero : (0 : ℝ) ^ (2 * k) = 0 := by
      refine zero_pow ?_
      omega
    rw [hzero]
    simp
  · rw [hμ, integral_subordination hα hω]
    have hΓ : Real.Gamma (α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp

/-! ### The Sobolev membership of the superposition -/

/-- The superposition is strongly measurable. -/
theorem stronglyMeasurable_gaussSobolevRay (k : ℕ) (α : ℝ) :
    StronglyMeasurable (gaussSobolevRay k α) := by
  have hsw : StronglyMeasurable
      (fun z : ℝ × ℝ => (z.2 ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale z.2) z.1) :=
    (stronglyMeasurable_subordination k α).comp_measurable measurable_swap
  have h := hsw.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  unfold gaussSobolevRay
  exact StronglyMeasurable.const_smul h ((Real.Gamma (α / 2))⁻¹ : ℝ)

/-- The `L²` mass of the dilated filter against the Sobolev weight. -/
theorem lintegral_bracket_gaussRayFun_le (k : ℕ) {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) :
    ∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖gaussRayFun k A b‖ₑ ^ 2 ≤
      ENNReal.ofReal ((A ^ (s - 2 * (k : ℝ) - 1 / 2) *
        raySobolevNorm s (gaussDerivFilterC k)) ^ 2 / (2 * Real.pi)) := by
  rw [lintegral_bracket_rpow_enorm_sq (memRaySobolev_gaussRayFun_of_one_le k hs hA)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbound := raySobolevNorm_gaussRayFun_le k hs hA
  have hnn : 0 ≤ raySobolevNorm s (gaussRayFun k A) := raySobolevNorm_nonneg _ _
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ hnn hbound 2

/-- **The Sobolev membership of `q_{α,ρ_k}`**: the superposition lies in `H^s_ω(ℝ)` in the
range `2k > α + 2s - 1/2` of `eq:nonbandpass-order`. -/
theorem memRaySobolev_gaussSobolevRay {k : ℕ} {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (hk : α + 2 * s - 1 / 2 < 2 * k) :
    MemRaySobolev s (gaussSobolevRay k α) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set c : ℝ := s - 2 * (k : ℝ) - 1 / 2 with hc
  set N : ℝ := raySobolevNorm s (gaussDerivFilterC k) with hN
  set w : ℝ → ℝ := fun u => u ^ (α / 2 - 1) with hw
  set m : ℝ → ℝ := fun u => (1 + u) ^ (c / 2) with hm
  set G : ℝ → ℝ → ℂ := fun u b => gaussRayFun k (subScale u) b with hG
  -- the finiteness of the one scalar integral that the estimate needs
  have hofReal : ∀ f : ℝ → ℝ, Integrable f μ → (∫⁻ u : ℝ, ENNReal.ofReal (f u) ∂μ) ≠ ⊤ := by
    intro f hf
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun u => ?_) hf.hasFiniteIntegral)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hKint : Integrable (fun u : ℝ => w u * m u) μ :=
    Real.integrableOn_rpow_mul_one_add_rpow (a := α / 2 - 1) (c := c / 2) (by linarith)
      (by rw [hc]; linarith)
  set K : ℝ≥0∞ := ∫⁻ u : ℝ, ENNReal.ofReal (w u * m u) ∂μ with hK
  have hKtop : K ≠ ⊤ := hofReal _ hKint
  -- the pointwise Hölder bound
  have hpoint : ∀ b : ℝ, ‖gaussSobolevRay k α b‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.Gamma (α / 2))⁻¹ ^ 2) *
        (K * ∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ) := by
    intro b
    have hwpos : ∀ u ∈ Ioi (0 : ℝ), 0 < w u := fun u hu => Real.rpow_pos_of_pos hu _
    have hmpos : ∀ u ∈ Ioi (0 : ℝ), 0 < m u := fun u hu =>
      Real.rpow_pos_of_pos (by linarith [mem_Ioi.mp hu]) _
    -- the superposition is dominated by the weighted `L¹` mass of the rays
    have hJ : ‖gaussSobolevRay k α b‖ₑ ≤
        ENNReal.ofReal |(Real.Gamma (α / 2))⁻¹| *
          ∫⁻ u : ℝ, ENNReal.ofReal (w u) * ‖G u b‖ₑ ∂μ := by
      unfold gaussSobolevRay
      rw [enorm_smul, Real.enorm_eq_ofReal_abs]
      refine mul_le_mul_left' ?_ _
      refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
      refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun u hu => ?_))
      show ‖(u ^ (α / 2 - 1) : ℝ) • gaussRayFun k (subScale u) b‖ₑ
          = ENNReal.ofReal (w u) * ‖G u b‖ₑ
      rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (hwpos u hu)]
    -- Hölder against the finite weight `w m`
    have hholder : (∫⁻ u : ℝ, ENNReal.ofReal (w u) * ‖G u b‖ₑ ∂μ) ≤
        K ^ ((1 : ℝ) / 2) *
          (∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
      set F : ℝ → ℝ≥0∞ := fun u => (ENNReal.ofReal (w u * m u)) ^ ((1 : ℝ) / 2) with hF
      set Gg : ℝ → ℝ≥0∞ := fun u =>
        (ENNReal.ofReal (w u / m u)) ^ ((1 : ℝ) / 2) * ‖G u b‖ₑ with hGg
      have hFm : AEMeasurable F μ := by
        refine ENNReal.measurable_ofReal.comp_aemeasurable ?_ |>.pow_const _
        exact ((by fun_prop : Measurable fun u : ℝ => w u * m u)).aemeasurable
      have hGm : AEMeasurable Gg μ := by
        have h1 : AEMeasurable (fun u : ℝ => (ENNReal.ofReal (w u / m u)) ^ ((1 : ℝ) / 2)) μ := by
          refine ENNReal.measurable_ofReal.comp_aemeasurable ?_ |>.pow_const _
          exact ((by fun_prop : Measurable fun u : ℝ => w u / m u)).aemeasurable
        have h2 : AEMeasurable (fun u : ℝ => ‖G u b‖ₑ) μ := by
          have hsub : Measurable fun u : ℝ => subScale u := by
            unfold subScale
            fun_prop
          have hc2 : Measurable fun u : ℝ => ((subScale u) ^ (-(2 * (k : ℝ) + 1)) : ℝ) := by
            fun_prop
          have h3 : Measurable fun u : ℝ => gaussDerivFilterC k (b / subScale u) :=
            (gaussDerivFilterC k).continuous.measurable.comp (by fun_prop)
          have hGmeas : Measurable fun u : ℝ => G u b := by
            show Measurable fun u : ℝ => gaussRayFun k (subScale u) b
            unfold gaussRayFun
            exact hc2.smul h3
          exact hGmeas.enorm.aemeasurable
        exact h1.mul h2
      have hprod : ∀ u ∈ Ioi (0 : ℝ), (F * Gg) u = ENNReal.ofReal (w u) * ‖G u b‖ₑ := by
        intro u hu
        have hw0 := hwpos u hu
        have hm0 := hmpos u hu
        have hmul : ENNReal.ofReal (w u * m u) * ENNReal.ofReal (w u / m u) =
            (ENNReal.ofReal (w u)) ^ (2 : ℕ) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hw0.le]
          congr 1
          field_simp
        show (ENNReal.ofReal (w u * m u)) ^ ((1 : ℝ) / 2) *
            ((ENNReal.ofReal (w u / m u)) ^ ((1 : ℝ) / 2) * ‖G u b‖ₑ) = _
        rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hmul,
          ← ENNReal.rpow_natCast (ENNReal.ofReal (w u)) 2, ← ENNReal.rpow_mul]
        norm_num
      have hFsq : ∀ u ∈ Ioi (0 : ℝ), F u ^ (2 : ℝ) = ENNReal.ofReal (w u * m u) := by
        intro u hu
        rw [hF, ← ENNReal.rpow_mul]
        norm_num
      have hGsq : ∀ u ∈ Ioi (0 : ℝ),
          Gg u ^ (2 : ℝ) = ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 := by
        intro u hu
        rw [hGg, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_natCast (‖G u b‖ₑ) 2]
        norm_num
      have hae : ∀ (f g : ℝ → ℝ≥0∞), (∀ u ∈ Ioi (0 : ℝ), f u = g u) →
          ∫⁻ u : ℝ, f u ∂μ = ∫⁻ u : ℝ, g u ∂μ := fun f g h =>
        lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall h))
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hFm hGm
      rw [hae _ _ hprod, hae _ _ hFsq, hae _ _ hGsq] at this
      exact this
    calc ‖gaussSobolevRay k α b‖ₑ ^ 2
        ≤ (ENNReal.ofReal |(Real.Gamma (α / 2))⁻¹| *
            ∫⁻ u : ℝ, ENNReal.ofReal (w u) * ‖G u b‖ₑ ∂μ) ^ 2 := by
          exact pow_le_pow_left' hJ 2
      _ ≤ (ENNReal.ofReal |(Real.Gamma (α / 2))⁻¹| *
            (K ^ ((1 : ℝ) / 2) *
              (∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2))) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal ((Real.Gamma (α / 2))⁻¹ ^ 2) *
            (K * ∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ) := by
          rw [mul_pow, mul_pow, ← ENNReal.rpow_natCast (K ^ ((1 : ℝ) / 2)) 2,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast
              ((∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) 2,
            ← ENNReal.rpow_mul]
          norm_num
          congr 1
          rw [← ENNReal.ofReal_pow (by positivity), inv_pow, sq_abs]
  -- the `L²` mass of each ray
  have hray : ∀ u ∈ Ioi (0 : ℝ),
      (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖G u b‖ₑ ^ 2) ≤
        ENNReal.ofReal (m u ^ 2 * (N ^ 2 / (2 * Real.pi))) := by
    intro u hu
    have hB := one_le_subScale (le_of_lt (mem_Ioi.mp hu))
    have h := lintegral_bracket_gaussRayFun_le k (A := subScale u) hs hB
    refine h.trans (le_of_eq ?_)
    congr 1
    have hmu : (1 + u) ^ ((s - 2 * (k : ℝ) - 1 / 2) / 2) = m u := rfl
    rw [subScale_rpow (le_of_lt (mem_Ioi.mp hu)), hmu, ← hN]
    ring
  -- the swap
  have hmeasprod : AEMeasurable (Function.uncurry fun (b : ℝ) (u : ℝ) =>
      ENNReal.ofReal (bracket b ^ (2 * s)) *
        (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2)) (volume.prod μ) := by
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (bracket z.1 ^ (2 * s)) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (continuous_bracket.rpow_const
        fun _ => Or.inl (bracket_pos _).ne').measurable.comp measurable_fst
    have h2 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (w z.2 / m z.2) := by
      refine ENNReal.measurable_ofReal.comp ?_
      fun_prop
    have h3 : Measurable fun z : ℝ × ℝ => ‖G z.2 z.1‖ₑ ^ 2 :=
      (((measurable_subScale_gaussRayFun k).comp measurable_swap).enorm).pow_const 2
    exact h1.mul (h2.mul h3)
  have hswap2 : (∫⁻ b : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
        (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2) ∂μ) =
      ∫⁻ u : ℝ, (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
        (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2)) ∂μ :=
    lintegral_lintegral_swap hmeasprod
  set C : ℝ≥0∞ := ENNReal.ofReal ((Real.Gamma (α / 2))⁻¹ ^ 2) with hCdef
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [memRaySobolev_iff (stronglyMeasurable_gaussSobolevRay k α).aestronglyMeasurable]
  constructor
  · exact (((continuous_bracket.rpow_const fun _ =>
      Or.inl (bracket_pos _).ne').aestronglyMeasurable).mul
      (((stronglyMeasurable_gaussSobolevRay k α).norm.pow 2).aestronglyMeasurable))
  · have hrewrite : ∀ b : ℝ, ‖(bracket b ^ (2 * s) : ℝ) * ‖gaussSobolevRay k α b‖ ^ 2‖ₑ
        = ENNReal.ofReal (bracket b ^ (2 * s)) * ‖gaussSobolevRay k α b‖ₑ ^ 2 := by
      intro b
      rw [Real.enorm_eq_ofReal
          (mul_nonneg (Real.rpow_nonneg (bracket_pos b).le _) (by positivity)),
        ENNReal.ofReal_mul (Real.rpow_nonneg (bracket_pos b).le _)]
      congr 1
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have hstepA : ∀ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
        (C * (K * ∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ)) =
        C * K * ∫⁻ u : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
          (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2) ∂μ := by
      intro b
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ring
    have hstepD : ∀ u : ℝ, (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
          (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2)) =
        ENNReal.ofReal (w u / m u) *
          ∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖G u b‖ₑ ^ 2 := by
      intro u
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun b => ?_
      ring
    have hfinal : (∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) *
        (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖G u b‖ₑ ^ 2) ∂μ) ≤
        ENNReal.ofReal (N ^ 2 / (2 * Real.pi)) * K := by
      have hle : (∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) *
          (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖G u b‖ₑ ^ 2) ∂μ) ≤
          ∫⁻ u : ℝ, ENNReal.ofReal (N ^ 2 / (2 * Real.pi)) *
            ENNReal.ofReal (w u * m u) ∂μ := by
        refine lintegral_mono_ae (μ := μ) ?_
        rw [hμ]
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
        have hw0 : 0 < w u := Real.rpow_pos_of_pos hu _
        have hm0 : 0 < m u := Real.rpow_pos_of_pos (by linarith [mem_Ioi.mp hu]) _
        refine le_trans (mul_le_mul_left' (hray u hu) _) (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      refine hle.trans (le_of_eq ?_)
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    show (∫⁻ b : ℝ, ‖(bracket b ^ (2 * s) : ℝ) * ‖gaussSobolevRay k α b‖ ^ 2‖ₑ) < ⊤
    calc (∫⁻ b : ℝ, ‖(bracket b ^ (2 * s) : ℝ) * ‖gaussSobolevRay k α b‖ ^ 2‖ₑ)
        = ∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖gaussSobolevRay k α b‖ₑ ^ 2 :=
          lintegral_congr hrewrite
      _ ≤ ∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
            (C * (K * ∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2 ∂μ)) :=
          lintegral_mono fun b => by gcongr; exact hpoint b
      _ = C * K * ∫⁻ b : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) *
            (ENNReal.ofReal (w u / m u) * ‖G u b‖ₑ ^ 2) ∂μ := by
          rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hCtop hKtop)]
          exact lintegral_congr hstepA
      _ = C * K * ∫⁻ u : ℝ, ENNReal.ofReal (w u / m u) *
            (∫⁻ b : ℝ, ENNReal.ofReal (bracket b ^ (2 * s)) * ‖G u b‖ₑ ^ 2) ∂μ := by
          rw [hswap2]
          congr 1
          exact lintegral_congr hstepD
      _ ≤ C * K * (ENNReal.ofReal (N ^ 2 / (2 * Real.pi)) * K) := by gcongr
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hCtop.lt_top hKtop.lt_top) ?_
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKtop.lt_top

end OperatorRidgelet
