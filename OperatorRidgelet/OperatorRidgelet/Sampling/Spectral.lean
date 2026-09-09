import OperatorRidgelet.Sampling.Basic
import OperatorRidgelet.Reconstruction.Tempered

/-!
# Finite variation and moments of the ridgelet coefficient

The material behind Theorem `thm:E`.  For a band-pass filter `ρ` with frequency window `I` and a
density `G` regular along rays, the uniform decay of the explicit coefficient
(`exists_const_forall_enorm_coefficientFormulaVec_le`) bounds `(1 + |c|)^{m+2} ‖γ_G(a,c)‖` by a
constant, depending only on `ρ` and `m`, times the ray-derivative bound
`max_{k ≤ m+2} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖`.  Two of the `m + 2` powers of `1 + |c|` are spent on
the Cauchy weight `(1 + c²)⁻¹`, whose Lebesgue integral is finite, and the remaining `m` powers
combine with `(1 + ‖a‖)^m` into the moment weight `(1 + ‖a‖ + |c|)^m`; Tonelli against
`ν ⊗ dc` then bounds the `m`-th moment of `γ_G λ_α` by `c_ρ M_{m+2}(G)`, which is the manuscript's
`eq:spectral-moments` for `m = 2`.

The second half of the file records the bridge between the two descriptions of the coefficient
measure `Γ = γ λ` used in Section 6: the polar data `polarWeight`, `polarLaw`, `polarDensity` of
the vector measure `λ.withDensityᵥ γ` agree (almost everywhere) with the explicit density data
`densityWeight`, `densityLaw`, `densityPhase` of `γ`, so the Barron bound of Theorem
`thm:lipschitz-barron`, which is stated for a measure of bounded variation, applies verbatim to
the sampled network `densitySampledNetwork` of a coefficient density.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology

open scoped ENNReal NNReal RealInnerProductSpace

/-! ### Moments of the explicit coefficient -/

section Moments

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Two of the `m + 2` powers of `1 + |c|` in the uniform decay bound are traded for the Cauchy
weight `(1 + c²)⁻¹`. -/
theorem enorm_coefficientFormulaVec_mul_pow_le {ρ : SchwartzMap ℝ ℝ} {I : Set ℝ} {G : H → Y}
    {K : ℝ≥0∞} {m : ℕ}
    (hK : ∀ (a : H) (c : ℝ), ENNReal.ofReal ((1 + |c|) ^ (m + 2)) *
      ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤ K * rayDerivBound I G (m + 2) a)
    (a : H) (c : ℝ) :
    ENNReal.ofReal ((1 + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
      K * rayDerivBound I G (m + 2) a * ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
  have hsq : ((1 + |c|) ^ 2)⁻¹ ≤ (1 + c ^ 2)⁻¹ := by
    have h1 : (0 : ℝ) < 1 + c ^ 2 := by positivity
    have h2 : 1 + c ^ 2 ≤ (1 + |c|) ^ 2 := by nlinarith [abs_nonneg c, sq_abs c]
    exact inv_anti₀ h1 h2
  have hmul := mul_le_mul' (hK a c) (le_refl (ENNReal.ofReal (((1 + |c|) ^ 2)⁻¹)))
  have hleft : ENNReal.ofReal ((1 + |c|) ^ (m + 2)) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ *
      ENNReal.ofReal (((1 + |c|) ^ 2)⁻¹) =
      ENNReal.ofReal ((1 + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ := by
    rw [mul_comm (ENNReal.ofReal ((1 + |c|) ^ (m + 2))), mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), mul_comm (‖coefficientFormulaVec ρ G (a, c)‖ₑ)]
    congr 2
    rw [pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  rw [hleft] at hmul
  exact hmul.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hsq))

/-- **The moment bound of Theorem `thm:E`.**  There is a constant, depending only on `ρ`, `I`
and `m`, with `∫ (1 + ‖a‖ + |c|)^m ‖γ_G‖ dλ_α ≤ c M_{m+2}(G)` for every density `G` regular
along rays. -/
theorem exists_const_lintegral_moment_enorm_coefficientFormulaVec_le {ν : Measure H} [SFinite ν]
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I) (m : ℕ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ G : H → Y, IsRegularAlongRays ν I G →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        c * rayMoment ν I G (m + 2) := by
  obtain ⟨K, _, hKtop, hK⟩ :=
    exists_const_forall_enorm_coefficientFormulaVec_le (H := H) (Y := Y) hρ hI (m + 2)
  set Cw : ℝ≥0∞ := ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹) with hCwdef
  have hCwtop : Cw < ⊤ := lintegral_ofReal_inv_one_add_sq_lt_top
  have hne : K * Cw ≠ ⊤ := (ENNReal.mul_lt_top hKtop hCwtop).ne
  refine ⟨K * Cw, hne, fun G hG => ?_⟩
  have hKG := hK G hG.contDiffOn
  have hmeas : Measurable fun θ : H × ℝ => ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) *
      ‖coefficientFormulaVec ρ G θ‖ₑ := by
    refine Measurable.mul ?_
      (stronglyMeasurable_coefficientFormulaVec ρ hG.stronglyMeasurable).enorm
    exact (ENNReal.continuous_ofReal.comp (by fun_prop :
      Continuous fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m)).measurable
  have hpt : ∀ (a : H) (c : ℝ),
      ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
        ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) *
          ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
    intro a c
    have hsplit : ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) ≤
        ENNReal.ofReal ((1 + ‖a‖) ^ m) * ENNReal.ofReal ((1 + |c|) ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ m)
      nlinarith [norm_nonneg a, abs_nonneg c]
    calc ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ
        ≤ ENNReal.ofReal ((1 + ‖a‖) ^ m) *
            (ENNReal.ofReal ((1 + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ) := by
          rw [← mul_assoc]
          exact mul_le_mul' hsplit le_rfl
      _ ≤ ENNReal.ofReal ((1 + ‖a‖) ^ m) *
            (K * rayDerivBound I G (m + 2) a * ENNReal.ofReal ((1 + c ^ 2)⁻¹)) :=
          mul_le_mul' le_rfl (enorm_coefficientFormulaVec_mul_pow_le hKG a c)
      _ = _ := by ring
  have hinner : ∀ a : H, (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
      ‖coefficientFormulaVec ρ G (a, c)‖ₑ) ≤
      K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2 + 2)) * rayDerivBound I G (m + 2) a) := by
    intro a
    have hmono : ENNReal.ofReal ((1 + ‖a‖) ^ m) ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2 + 2)) :=
      ENNReal.ofReal_le_ofReal
        (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg a)) (by omega))
    calc (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
            ‖coefficientFormulaVec ρ G (a, c)‖ₑ)
        ≤ ∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) *
            ENNReal.ofReal ((1 + c ^ 2)⁻¹) := lintegral_mono fun c => hpt a c
      _ = ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) * Cw :=
          lintegral_const_mul _ measurable_ofReal_inv_one_add_sq
      _ ≤ K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2 + 2)) * rayDerivBound I G (m + 2) a) := by
          rw [show ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) * Cw =
              K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ m) * rayDerivBound I G (m + 2) a) from by
                ring]
          exact mul_le_mul' le_rfl (mul_le_mul' hmono le_rfl)
  rw [parameterMeasure, lintegral_prod _ hmeas.aemeasurable]
  calc (∫⁻ a : H, (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
        ‖coefficientFormulaVec ρ G (a, c)‖ₑ) ∂ν)
      ≤ ∫⁻ a : H, K * Cw *
          (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2 + 2)) * rayDerivBound I G (m + 2) a) ∂ν :=
        lintegral_mono hinner
    _ = K * Cw * rayMoment ν I G (m + 2) := lintegral_const_mul' _ _ hne

/-- **Finite moments of all orders.**  For a density regular along rays, the coefficient measure
`γ_G λ_α` has a finite moment of every order. -/
theorem integrable_moment_norm_coefficientFormulaVec {ν : Measure H} [SFinite ν]
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I)
    {G : H → Y} (hG : IsRegularAlongRays ν I G) (m : ℕ) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖)
      (parameterMeasure ν) := by
  obtain ⟨c, hctop, hc⟩ :=
    exists_const_lintegral_moment_enorm_coefficientFormulaVec_le (ν := ν) (Y := Y) hρ hI m
  have hsm : StronglyMeasurable
      (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖) :=
    (Continuous.stronglyMeasurable (by fun_prop)).mul
      (stronglyMeasurable_coefficientFormulaVec ρ hG.stronglyMeasurable).norm
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcongr : ∀ θ : H × ℝ,
      ‖(1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖‖ₑ =
        ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) * ‖coefficientFormulaVec ρ G θ‖ₑ := by
    intro θ
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (by positivity), ofReal_norm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr hcongr)) ?_
  exact lt_of_le_of_lt (hc G hG) (ENNReal.mul_lt_top hctop.lt_top (hG.rayMoment_lt_top (m + 2)))

end Moments

/-! ### The polar decomposition of a coefficient measure with a density -/

section Density

variable {Θ : Type*} [MeasurableSpace Θ]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

omit [NormedSpace ℂ Y] in
/-- The weight `V = ‖γ‖_{L¹(λ)}` of a coefficient density is nonnegative. -/
theorem densityWeight_nonneg (lam : Measure Θ) (γ : Θ → Y) : 0 ≤ densityWeight lam γ :=
  integral_nonneg fun _ => norm_nonneg _

omit [MeasurableSpace Θ] in
/-- The phase `h = γ/‖γ‖` of a coefficient density has norm at most one (norm one where `γ`
does not vanish, and zero where it does). -/
theorem norm_densityPhase_le_one (γ : Θ → Y) (θ : Θ) : ‖densityPhase γ θ‖ ≤ 1 := by
  rcases eq_or_ne (γ θ) 0 with h | h
  · simp [densityPhase, h]
  · rw [densityPhase, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

omit [NormedSpace ℂ Y] in
/-- The total mass `∫ ‖γ‖ₑ dλ` of a coefficient measure with an integrable density is
`V = ‖γ‖_{L¹(λ)}`. -/
theorem lintegral_enorm_eq_ofReal_densityWeight {lam : Measure Θ} {γ : Θ → Y}
    (hγ : Integrable γ lam) :
    ∫⁻ θ, ‖γ θ‖ₑ ∂lam = ENNReal.ofReal (densityWeight lam γ) :=
  (ofReal_integral_norm_eq_lintegral_enorm hγ).symm

omit [NormedSpace ℂ Y] in
/-- The parameter law `p = |γ| λ / V` is absolutely continuous with respect to `λ`. -/
theorem densityLaw_absolutelyContinuous (lam : Measure Θ) (γ : Θ → Y) :
    densityLaw lam γ ≪ lam :=
  Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous lam _)

omit [NormedSpace ℂ Y] in
/-- The parameter law of a coefficient density of zero weight is the zero measure. -/
theorem densityLaw_eq_zero {lam : Measure Θ} {γ : Θ → Y} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ = 0) : densityLaw lam γ = 0 := by
  have h : lam.withDensity (fun θ => ‖γ θ‖ₑ) = 0 := by
    refine Measure.measure_univ_eq_zero.mp ?_
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_enorm_eq_ofReal_densityWeight hγ, hV, ENNReal.ofReal_zero]
  rw [densityLaw, h, smul_zero]

omit [NormedSpace ℂ Y] in
/-- The parameter law of a coefficient density of nonzero weight is a probability measure. -/
theorem isProbabilityMeasure_densityLaw {lam : Measure Θ} {γ : Θ → Y} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ ≠ 0) : IsProbabilityMeasure (densityLaw lam γ) := by
  have hVpos : 0 < densityWeight lam γ :=
    lt_of_le_of_ne (densityWeight_nonneg lam γ) (Ne.symm hV)
  refine ⟨?_⟩
  rw [densityLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_enorm_eq_ofReal_densityWeight hγ,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hVpos).ne' ENNReal.ofReal_ne_top]

/-- **The polar decomposition of a coefficient measure with a density.**
`V ∫ f h dp = ∫ f γ dλ` with `V = ‖γ‖_{L¹(λ)}`, `p = |γ| λ / V` and `h = γ/‖γ‖`. -/
theorem densityWeight_smul_integral_smul_densityPhase [CompleteSpace Y] {lam : Measure Θ}
    {γ : Θ → Y} (hγ : Integrable γ lam) (f : Θ → ℂ) :
    densityWeight lam γ • ∫ θ, f θ • densityPhase γ θ ∂densityLaw lam γ =
      ∫ θ, f θ • γ θ ∂lam := by
  have hpt : ∀ θ : Θ, (‖γ θ‖₊ : ℝ≥0) • (f θ • densityPhase γ θ) = f θ • γ θ := by
    intro θ
    rcases eq_or_ne (γ θ) 0 with h | h
    · simp [densityPhase, h]
    · rw [NNReal.smul_def, densityPhase, smul_comm (f θ) ((‖γ θ‖⁻¹ : ℝ)), smul_smul,
        coe_nnnorm, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
  rcases eq_or_ne (densityWeight lam γ) 0 with hV | hV
  · rw [hV, zero_smul]
    have hzero : ∀ᵐ θ ∂lam, γ θ = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun θ => norm_nonneg (γ θ)) hγ.norm).mp hV
      filter_upwards [h] with θ hθ using norm_eq_zero.mp hθ
    refine ((integral_congr_ae (g := fun _ : Θ => (0 : Y)) ?_).trans (integral_zero _ _)).symm
    filter_upwards [hzero] with θ hθ using by rw [hθ, smul_zero]
  · have hinv : ((ENNReal.ofReal (densityWeight lam γ))⁻¹).toReal = (densityWeight lam γ)⁻¹ := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (densityWeight_nonneg lam γ)]
    have hnn : AEMeasurable (fun θ => ‖γ θ‖₊) lam := hγ.aestronglyMeasurable.nnnorm.aemeasurable
    rw [densityLaw, integral_smul_measure, hinv, smul_smul,
      mul_inv_cancel₀ hV, one_smul]
    have hwd : lam.withDensity (fun θ => ‖γ θ‖ₑ) =
        lam.withDensity fun θ => ((‖γ θ‖₊ : ℝ≥0) : ℝ≥0∞) := by
      simp [enorm_eq_nnnorm]
    rw [hwd, integral_withDensity_eq_integral_smul₀ hnn]
    exact integral_congr_ae (Eventually.of_forall hpt)

omit [NormedSpace ℂ Y] in
/-- **Integrability against the parameter law.**  A function integrable against `|γ| λ` is
integrable against the probability law `p = |γ| λ / V`. -/
theorem integrable_densityLaw_of_integrable_mul {lam : Measure Θ} {γ : Θ → Y}
    (hγ : Integrable γ lam) {f : Θ → ℝ} (hf : AEStronglyMeasurable f lam)
    (hfi : Integrable (fun θ => f θ * ‖γ θ‖) lam) : Integrable f (densityLaw lam γ) := by
  by_cases hV : densityWeight lam γ = 0
  · rw [densityLaw_eq_zero hγ hV]
    exact integrable_zero_measure
  have hg : AEMeasurable (fun θ => ‖γ θ‖ₑ) lam := hγ.aestronglyMeasurable.enorm
  have hwd : Integrable f (lam.withDensity fun θ => ‖γ θ‖ₑ) := by
    refine ⟨hf.mono_ac (withDensity_absolutelyContinuous lam _), ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_withDensity_eq_lintegral_mul₀ hg hf.enorm]
    have hcongr : ∀ θ : Θ, ((fun θ => ‖γ θ‖ₑ) * fun θ => ‖f θ‖ₑ) θ = ‖f θ * ‖γ θ‖‖ₑ := by
      intro θ
      simp only [Pi.mul_apply]
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg (γ θ))]
      congr 1
      rw [norm_mul, norm_norm, mul_comm]
    rw [lintegral_congr hcongr]
    exact hfi.2
  have hVpos : 0 < densityWeight lam γ :=
    lt_of_le_of_ne (densityWeight_nonneg lam γ) (Ne.symm hV)
  have hne : (ENNReal.ofReal (densityWeight lam γ))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hVpos).ne'
  rw [densityLaw]
  exact hwd.smul_measure hne

end Density

/-! ### The parameter law of the coefficient measure -/

section CoefficientLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The explicit coefficient of a density regular along rays is integrable against `λ_α`: the
coefficient measure `γ_G λ_α` has bounded variation. -/
theorem integrable_coefficientFormulaVec {ν : Measure H} [SFinite ν] {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y}
    (hG : IsRegularAlongRays ν I G) :
    Integrable (coefficientFormulaVec ρ G) (parameterMeasure ν) := by
  refine (integrable_norm_iff
    (stronglyMeasurable_coefficientFormulaVec ρ hG.stronglyMeasurable).aestronglyMeasurable).mp ?_
  refine (integrable_moment_norm_coefficientFormulaVec hρ hI hG 0).congr
    (Eventually.of_forall fun θ => ?_)
  show (1 + ‖θ.1‖ + |θ.2|) ^ 0 * ‖coefficientFormulaVec ρ G θ‖ =
    ‖coefficientFormulaVec ρ G θ‖
  rw [pow_zero, one_mul]

/-- The parameter law `p = |γ_G| λ_α / V` of the coefficient measure has a finite second
moment. -/
theorem integrable_sq_densityLaw_coefficientFormulaVec {ν : Measure H} [SFinite ν]
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I)
    {G : H → Y} (hG : IsRegularAlongRays ν I G) :
    Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2)
      (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) := by
  refine integrable_densityLaw_of_integrable_mul (integrable_coefficientFormulaVec hρ hI hG)
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  have hsm : StronglyMeasurable (fun θ : H × ℝ =>
      (‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormulaVec ρ G θ‖) :=
    (Continuous.stronglyMeasurable (by fun_prop)).mul
      (stronglyMeasurable_coefficientFormulaVec ρ hG.stronglyMeasurable).norm
  refine (integrable_moment_norm_coefficientFormulaVec hρ hI hG 2).mono
    hsm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
  have h1 : ‖(‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormulaVec ρ G θ‖‖ =
      (‖θ.1‖ ^ 2 + |θ.2| ^ 2) * ‖coefficientFormulaVec ρ G θ‖ :=
    Real.norm_of_nonneg (by positivity)
  have h2 : ‖(1 + ‖θ.1‖ + |θ.2|) ^ 2 * ‖coefficientFormulaVec ρ G θ‖‖ =
      (1 + ‖θ.1‖ + |θ.2|) ^ 2 * ‖coefficientFormulaVec ρ G θ‖ :=
    Real.norm_of_nonneg (by positivity)
  rw [h1, h2]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  nlinarith [norm_nonneg θ.1, abs_nonneg θ.2]

omit [MeasurableSpace H] [BorelSpace H] in
/-- For a scalar density the `Y`-valued and the scalar explicit coefficients agree as
functions. -/
theorem coefficientFormulaVec_eq_coefficientFormula' (ρ : SchwartzMap ℝ ℝ) (G : H → ℂ) :
    coefficientFormulaVec ρ G = coefficientFormula ρ G :=
  funext fun p => coefficientFormulaVec_eq_coefficientFormula ρ G p

end CoefficientLaw

/-! ### The Barron bound for a coefficient measure with a density -/

section DensityBarron

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] {K : Set H}

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] in
/-- The phase of a coefficient density is measurable for the parameter law. -/
theorem aestronglyMeasurable_densityPhase {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ}
    (hγ : Integrable γ lam) :
    AEStronglyMeasurable (densityPhase γ) (densityLaw lam γ) := by
  have h1 : AEStronglyMeasurable (densityPhase γ) lam :=
    (hγ.aestronglyMeasurable.norm.aemeasurable.inv).aestronglyMeasurable.smul
      hγ.aestronglyMeasurable
  exact h1.mono_ac (densityLaw_absolutelyContinuous lam γ)

/-- The `C(K)`-valued atoms of a coefficient measure with a density are Bochner integrable. -/
theorem integrable_density_atom (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) :
    Integrable (fun θ => densityPhase γ θ • ridgeAtom hK (continuous_ofReal_comp hβ) θ)
      (densityLaw lam γ) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  exact integrable_smul_ridgeAtom hK hβ (densityLaw lam γ) measurable_id
    (aestronglyMeasurable_densityPhase hγ)
    (Eventually.of_forall fun θ => norm_densityPhase_le_one γ θ) hM

omit [BorelSpace H] in
/-- The integral network of a coefficient measure with a density, written through its polar
decomposition. -/
theorem integralNetworkDensity_eq_smul_integral (β : ℝ → ℂ) {lam : Measure (H × ℝ)}
    {γ : H × ℝ → ℂ} (hγ : Integrable γ lam) (x : H) :
    integralNetworkDensity β lam γ x =
      densityWeight lam γ • ∫ θ, β (⟪θ.1, x⟫ + θ.2) • densityPhase γ θ ∂densityLaw lam γ :=
  (densityWeight_smul_integral_smul_densityPhase hγ fun θ => β (⟪θ.1, x⟫ + θ.2)).symm

/-- The error of the sampled network of a coefficient density on `K`, as `V/N` times the
`C(K)`-norm of the centred sum of the atoms. -/
theorem compactSupNorm_densitySampledNetwork_sub_eq (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) :
    compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x) =
      densityWeight lam γ / N *
        ‖∑ j, densityPhase γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
          (N : ℝ) • ∫ θ', densityPhase γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
            ∂densityLaw lam γ‖ := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  calc compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
      = compactSupNorm K (fun x =>
          ∑ j, (β (⟪(id (θ j)).1, x⟫ + (id (θ j)).2) : ℂ) •
              (((densityWeight lam γ / N : ℝ) : ℂ) • densityPhase γ (θ j)) -
            densityWeight lam γ • ∫ θ', (β (⟪(id θ').1, x⟫ + (id θ').2) : ℂ) •
              densityPhase γ θ' ∂densityLaw lam γ) := by
        refine compactSupNorm_congr fun x _ => ?_
        rw [integralNetworkDensity_eq_smul_integral (fun t => (β t : ℂ)) hγ x]
        simp only [densitySampledNetwork, sampledNetwork, finiteNetwork, id]
    _ = _ := compactSupNorm_sampled_sub_eq (densityLaw lam γ) (fun t => (β t : ℂ)) id
        (densityPhase γ) (smul_ridgeAtom_apply hK (continuous_ofReal_comp hβ) id
          (densityPhase γ)) (integrable_density_atom hK hβ hγ hV hM)
        (densityWeight_nonneg lam γ) hN θ

/-- The error of the sampled network of a coefficient density at a point of `K` is bounded by
its compact sup norm. -/
theorem norm_densitySampledNetwork_sub_le_compactSupNorm (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ}
    (hγ : Integrable γ lam) (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) {x : H} (hx : x ∈ K) :
    ‖densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
        integralNetworkDensity (fun t => (β t : ℂ)) lam γ x‖ ≤
      compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  have hΦint := integrable_density_atom hK hβ hγ hV hM
  refine le_compactSupNorm_of_forall (g := fun x =>
      densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
        integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
    ((densityWeight lam γ / N : ℝ) •
      (∑ j, densityPhase γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
        (N : ℝ) • ∫ θ', densityPhase γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
          ∂densityLaw lam γ))
    (fun y => ?_) hx
  refine (smul_sum_sub_apply (densityLaw lam γ) (fun t => (β t : ℂ)) id (densityPhase γ)
    (smul_ridgeAtom_apply hK (continuous_ofReal_comp hβ) id (densityPhase γ)) hΦint
    (densityWeight lam γ) hN θ y).trans ?_
  rw [integralNetworkDensity_eq_smul_integral (fun t => (β t : ℂ)) hγ (y : H)]
  simp only [densitySampledNetwork, sampledNetwork, finiteNetwork, id]

/-- **The Barron bound for a coefficient measure with a density.**  The mean compact-open error
of the sampled network of `γ λ` is at most `(8V/√N)(|β(0)| + Lip(β) R_K M₂)`. -/
theorem integral_compactSupNorm_densitySampledNetwork_sub_le (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ}
    (hγ : Integrable γ lam)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
            integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
        ∂sampleLaw N (densityLaw lam γ) ≤
      8 * densityWeight lam γ / Real.sqrt N *
        (|β 0| + (L : ℝ) * compactRadius K * Real.sqrt (secondMoment (densityLaw lam γ))) := by
  by_cases hV : densityWeight lam γ = 0
  · rw [densityLaw_eq_zero hγ hV, sampleLaw_zero hN, integral_zero_measure, hV]
    simp
  haveI := isProbabilityMeasure_densityLaw hγ hV
  have hsqrt : Real.sqrt N / N = 1 / Real.sqrt N := Real.sqrt_div_self'
  calc ∫ θ, compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
            integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
        ∂sampleLaw N (densityLaw lam γ)
      = ∫ θ, densityWeight lam γ / N *
          ‖∑ j, densityPhase γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
            (N : ℝ) • ∫ θ', densityPhase γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
              ∂densityLaw lam γ‖
          ∂sampleLaw N (densityLaw lam γ) :=
        integral_congr_ae (Eventually.of_forall
          (compactSupNorm_densitySampledNetwork_sub_eq hK hβ hγ hV hM hN))
    _ = densityWeight lam γ / N * ∫ θ,
          ‖∑ j, densityPhase γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
            (N : ℝ) • ∫ θ', densityPhase γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
              ∂densityLaw lam γ‖
          ∂sampleLaw N (densityLaw lam γ) := integral_const_mul _ _
    _ ≤ densityWeight lam γ / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
          Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂densityLaw lam γ))) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_sum_smul_ridgeAtom_sub_le hK hβ (densityLaw lam γ) measurable_id
            (aestronglyMeasurable_densityPhase hγ)
            (Eventually.of_forall fun θ => norm_densityPhase_le_one γ θ) hM N)
          (div_nonneg (densityWeight_nonneg lam γ) (Nat.cast_nonneg N))
    _ = 8 * densityWeight lam γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K *
            Real.sqrt (secondMoment (densityLaw lam γ))) := by
        rw [secondMoment]
        calc densityWeight lam γ / N * (8 * Real.sqrt N * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂densityLaw lam γ)))
            = 8 * densityWeight lam γ * (|β 0| + L * compactRadius K *
                Real.sqrt (∫ θ, (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂densityLaw lam γ)) *
                  (Real.sqrt N / N) := by ring
          _ = _ := by rw [hsqrt]; ring

/-- The compact-open error of the sampled network of a coefficient density is an integrable
function of the sample. -/
theorem integrable_compactSupNorm_densitySampledNetwork_sub (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ}
    (hγ : Integrable γ lam) (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) :
    Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x))
      (sampleLaw N (densityLaw lam γ)) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  exact ((integrable_norm_sum_sub (densityLaw lam γ) (integrable_density_atom hK hβ hγ hV hM)
    N).const_mul (densityWeight lam γ / N)).congr (Eventually.of_forall fun θ =>
      (compactSupNorm_densitySampledNetwork_sub_eq hK hβ hγ hV hM hN θ).symm)

/-- **A deterministic realization of the Barron bound** for a coefficient measure with a
density. -/
theorem exists_compactSupNorm_densitySampledNetwork_sub_le (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → ℂ}
    (hγ : Integrable γ lam)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) :
    ∃ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
            integralNetworkDensity (fun t => (β t : ℂ)) lam γ x) ≤
        8 * densityWeight lam γ / Real.sqrt N *
          (|β 0| + (L : ℝ) * compactRadius K *
            Real.sqrt (secondMoment (densityLaw lam γ))) := by
  by_cases hV : densityWeight lam γ = 0
  · refine ⟨fun _ => (0, 0), ?_⟩
    rw [hV]
    refine le_of_le_of_eq (compactSupNorm_le le_rfl fun x _ => ?_) (by simp)
    have hzero : ∀ᵐ θ ∂lam, γ θ = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun θ => norm_nonneg (γ θ)) hγ.norm).mp hV
      filter_upwards [h] with θ hθ using norm_eq_zero.mp hθ
    have h1 : integralNetworkDensity (fun t => (β t : ℂ)) lam γ x = 0 := by
      refine (integral_congr_ae (g := fun _ : H × ℝ => (0 : ℂ)) ?_).trans (integral_zero _ _)
      filter_upwards [hzero] with θ hθ using by rw [hθ, smul_zero]
    have h2 : densitySampledNetwork (fun t => (β t : ℂ)) lam γ
        (fun _ : Fin N => ((0 : H), (0 : ℝ))) x = 0 := by
      simp [densitySampledNetwork, sampledNetwork, finiteNetwork, hV]
    rw [h1, h2, sub_zero, norm_zero]
  haveI := isProbabilityMeasure_densityLaw hγ hV
  have hint := integrable_compactSupNorm_densitySampledNetwork_sub hK hβ hγ hV hM hN
  obtain ⟨θ, hθ⟩ := exists_realization_le_mean _ _ hint
  exact ⟨θ, hθ.trans (integral_compactSupNorm_densitySampledNetwork_sub_le hK hβ hγ hM hN)⟩

end DensityBarron

end OperatorRidgelet
