import OperatorRidgelet.Sobolev.Pairing
import OperatorRidgelet.Sobolev.Uniqueness
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Network.Defs
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Absolute synthesis from weak Sobolev regularity along rays

The material behind Theorem `thm:weak-sobolev-synthesis`: the moment bound of the coefficient,
its finite variation, and the synthesis identity.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Homogeneity as a change of variables: `∫ F(-ωa) dν(a) = |ω|^{-α} ∫ F dν` for `ω ≠ 0`. -/
theorem IsHomogeneous.integral_comp_neg_smul {α : ℝ} {ν : Measure H} (hν : IsHomogeneous α ν)
    {F : H → Y} (hF : StronglyMeasurable F) {ω : ℝ} (hω : ω ≠ 0) :
    ∫ a : H, F (-(ω • a)) ∂ν = ((|ω| ^ (-α) : ℝ)) • ∫ ξ : H, F ξ ∂ν := by
  have hfun : (fun a : H => F (-(ω • a))) = fun a => F ((-ω) • a) := by
    funext a
    rw [neg_smul]
  rw [hfun, ← integral_map (measurable_const_smul (-ω)).aemeasurable hF.aestronglyMeasurable,
    hν (-ω) (neg_ne_zero.mpr hω), integral_smul_measure, abs_neg,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg ω) _)]

/-! ### The moment bound -/

/-- `1 + ‖a‖ + |b| ≤ √2 (1 + ‖a‖) ⟨b⟩`. -/
theorem one_add_add_abs_le (c b : ℝ) (hc : 1 ≤ c) :
    c + |b| ≤ Real.sqrt 2 * (c * bracket b) := by
  have h1 : 1 + |b| ≤ Real.sqrt 2 * bracket b := one_add_abs_le_sqrt_two_mul_bracket b
  have hb : 0 ≤ bracket b := (bracket_pos b).le
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [abs_nonneg b, one_le_bracket b]

/-- The per-ray moment bound of Theorem `thm:weak-sobolev-synthesis`. -/
theorem lintegral_ray_moment_le {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s) (c : ℝ)
    (hc : 1 ≤ c) {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    ∫⁻ b : ℝ, ENNReal.ofReal ((c + |b|) ^ r * ‖γ b‖) ≤
      ENNReal.ofReal (Real.sqrt 2 ^ r * sobolevMomentConst s r * (c ^ s * raySobolevNorm s γ)) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hint := integrable_bracket_rpow_norm hr0 hrs hγ
  have hpt : ∀ b : ℝ, (c + |b|) ^ r * ‖γ b‖ ≤
      (Real.sqrt 2 ^ r * c ^ s) * ((bracket b ^ r : ℝ) * ‖γ b‖) := by
    intro b
    have h1 : ((c + |b|) ^ r : ℝ) ≤ (Real.sqrt 2 * (c * bracket b)) ^ r :=
      Real.rpow_le_rpow (by positivity) (one_add_add_abs_le c b hc) hr0
    have h2 : ((Real.sqrt 2 * (c * bracket b)) ^ r : ℝ) =
        Real.sqrt 2 ^ r * (c ^ r * bracket b ^ r) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg 2) (mul_nonneg hc0.le (bracket_pos b).le),
        Real.mul_rpow hc0.le (bracket_pos b).le]
    have h3 : (c ^ r : ℝ) ≤ c ^ s := Real.rpow_le_rpow_of_exponent_le hc (by linarith)
    have h4 : ((c + |b|) ^ r : ℝ) ≤ Real.sqrt 2 ^ r * (c ^ s * bracket b ^ r) := by
      refine h1.trans (le_of_eq_of_le h2 ?_)
      have hs2 : (0 : ℝ) ≤ Real.sqrt 2 ^ r := Real.rpow_nonneg (Real.sqrt_nonneg 2) r
      have hbr : (0 : ℝ) ≤ bracket b ^ r := Real.rpow_nonneg (bracket_pos b).le r
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hbr) hs2
    calc (c + |b|) ^ r * ‖γ b‖
        ≤ (Real.sqrt 2 ^ r * (c ^ s * bracket b ^ r)) * ‖γ b‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      _ = (Real.sqrt 2 ^ r * c ^ s) * ((bracket b ^ r : ℝ) * ‖γ b‖) := by ring
  have hbound := integral_bracket_rpow_norm_le hr0 hrs hγ
  have hconst : (0 : ℝ) ≤ Real.sqrt 2 ^ r * c ^ s :=
    mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg 2) r) (Real.rpow_nonneg hc0.le s)
  calc ∫⁻ b : ℝ, ENNReal.ofReal ((c + |b|) ^ r * ‖γ b‖)
      ≤ ∫⁻ b : ℝ, ENNReal.ofReal ((Real.sqrt 2 ^ r * c ^ s) *
          ((bracket b ^ r : ℝ) * ‖γ b‖)) :=
        lintegral_mono fun b => ENNReal.ofReal_le_ofReal (hpt b)
    _ = ENNReal.ofReal (Real.sqrt 2 ^ r * c ^ s) *
          ∫⁻ b : ℝ, ENNReal.ofReal ((bracket b ^ r : ℝ) * ‖γ b‖) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun b => by
          rw [← ENNReal.ofReal_mul hconst]
    _ = ENNReal.ofReal (Real.sqrt 2 ^ r * c ^ s) *
          ENNReal.ofReal (∫ b : ℝ, (bracket b ^ r : ℝ) * ‖γ b‖) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun b =>
            mul_nonneg (Real.rpow_nonneg (bracket_pos b).le r) (norm_nonneg _))]
    _ ≤ ENNReal.ofReal (Real.sqrt 2 ^ r * c ^ s) *
          ENNReal.ofReal (sobolevMomentConst s r * raySobolevNorm s γ) := by
        exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal hbound) _
    _ = ENNReal.ofReal (Real.sqrt 2 ^ r * sobolevMomentConst s r *
          (c ^ s * raySobolevNorm s γ)) := by
        rw [← ENNReal.ofReal_mul hconst]
        congr 1
        ring

/-- **The moment bound** `eq:sobolev-moments` of Theorem `thm:weak-sobolev-synthesis`. -/
theorem lintegral_prod_moment_le {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b)) :
    ∫⁻ p : H × ℝ, ENNReal.ofReal ((1 + ‖p.1‖ + |p.2|) ^ r * ‖γ p‖) ∂(ν.prod volume) ≤
      ENNReal.ofReal (Real.sqrt 2 ^ r * sobolevMomentConst s r) *
        ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν := by
  have hK : (0 : ℝ) ≤ Real.sqrt 2 ^ r * sobolevMomentConst s r :=
    mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg 2) r) (by
      rw [sobolevMomentConst]
      positivity)
  have hmeas : Measurable fun p : H × ℝ =>
      ENNReal.ofReal ((1 + ‖p.1‖ + |p.2|) ^ r * ‖γ p‖) := by
    have hcont : Continuous fun p : H × ℝ => ((1 + ‖p.1‖ + |p.2|) ^ r : ℝ) := by
      refine Continuous.rpow_const ?_ fun p => Or.inr hr0
      fun_prop
    exact ENNReal.measurable_ofReal.comp (hcont.measurable.mul hγm.norm.measurable)
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc ∫⁻ a : H, ∫⁻ b : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |b|) ^ r * ‖γ (a, b)‖) ∂volume ∂ν
      ≤ ∫⁻ a : H, ENNReal.ofReal (Real.sqrt 2 ^ r * sobolevMomentConst s r *
          ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b))) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hray] with a ha
        have h1 : (1 : ℝ) ≤ 1 + ‖a‖ := by simp [norm_nonneg]
        exact lintegral_ray_moment_le hr0 hrs (1 + ‖a‖) h1 ha
    _ = ENNReal.ofReal (Real.sqrt 2 ^ r * sobolevMomentConst s r) *
          ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun a => by rw [← ENNReal.ofReal_mul hK]

/-- The moment integrand is integrable. -/
theorem integrable_moment {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s) {ν : Measure H}
    [SFinite ν] {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Integrable (fun q : H × ℝ => (1 + ‖q.1‖ + |q.2|) ^ r * ‖γ q‖) (ν.prod volume) := by
  have hcont : Continuous fun q : H × ℝ => ((1 + ‖q.1‖ + |q.2|) ^ r : ℝ) := by
    refine Continuous.rpow_const ?_ fun p => Or.inr hr0
    fun_prop
  refine ⟨(hcont.aestronglyMeasurable.mul hγm.norm.aestronglyMeasurable), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnn : ∀ q : H × ℝ, ‖(1 + ‖q.1‖ + |q.2|) ^ r * ‖γ q‖‖ₑ =
      ENNReal.ofReal ((1 + ‖q.1‖ + |q.2|) ^ r * ‖γ q‖) := by
    intro q
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) r) (norm_nonneg _))]
  rw [lintegral_congr hnn]
  exact lt_of_le_of_lt (lintegral_prod_moment_le hr0 hrs hγm hray)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hB))

/-- **Finite variation** of the coefficient measure. -/
theorem integrable_coefficient {s : ℝ} (hs : 1 / 2 < s) {ν : Measure H} [SFinite ν]
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Integrable γ (ν.prod volume) := by
  have h := integrable_moment (r := 0) le_rfl (by linarith) hγm hray hB
  refine ⟨hγm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hfin := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun q => ?_)) hfin
  rw [Real.rpow_zero, one_mul, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-! ### Absolute convergence of the synthesis -/

/-- The affine bias bound `1 + |⟪a, x⟫ - b| ≤ max 1 ‖x‖ (1 + ‖a‖ + |b|)`. -/
theorem one_add_abs_inner_sub_le (a x : H) (b : ℝ) :
    1 + |⟪a, x⟫ - b| ≤ max 1 ‖x‖ * (1 + ‖a‖ + |b|) := by
  have h1 : |⟪a, x⟫ - b| ≤ ‖a‖ * ‖x‖ + |b| :=
    (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm a x) le_rfl)
  have hx : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
  have h1m : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hb : (0 : ℝ) ≤ |b| := abs_nonneg b
  nlinarith [mul_le_mul_of_nonneg_left hx ha]

/-- The synthesis integrand is dominated by the moment integrand. -/
theorem norm_smul_le_moment {p Cσ : ℝ} (hp : 0 ≤ p) {σ : ℝ → ℂ}
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) (x : H) (γ : H × ℝ → Y) (q : H × ℝ) :
    ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ ≤
      (Cσ * max 1 ‖x‖ ^ p) * ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖) := by
  have hC : 0 ≤ Cσ := by
    have h := hσg 0
    simpa using le_trans (norm_nonneg (σ 0)) h
  have hmax : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  have hb := one_add_abs_inner_sub_le q.1 x q.2
  have h1 : ((1 + |⟪q.1, x⟫ - q.2|) ^ p : ℝ) ≤
      (max 1 ‖x‖ * (1 + ‖q.1‖ + |q.2|)) ^ p := Real.rpow_le_rpow (by positivity) hb hp
  have h2 : ((max 1 ‖x‖ * (1 + ‖q.1‖ + |q.2|)) ^ p : ℝ) =
      max 1 ‖x‖ ^ p * (1 + ‖q.1‖ + |q.2|) ^ p :=
    Real.mul_rpow (by positivity) (by positivity)
  rw [norm_smul]
  calc ‖σ (⟪q.1, x⟫ - q.2)‖ * ‖γ q‖
      ≤ (Cσ * (1 + |⟪q.1, x⟫ - q.2|) ^ p) * ‖γ q‖ :=
        mul_le_mul_of_nonneg_right (hσg _) (norm_nonneg _)
    _ ≤ (Cσ * (max 1 ‖x‖ ^ p * (1 + ‖q.1‖ + |q.2|) ^ p)) * ‖γ q‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) hC
    _ = (Cσ * max 1 ‖x‖ ^ p) * ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖) := by ring

/-- The synthesis integral converges absolutely. -/
theorem integrable_synthesis {s p Cσ : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    (x : H) :
    Integrable (fun q : H × ℝ => σ (⟪q.1, x⟫ - q.2) • γ q) (ν.prod volume) := by
  have hC : 0 ≤ Cσ * max 1 ‖x‖ ^ p := by
    have h := hσg 0
    have hC0 : 0 ≤ Cσ := by simpa using le_trans (norm_nonneg (σ 0)) h
    positivity
  have hmeas : AEStronglyMeasurable (fun q : H × ℝ => σ (⟪q.1, x⟫ - q.2) • γ q)
      (ν.prod volume) := by
    have h1 : Continuous fun q : H × ℝ => σ (⟪q.1, x⟫ - q.2) :=
      hσc.comp (by fun_prop)
    exact h1.aestronglyMeasurable.smul hγm.aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hdom : ∫⁻ q : H × ℝ, ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ₑ ∂(ν.prod volume) ≤
      ENNReal.ofReal (Cσ * max 1 ‖x‖ ^ p) *
        ∫⁻ q : H × ℝ, ENNReal.ofReal ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖) ∂(ν.prod volume) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun q => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (norm_smul_le_moment hp hσg x γ q)
  refine lt_of_le_of_lt hdom (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  refine lt_of_le_of_lt (lintegral_prod_moment_le hp hps hγm hray) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hB)

/-! ### The bias shift on the product -/

/-- The fibrewise bias reflection `b ↦ ⟪a, x⟫ - b` preserves the lower integral on the
product. -/
theorem lintegral_prod_shift {ν : Measure H} [SFinite ν] (f : H × ℝ → ℝ≥0∞) (hf : Measurable f)
    (x : H) :
    ∫⁻ q : H × ℝ, f (q.1, ⟪q.1, x⟫ - q.2) ∂(ν.prod volume) =
      ∫⁻ q : H × ℝ, f q ∂(ν.prod volume) := by
  have hshift : Measurable fun q : H × ℝ => f (q.1, ⟪q.1, x⟫ - q.2) :=
    hf.comp (measurable_fst.prodMk (by fun_prop : Measurable fun q : H × ℝ => ⟪q.1, x⟫ - q.2))
  rw [lintegral_prod _ hshift.aemeasurable, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun a => ?_
  exact lintegral_sub_left_eq_self (fun b : ℝ => f (a, b)) ⟪a, x⟫

/-- The shifted coefficient is integrable on the product. -/
theorem integrable_shift {s : ℝ} (hs : 1 / 2 < s) {ν : Measure H} [SFinite ν]
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    (x : H) :
    Integrable (fun q : H × ℝ => γ (q.1, ⟪q.1, x⟫ - q.2)) (ν.prod volume) := by
  have hmeas : StronglyMeasurable fun q : H × ℝ => γ (q.1, ⟪q.1, x⟫ - q.2) :=
    hγm.comp_measurable
      (measurable_fst.prodMk (by fun_prop : Measurable fun q : H × ℝ => ⟪q.1, x⟫ - q.2))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsub := lintegral_prod_shift (ν := ν) (fun q => ‖γ q‖ₑ) hγm.enorm x
  rw [hsub]
  have hmom := lintegral_prod_moment_le (r := 0) le_rfl (by linarith) hγm hray
  have hzero : ∫⁻ q : H × ℝ, ENNReal.ofReal ((1 + ‖q.1‖ + |q.2|) ^ (0 : ℝ) * ‖γ q‖)
      ∂(ν.prod volume) = ∫⁻ q : H × ℝ, ‖γ q‖ₑ ∂(ν.prod volume) := by
    refine lintegral_congr fun q => ?_
    rw [Real.rpow_zero, one_mul, ofReal_norm]
  rw [hzero] at hmom
  exact lt_of_le_of_lt hmom
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hB))

/-! ### The averaged coefficient -/

/-- The average of the shifted coefficient over the directions is integrable. -/
theorem integrable_avg {s : ℝ} (hs : 1 / 2 < s) {ν : Measure H} [SFinite ν]
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    (x : H) :
    Integrable (fun t : ℝ => ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν) volume :=
  ((integrable_shift hs hγm hray hB x).swap).integral_prod_left

/-- The profile of the averaged coefficient, at a nonzero frequency. -/
theorem rayProfile_avg {s α : ℝ} (hs : 1 / 2 < s) {ν : Measure H} [SFinite ν]
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} {g : H → Y} (hgm : StronglyMeasurable g)
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hprofile : ∀ᵐ a ∂ν, ∀ ω : ℝ,
      rayProfile (fun b => γ (a, b)) ω = filterFourier ρ (-ω) • g (ω • a))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    (x : H) {ω : ℝ} (hω : ω ≠ 0) :
    rayProfile (fun t : ℝ => ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν) ω =
      filterFourier ρ ω • (((|ω| ^ (-α) : ℝ)) • spectralTarget ν g x) := by
  have hshift := integrable_shift hs hγm hray hB x
  have hprodint : Integrable
      (Function.uncurry fun (a : H) (t : ℝ) =>
        Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t)) (ν.prod volume) := by
    refine hshift.mono ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact ((by fun_prop : Continuous fun q : H × ℝ =>
        Complex.exp ((-(ω * q.2) : ℝ) * Complex.I)).aestronglyMeasurable).smul
        hshift.aestronglyMeasurable
    · exact le_of_eq (norm_exp_smul ω q.2 _)
  have hray' : ∀ a : H, (∫ t : ℝ,
      Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t)) =
      Complex.exp ((-(ω * ⟪a, x⟫) : ℝ) * Complex.I) • rayProfile (fun b => γ (a, b)) (-ω) := by
    intro a
    have hF := integral_sub_left_eq_self (fun b : ℝ =>
      Complex.exp ((-(ω * (⟪a, x⟫ - b)) : ℝ) * Complex.I) • γ (a, b)) volume ⟪a, x⟫
    have hL : (∫ t : ℝ, Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t)) =
        ∫ t : ℝ, (fun b : ℝ => Complex.exp ((-(ω * (⟪a, x⟫ - b)) : ℝ) * Complex.I) • γ (a, b))
          (⟪a, x⟫ - t) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [sub_sub_cancel]
    rw [hL, hF, rayProfile, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only
    rw [smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hprofile' : ∀ᵐ a ∂ν,
      (∫ t : ℝ, Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t)) =
        filterFourier ρ ω • (Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) • g (-(ω • a))) := by
    filter_upwards [hprofile] with a ha
    have hexp : ((-(ω * ⟪a, x⟫) : ℝ) : ℂ) = ((⟪x, -(ω • a)⟫ : ℝ) : ℂ) := by
      congr 1
      rw [inner_neg_right, real_inner_smul_right, real_inner_comm]
    rw [hray' a, ha (-ω), neg_neg, neg_smul, smul_comm, hexp]
  have hF : StronglyMeasurable fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • g ξ := by
    refine StronglyMeasurable.smul ?_ hgm
    exact (by fun_prop : Continuous fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).stronglyMeasurable
  calc rayProfile (fun t : ℝ => ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν) ω
      = ∫ t : ℝ, (∫ a : H, Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t) ∂ν) := by
        rw [rayProfile]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => (integral_smul _ _).symm)
    _ = ∫ a : H, (∫ t : ℝ,
          Complex.exp ((-(ω * t) : ℝ) * Complex.I) • γ (a, ⟪a, x⟫ - t)) ∂ν :=
        (integral_integral_swap hprodint).symm
    _ = ∫ a : H, filterFourier ρ ω •
          (Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) • g (-(ω • a))) ∂ν :=
        integral_congr_ae hprofile'
    _ = filterFourier ρ ω • ∫ a : H,
          Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) • g (-(ω • a)) ∂ν := integral_smul _ _
    _ = filterFourier ρ ω • (((|ω| ^ (-α) : ℝ)) • spectralTarget ν g x) := by
        rw [spectralTarget, ← hν.integral_comp_neg_smul hF hω]

/-- The synthesis integral as an integral of the averaged coefficient against the activation. -/
theorem integral_synthesis_eq {s p Cσ : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) =
      ∫ t : ℝ, σ t • ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν := by
  have hsyn := integrable_synthesis hp hps hσc hσg hγm hray hB x
  have hshiftm : StronglyMeasurable fun q : H × ℝ => σ q.2 • γ (q.1, ⟪q.1, x⟫ - q.2) := by
    refine StronglyMeasurable.smul ?_ ?_
    · exact (hσc.comp (by fun_prop : Continuous fun q : H × ℝ => q.2)).stronglyMeasurable
    · exact hγm.comp_measurable
        (measurable_fst.prodMk (by fun_prop : Measurable fun q : H × ℝ => ⟪q.1, x⟫ - q.2))
  have hσshift : Integrable
      (Function.uncurry fun (a : H) (t : ℝ) => σ t • γ (a, ⟪a, x⟫ - t)) (ν.prod volume) := by
    refine ⟨hshiftm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hfm : Measurable fun q : H × ℝ => ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ₑ := by
      refine (StronglyMeasurable.smul ?_ hγm).enorm
      exact (hσc.comp (by fun_prop : Continuous fun q : H × ℝ => ⟪q.1, x⟫ - q.2)).stronglyMeasurable
    have heq : ∀ q : H × ℝ, ‖σ q.2 • γ (q.1, ⟪q.1, x⟫ - q.2)‖ₑ =
        (fun q : H × ℝ => ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ₑ) (q.1, ⟪q.1, x⟫ - q.2) := by
      intro q
      simp only [sub_sub_cancel]
    have hfin := hsyn.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    calc ∫⁻ q : H × ℝ, ‖σ q.2 • γ (q.1, ⟪q.1, x⟫ - q.2)‖ₑ ∂(ν.prod volume)
        = ∫⁻ q : H × ℝ, (fun q : H × ℝ => ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ₑ)
            (q.1, ⟪q.1, x⟫ - q.2) ∂(ν.prod volume) := lintegral_congr heq
      _ = ∫⁻ q : H × ℝ, ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ₑ ∂(ν.prod volume) :=
          lintegral_prod_shift _ hfm x
      _ < ⊤ := hfin
  have hray' : ∀ a : H, (∫ b : ℝ, σ (⟪a, x⟫ - b) • γ (a, b)) =
      ∫ t : ℝ, σ t • γ (a, ⟪a, x⟫ - t) := by
    intro a
    have hF := integral_sub_left_eq_self
      (fun b : ℝ => σ (⟪a, x⟫ - b) • γ (a, b)) volume ⟪a, x⟫
    rw [← hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [sub_sub_cancel]
  calc ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume)
      = ∫ a : H, (∫ b : ℝ, σ (⟪a, x⟫ - b) • γ (a, b)) ∂ν := integral_prod _ hsyn
    _ = ∫ a : H, (∫ t : ℝ, σ t • γ (a, ⟪a, x⟫ - t)) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hray')
    _ = ∫ t : ℝ, (∫ a : H, σ t • γ (a, ⟪a, x⟫ - t) ∂ν) := integral_integral_swap hσshift
    _ = ∫ t : ℝ, σ t • ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => integral_smul _ _)

/-! ### The synthesis identity -/

/-- **The synthesis identity** `eq:weak-sobolev-synthesis` of Theorem
`thm:weak-sobolev-synthesis`. -/
theorem integral_synthesis_eq_pairing_smul {s p α Cσ : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ}
    {g : H → Y} (hgm : StronglyMeasurable g) {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hprofile : ∀ᵐ a ∂ν, ∀ ω : ℝ,
      rayProfile (fun b => γ (a, b)) ω = filterFourier ρ (-ω) • g (ω • a))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    {γq : ℝ → ℂ} (hγq : MemRaySobolev s γq)
    (hqprofile : ∀ ω : ℝ, rayProfile γq ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ))
    (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) =
      sobolevPairing σ γq • spectralTarget ν g x := by
  have hs : 1 / 2 < s := by linarith
  set f : Y := spectralTarget ν g x with hfdef
  set Ψ : ℝ → Y := fun t => ∫ a : H, γ (a, ⟪a, x⟫ - t) ∂ν with hΨdef
  set Θ : ℝ → Y := fun t => γq (-t) • f with hΘdef
  have hΨint : Integrable Ψ volume := integrable_avg hs hγm hray hB x
  have hqint : Integrable γq volume := integrable_of_memRaySobolev hs hγq
  have hqneg : Integrable (fun t : ℝ => γq (-t)) volume :=
    MeasureTheory.Integrable.comp_neg hqint
  have hΘint : Integrable Θ volume := hqneg.smul_const f
  -- the two profiles agree off the origin
  have hprof : ∀ ω : ℝ, ω ≠ 0 → rayProfile Ψ ω = rayProfile Θ ω := by
    intro ω hω
    have h1 := rayProfile_avg hs hν hgm hγm hray hprofile hB x hω
    have h2 : rayProfile Θ ω = rayProfile γq (-ω) • f := by
      rw [← rayProfile_neg γq ω, hΘdef, rayProfile, rayProfile, ← integral_smul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [smul_smul, smul_eq_mul]
    rw [h1, h2, hqprofile (-ω), neg_neg, abs_neg, ← Complex.coe_smul, smul_smul]
  -- both profiles are continuous, so they agree everywhere
  have hprofall : ∀ ω : ℝ, rayProfile Ψ ω = rayProfile Θ ω := by
    have hd : Dense ({(0 : ℝ)}ᶜ : Set ℝ) := dense_compl_singleton 0
    have heq : Set.EqOn (rayProfile Ψ) (rayProfile Θ) ({(0 : ℝ)}ᶜ : Set ℝ) := fun ω hω =>
      hprof ω (by simpa using hω)
    have := Continuous.ext_on hd (continuous_rayProfile hΨint) (continuous_rayProfile hΘint) heq
    exact congrFun this
  have hae : Ψ =ᵐ[volume] Θ := ae_eq_of_rayProfile_eq hΨint hΘint hprofall
  calc ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume)
      = ∫ t : ℝ, σ t • Ψ t := integral_synthesis_eq hp hps hσc hσg hγm hray hB x
    _ = ∫ t : ℝ, σ t • Θ t := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with t ht
        rw [ht]
    _ = ∫ t : ℝ, (σ t * γq (-t)) • f := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        rw [hΘdef]
        simp only
        rw [smul_smul]
    _ = (∫ t : ℝ, σ t * γq (-t)) • f := integral_smul_const _ _
    _ = sobolevPairing σ γq • f := by
        rw [sobolevPairing]
        congr 1

/-! ### Uniform absolute convergence and continuity -/

/-- The synthesis integrand is dominated, uniformly over a ball of inputs, by an integrable
moment majorant. -/
theorem norm_synthesis_le_majorant {p Cσ R : ℝ} (hp : 0 ≤ p) {σ : ℝ → ℂ}
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {x : H} (hx : ‖x‖ ≤ R) (γ : H × ℝ → Y)
    (q : H × ℝ) :
    ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ ≤
      Cσ * max 1 R ^ p * ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖) := by
  have hC : 0 ≤ Cσ := by
    have h := hσg 0
    simpa using le_trans (norm_nonneg (σ 0)) h
  have hmono : (max 1 ‖x‖ : ℝ) ^ p ≤ max 1 R ^ p :=
    Real.rpow_le_rpow (by positivity) (max_le_max le_rfl hx) hp
  refine (norm_smul_le_moment hp hσg x γ q).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hC) ?_
  exact mul_nonneg (Real.rpow_nonneg (by positivity) p) (norm_nonneg _)

/-- The synthesis is continuous in the input. -/
theorem continuous_synthesis {s p Cσ : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Continuous fun x : H => ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) := by
  have hmom := integrable_moment hp hps hγm hray hB
  have hC : 0 ≤ Cσ := by
    have h := hσg 0
    simpa using le_trans (norm_nonneg (σ 0)) h
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  set R : ℝ := ‖x₀‖ + 1 with hR
  refine continuousAt_of_dominated (bound := fun q : H × ℝ =>
    Cσ * max 1 R ^ p * ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖)) ?_ ?_ ?_ ?_
  · filter_upwards with x
    have h1 : Continuous fun q : H × ℝ => σ (⟪q.1, x⟫ - q.2) := hσc.comp (by fun_prop)
    exact h1.aestronglyMeasurable.smul hγm.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    have hxR : ‖x‖ ≤ R := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_sub_norm_le x x₀
      linarith [le_of_lt hx]
    exact Filter.Eventually.of_forall fun q => norm_synthesis_le_majorant hp hσg hxR γ q
  · exact hmom.const_mul _
  · filter_upwards with q
    refine ContinuousAt.smul ?_ continuousAt_const
    exact (hσc.comp (by fun_prop : Continuous fun x : H => ⟪q.1, x⟫ - q.2)).continuousAt

/-! ### The bias convention -/

/-- The bias transport `τ(a, b) = (a, -b)` preserves the parameter measure. -/
theorem measurePreserving_neg_bias {ν : Measure H} [SFinite ν] :
    MeasurePreserving (fun q : H × ℝ => (q.1, -q.2)) (ν.prod volume) (ν.prod volume) := by
  have hneg : MeasurePreserving (fun t : ℝ => -t) volume volume :=
    Measure.measurePreserving_neg volume
  have h := (MeasurePreserving.id ν).prod hneg
  exact h

/-- **The bias convention.**  The synthesis written in the manuscript's convention
`σ(⟪a, x⟫ - b)` is the integral network of the library's convention `σ(⟪a, x⟫ + c)` applied to
the transported coefficient `γ ∘ τ`, `τ(a, c) = (a, -c)`. -/
theorem integral_synthesis_eq_integralNetworkDensity (σ : ℝ → ℂ) {ν : Measure H} [SFinite ν]
    (γ : H × ℝ → Y) (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) =
      integralNetworkDensity σ (parameterMeasure ν) (fun q => γ (q.1, -q.2)) x := by
  rw [integralNetworkDensity, parameterMeasure]
  have hmp : MeasurePreserving (fun q : H × ℝ => (q.1, -q.2)) (ν.prod volume) (ν.prod volume) :=
    measurePreserving_neg_bias
  have hemb : MeasurableEmbedding fun q : H × ℝ => (q.1, -q.2) :=
    ((MeasurableEquiv.refl H).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have h := hmp.integral_comp hemb
    (fun q : H × ℝ => σ (⟪q.1, x⟫ + q.2) • γ (q.1, -q.2))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [neg_neg]
  rw [← sub_eq_add_neg]

end OperatorRidgelet
