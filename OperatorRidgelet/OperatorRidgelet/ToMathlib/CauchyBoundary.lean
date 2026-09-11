import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral

/-!
# Cauchy boundary limits and a Hadamard finite part

For complex Schwartz functions on the real line, the Poisson kernel converges to point
evaluation, the odd Cauchy kernel converges to a symmetric principal value, and the
finite part of division by the square of the coordinate is the principal value of the
derivative. All limits are limits of ordinary Bochner integrals.
-/

noncomputable section
open MeasureTheory Complex Filter Topology Set
open scoped ENNReal

namespace SchwartzMap

/-- Reflection changes a negative-ray integral into a positive-ray integral. -/
theorem integral_negative_ray (f : ℝ → ℂ) (a : ℝ) :
    (∫ x in Iio (-a), f x) = ∫ x in Ioi a, f (-x) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
    ← integral_neg_eq_self ((Iio (-a)).indicator f)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [indicator_apply, mem_Iio, mem_Ioi, neg_lt_neg_iff]

/-- Dividing an integrable function by a coordinate power preserves integrability away from zero. -/
theorem integrableOn_div_pow_abs {f : ℝ → ℂ} (hf : Integrable f) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) :
    IntegrableOn (fun x : ℝ => f x / (x : ℂ) ^ n) {x : ℝ | ε < |x|} := by
  have hm : AEStronglyMeasurable (fun x : ℝ => f x / (x : ℂ) ^ n) (volume : Measure ℝ) := by
    simp only [div_eq_mul_inv]
    exact hf.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.pow_const n).inv.aestronglyMeasurable)
  apply (hf.norm.div_const (ε ^ n)).integrableOn.mono' hm.restrict
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const continuous_abs.measurable)] with x hx
  change ε < |x| at hx
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε n)
  exact pow_le_pow_left₀ hε.le hx.le n

/-- A symmetrically truncated inverse-square integral is an integral on the positive half-line. -/
theorem integral_truncated_eq_symmetric (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in {x : ℝ | ε < |x|}, φ x / (x : ℂ) ^ 2) =
      ∫ x in Ioi ε, (φ x + φ (-x)) / (x : ℂ) ^ 2 := by
  have hcut := integrableOn_div_pow_abs φ.integrable hε 2
  have hs : {x : ℝ | ε < |x|} = Iio (-ε) ∪ Ioi ε := by
    ext x
    simp only [mem_setOf_eq, lt_abs, mem_union, mem_Iio, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Iio (-ε)) (Ioi ε) := by
    apply disjoint_left.mpr
    intro x hx hx'
    have hx1 : x < -ε := hx
    have hx2 : ε < x := hx'
    linarith
  have hn : IntegrableOn (fun x : ℝ => φ x / (x : ℂ) ^ 2) (Iio (-ε)) :=
    hcut.mono_set (by rw [hs]; exact subset_union_left)
  have hp : IntegrableOn (fun x : ℝ => φ x / (x : ℂ) ^ 2) (Ioi ε) :=
    hcut.mono_set (by rw [hs]; exact subset_union_right)
  have hnp : IntegrableOn (fun x : ℝ => φ (-x) / (x : ℂ) ^ 2) (Ioi ε) :=
    (integrableOn_div_pow_abs φ.integrable.comp_neg hε 2).mono_set (by
      intro x hx
      exact lt_of_lt_of_le hx (le_abs_self x))
  rw [hs, setIntegral_union hd measurableSet_Ioi hn hp, integral_negative_ray]
  simp only [Complex.ofReal_neg, neg_sq]
  rw [← integral_add hnp hp]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  ring

/-- Reflection changes integration over the negative half-line into integration over the positive half-line. -/
theorem integral_negative_half (f : ℝ → ℂ) :
    (∫ x in Iio (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f (-x) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
    ← integral_neg_eq_self ((Iio (0 : ℝ)).indicator f)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [indicator_apply, mem_Iio, mem_Ioi, neg_lt_zero]

/-- An integrable function can be integrated by summing its two reflected half-lines. -/
theorem integral_eq_positive_add_negative {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∫ x in Ioi (0 : ℝ), f x + f (-x) := by
  rw [integral_add hf.integrableOn hf.comp_neg.integrableOn, add_comm,
    ← integral_negative_half]
  rw [restrict_Iio_eq_restrict_Iic]
  exact (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm

/-- The symmetric first difference divided by the coordinate. -/
def symmetricSlope (φ : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  (φ x - φ (-x)) / (x : ℂ)

/-- The symmetric slope of a Schwartz function is integrable on the positive half-line. -/
theorem integrableOn_symmetricSlope (φ : SchwartzMap ℝ ℂ) :
    IntegrableOn (symmetricSlope φ) (Ioi (0 : ℝ)) := by
  let L : ℝ := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℂ ℂ φ)
  have hderiv : ∀ x : ℝ, ‖deriv φ x‖ ≤ L := by
    intro x
    rw [← SchwartzMap.derivCLM_apply ℂ φ x]
    exact (SchwartzMap.derivCLM ℂ ℂ φ).norm_le_seminorm ℝ x
  have hbound (x : ℝ) : ‖φ x - φ (-x)‖ ≤ L * ‖x - (-x)‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => (φ.smooth 1).differentiable one_ne_zero y)
      (fun y _ => hderiv y) convex_univ (mem_univ _) (mem_univ _)
  have hmeas : AEStronglyMeasurable (symmetricSlope φ) (volume : Measure ℝ) := by
    unfold symmetricSlope
    exact ((φ.continuous.measurable.sub (φ.continuous.measurable.comp measurable_neg)).div
      Complex.measurable_ofReal).aestronglyMeasurable
  have hnear : IntegrableOn (symmetricSlope φ) (Ioc (0 : ℝ) 1) := by
    have hc : IntegrableOn (fun _ : ℝ => 2 * L) (Ioc (0 : ℝ) 1) (volume : Measure ℝ) :=
      integrableOn_const (by simp)
    apply hc.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change 0 < x ∧ x ≤ 1 at hx
    rw [symmetricSlope, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1,
      div_le_iff₀ hx.1]
    have hb := hbound x
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x - (-x))] at hb
    nlinarith
  have hsum : Integrable (fun x : ℝ => ‖φ x‖ + ‖φ (-x)‖) :=
    φ.integrable.norm.add φ.integrable.comp_neg.norm
  have hfar : IntegrableOn (symmetricSlope φ) (Ioi (1 : ℝ)) := by
    apply hsum.integrableOn.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [symmetricSlope, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < x)]
    exact (div_le_div_of_nonneg_right (norm_sub_le _ _) (by linarith)).trans
      (div_le_self (by positivity) (by linarith))
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hs, integrableOn_union]
  exact ⟨hnear, hfar⟩

/-- The odd Cauchy kernel times a Schwartz function is integrable. -/
theorem integrable_cauchyOdd (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => ((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x) := by
  apply φ.integrable.bdd_mul (c := ε⁻¹)
    ((measurable_id.div (measurable_const.add (measurable_id.pow_const 2))).complex_ofReal.aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.div_apply, Pi.add_apply, id_eq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : 0 < ε ^ 2 + x ^ 2)]
  rw [← one_div, div_le_div_iff₀ (by positivity : 0 < ε ^ 2 + x ^ 2) hε]
  nlinarith [sq_nonneg (|x| - ε), sq_abs x]

/-- Symmetrization writes the odd Cauchy integral as a bounded multiple of the symmetric slope. -/
theorem integral_cauchyOdd_eq_symmetric (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, ((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x) =
      ∫ x in Ioi (0 : ℝ), ((x ^ 2 / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * symmetricSlope φ x := by
  rw [integral_eq_positive_add_negative (integrable_cauchyOdd φ hε)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  dsimp [symmetricSlope]
  push_cast
  field_simp
  ring

/-- The odd Cauchy kernel converges to the symmetric principal-value integral. -/
theorem tendsto_integral_cauchyOdd (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, ((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0 : ℝ), symmetricSlope φ x)) := by
  have hint := integrableOn_symmetricSlope φ
  have hlim : Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ),
      ((x ^ 2 / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * symmetricSlope φ x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0 : ℝ), symmetricSlope φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖symmetricSlope φ x‖)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) hint.norm ?_
    · exact ((measurable_id.pow_const 2).div
        (measurable_const.add (measurable_id.pow_const 2))).complex_ofReal.aestronglyMeasurable.mul
          hint.aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / (ε ^ 2 + x ^ 2))]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact div_le_one_of_le₀ (by nlinarith [sq_nonneg ε]) (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hc : ContinuousAt (fun ε : ℝ =>
          ((x ^ 2 / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * symmetricSlope φ x) 0 := by
        fun_prop (disch := positivity)
      simpa [hx0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_cauchyOdd_eq_symmetric φ hε).symm

/-- The Poisson kernel times a Schwartz function is integrable. -/
theorem integrable_poisson (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x) := by
  apply φ.integrable.bdd_mul (c := ε⁻¹)
    ((measurable_const.div (measurable_const.add (measurable_id.pow_const 2))).complex_ofReal.aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.div_apply, Pi.add_apply, id_eq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hε,
    abs_of_pos (by positivity : 0 < ε ^ 2 + x ^ 2)]
  rw [← one_div, div_le_div_iff₀ (by positivity : 0 < ε ^ 2 + x ^ 2) hε]
  nlinarith [sq_nonneg x]

/-- Rescaling the Poisson kernel transfers its scale to the Schwartz function. -/
theorem integral_poisson_eq_scaled (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x) =
      ∫ x : ℝ, (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * φ (ε * x) := by
  let g : ℝ → ℂ := fun x => (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * φ (ε * x)
  have he : (fun x : ℝ => ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x) =
      fun x => (ε⁻¹ : ℝ) • g (ε⁻¹ * x) := by
    funext x
    dsimp [g]
    rw [mul_inv_cancel_left₀ hε.ne']
    have hr : ε / (ε ^ 2 + x ^ 2) = ε⁻¹ * (1 + (ε⁻¹ * x) ^ 2)⁻¹ := by
      field_simp
    rw [hr, Complex.ofReal_mul, mul_assoc]
  rw [he, integral_smul, Measure.integral_comp_inv_mul_left, abs_of_pos hε, smul_smul,
    inv_mul_cancel₀ hε.ne', one_smul]

/-- The Poisson kernel converges to pi times point evaluation. -/
theorem tendsto_integral_poisson (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * φ x)
      (𝓝[>] 0) (𝓝 ((Real.pi : ℂ) * φ 0)) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * φ (ε * x)) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * φ 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (1 + x ^ 2)⁻¹ * SchwartzMap.seminorm ℝ 0 0 φ)
      (Eventually.of_forall fun ε => (by fun_prop))
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_)
      (integrable_inv_one_add_sq.mul_const _) ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 + x ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℝ _) (by positivity)
    · filter_upwards with x
      apply Tendsto.const_mul
      have ht : Tendsto (fun ε : ℝ => ε * x) (𝓝[>] 0) (𝓝 0) := by
        have ht0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using ht0.mul_const x
      exact φ.continuous.continuousAt.tendsto.comp ht
  have hv : (∫ x : ℝ, (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * φ 0) = (Real.pi : ℂ) * φ 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_univ_inv_one_add_sq]
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_poisson_eq_scaled φ hε).symm

/-- Integration by parts relates the inverse-square truncation to the symmetric slope of the derivative. -/
theorem integral_truncated_parts (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in {x : ℝ | ε < |x|}, φ x / (x : ℂ) ^ 2) =
      (∫ x in Ioi ε, symmetricSlope (derivCLM ℂ ℂ φ) x) +
        (φ ε + φ (-ε)) / (ε : ℂ) := by
  let D := derivCLM ℂ ℂ φ
  let A := fun x : ℝ => φ x + φ (-x)
  let B := fun x : ℝ => A x / (x : ℂ)
  have hD (x : ℝ) : HasDerivAt φ (D x) x := by
    simpa [D, derivCLM_apply] using ((φ.smooth 1).differentiable one_ne_zero x).hasDerivAt
  have hA (x : ℝ) : HasDerivAt A (D x - D (-x)) x := by
    convert (hD x).add ((hD (-x)).scomp x (hasDerivAt_neg x)) using 1 <;>
      first | rfl | simp [sub_eq_add_neg]
  have hderiv (x : ℝ) (hx : x ∈ Ici ε) :
      HasDerivAt B (symmetricSlope D x - A x / (x : ℂ) ^ 2) x := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hε hx))
    apply ((hA x).div (Complex.ofRealCLM.hasDerivAt) hx0).congr_deriv
    dsimp [symmetricSlope]
    field_simp
  have hiD := (integrableOn_symmetricSlope D).mono_set (Ioi_subset_Ioi hε.le)
  have hiA : IntegrableOn (fun x => A x / (x : ℂ) ^ 2) (Ioi ε) :=
    (integrableOn_div_pow_abs (φ.integrable.add φ.integrable.comp_neg) hε 2).mono_set (by
      intro x hx
      exact lt_of_lt_of_le hx (le_abs_self x))
  have htop : Tendsto B atTop (𝓝 0) := by
    have hp := φ.tendsto_cocompact.mono_left atTop_le_cocompact
    have hn := (φ.tendsto_cocompact.mono_left atBot_le_cocompact).comp
      tendsto_neg_atTop_atBot
    have hinv : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
      exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
    simpa [B, A, div_eq_mul_inv] using (hp.add hn).mul hinv
  have hparts := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hiD.sub hiA) htop
  rw [integral_sub hiD hiA] at hparts
  rw [integral_truncated_eq_symmetric φ hε]
  dsimp [B, A] at hparts
  change (∫ x in Ioi ε, A x / (x : ℂ) ^ 2) = _
  linear_combination -hparts

/-- The Hadamard finite part of the inverse square is the principal value of the derivative. -/
theorem tendsto_finitePart (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ =>
      (∫ x in {x : ℝ | ε < |x|}, φ x / (x : ℂ) ^ 2) - 2 * φ 0 / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0 : ℝ), symmetricSlope (derivCLM ℂ ℂ φ) x)) := by
  have hd := ((φ.smooth 1).differentiable one_ne_zero (0 : ℝ)).hasDerivAt
  have hA : HasDerivAt (fun x : ℝ => φ x + φ (-x)) 0 0 := by
    have hdn : HasDerivAt φ (deriv φ 0) (-(0 : ℝ)) := by simpa using hd
    convert hd.add (hdn.scomp 0 (hasDerivAt_neg (0 : ℝ))) using 1 <;> first | rfl | simp
  have hbound : Tendsto (fun ε : ℝ => (φ ε + φ (-ε) - 2 * φ 0) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Complex.real_smul, div_eq_mul_inv, mul_comm, two_mul] using hA.tendsto_slope_zero_right
  have htail := (integrableOn_symmetricSlope (derivCLM ℂ ℂ φ)).continuousWithinAt_Ici_primitive_Ioi
  have ht : Tendsto (fun ε : ℝ => ∫ x in Ioi ε, symmetricSlope (derivCLM ℂ ℂ φ) x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0 : ℝ), symmetricSlope (derivCLM ℂ ℂ φ) x)) :=
    htail.mono Ioi_subset_Ici_self
  convert (ht.add hbound).congr' ?_ using 1 <;> try simp
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [integral_truncated_parts φ hε]
  ring

/-- Exponential damping of the Fourier integral on the positive half-line gives the Cauchy resolvent. -/
theorem integral_damped_fourier (ψ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) * (∫ ω : ℝ, exp (-I * ((ω : ℂ) * (x : ℂ))) * ψ ω)) =
      ∫ ω : ℝ, ((ε : ℂ) + I * (ω : ℂ))⁻¹ * ψ ω := by
  let f := fun x ω : ℝ => exp (-((ε : ℂ) + I * (ω : ℂ)) * (x : ℂ)) * ψ ω
  have hnorm (x ω : ℝ) : ‖f x ω‖ = Real.exp (-ε * x) * ‖ψ ω‖ := by
    simp [f, Complex.norm_exp]
  have hi : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hε) 0).mul_prod ψ.integrable.norm).mono'
      (by dsimp [f, Function.uncurry]; fun_prop)
    filter_upwards with p
    dsimp only [Function.uncurry]
    rw [hnorm]
  have hleft (x : ℝ) : (Real.exp (-ε * x) : ℂ) * (∫ ω : ℝ, exp (-I * ((ω : ℂ) * (x : ℂ))) * ψ ω) =
      ∫ ω : ℝ, f x ω := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    dsimp [f]
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hleft]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with ω
  dsimp [f]
  rw [integral_mul_const, integral_exp_mul_complex_Ioi (by simp; exact hε)]
  simp only [Complex.ofReal_zero, mul_zero, exp_zero, neg_div_neg_eq, one_div]

end SchwartzMap

