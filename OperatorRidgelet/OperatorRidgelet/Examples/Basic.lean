import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.ToMathlib.GaussianRealIntegral
import OperatorRidgelet.Transform.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Auxiliary lemmas for Section 7 and Appendix E

Elementary facts used by the proofs in `OperatorRidgelet.Paper.Examples`; not imported by
`Challenge`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory LeanRidgelet Filter

/-- `|b|^j e^{-b²/2}` is integrable on `ℝ` for every `j`. -/
theorem integrable_abs_pow_mul_exp_neg_sq_half (j : ℕ) :
    Integrable fun b : ℝ => |b| ^ j * Real.exp (-b ^ 2 / 2) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) (s := (j : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) j])).abs
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [Real.rpow_natCast, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

/-- The real ReLU activation is continuous. -/
theorem continuous_relu : Continuous relu := by
  unfold relu
  fun_prop

/-- The second derivative formula for the Gaussian activation is continuous. -/
theorem continuous_gaussianActDeriv2 : Continuous gaussianActDeriv2 := by
  unfold gaussianActDeriv2
  fun_prop

/-- `|φ''(b)| ≤ (b² + 1) e^{-b²/2}`. -/
theorem abs_gaussianActDeriv2_le (b : ℝ) :
    |gaussianActDeriv2 b| ≤ (b ^ 2 + 1) * Real.exp (-b ^ 2 / 2) := by
  unfold gaussianActDeriv2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg b]

/-! ### Moments of `φ''` -/

/-- `φ''` is integrable. -/
theorem integrable_gaussianActDeriv2 : Integrable gaussianActDeriv2 := by
  have h0 := integrable_abs_pow_mul_exp_neg_sq_half 0
  have h2 := integrable_abs_pow_mul_exp_neg_sq_half 2
  refine (h2.add h0).mono' continuous_gaussianActDeriv2.aestronglyMeasurable
    (Eventually.of_forall fun b => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_gaussianActDeriv2_le b).trans (le_of_eq ?_)
  simp only [Pi.add_apply, sq_abs, pow_zero]
  ring

/-- **Lemma `lem:gaussian-hinge`(ii)**: `∫ (1 + |b|^k) |φ''(b)| db < ∞` for every `k`. -/
theorem integrable_one_add_abs_pow_mul_abs_gaussianActDeriv2 (k : ℕ) :
    Integrable fun b : ℝ => (1 + |b| ^ k) * |gaussianActDeriv2 b| := by
  have h0 := integrable_abs_pow_mul_exp_neg_sq_half 0
  have h2 := integrable_abs_pow_mul_exp_neg_sq_half 2
  have hk := integrable_abs_pow_mul_exp_neg_sq_half k
  have hk2 := integrable_abs_pow_mul_exp_neg_sq_half (k + 2)
  refine ((h2.add h0).add (hk2.add hk)).mono' ?_ ?_
  · exact ((continuous_const.add (continuous_abs.pow k)).mul
      continuous_gaussianActDeriv2.abs).aestronglyMeasurable
  · filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb2 : b ^ 2 + 1 = |b| ^ 2 + |b| ^ 0 := by rw [sq_abs, pow_zero]
    calc (1 + |b| ^ k) * |gaussianActDeriv2 b|
        ≤ (1 + |b| ^ k) * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (abs_gaussianActDeriv2_le b) (by positivity)
      _ = |b| ^ 2 * Real.exp (-b ^ 2 / 2) + |b| ^ 0 * Real.exp (-b ^ 2 / 2) +
          (|b| ^ (k + 2) * Real.exp (-b ^ 2 / 2) + |b| ^ k * Real.exp (-b ^ 2 / 2)) := by
          rw [hb2]; ring

/-- `(u + v)^k ≤ 2^k (u^k + v^k)` for `u, v ≥ 0`. -/
theorem add_pow_le_two_pow_mul_add_pow {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (k : ℕ) :
    (u + v) ^ k ≤ 2 ^ k * (u ^ k + v ^ k) := by
  have h1 : u + v ≤ 2 * max u v := by
    rcases le_total u v with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (u + v) ^ k ≤ (2 * max u v) ^ k := pow_le_pow_left₀ (by positivity) h1 k
    _ = 2 ^ k * (max u v) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (u ^ k + v ^ k) := by
        gcongr
        rcases le_total u v with h | h
        · rw [max_eq_right h]; linarith [pow_nonneg hu k]
        · rw [max_eq_left h]; linarith [pow_nonneg hv k]

/-- `|t|^k |φ''(t)|` is integrable. -/
theorem integrable_abs_pow_mul_abs_gaussianActDeriv2 (k : ℕ) :
    Integrable fun t : ℝ => |t| ^ k * |gaussianActDeriv2 t| := by
  refine (integrable_one_add_abs_pow_mul_abs_gaussianActDeriv2 k).mono'
    ((continuous_abs.pow k).mul continuous_gaussianActDeriv2.abs).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : 0 ≤ |gaussianActDeriv2 t| := abs_nonneg _
  nlinarith [pow_nonneg (abs_nonneg t) k]

/-- `(1 + C + |t|)^k |φ''(t)|` is integrable for `C ≥ 0`. -/
theorem integrable_const_add_abs_pow_mul_abs_gaussianActDeriv2 {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    Integrable fun t : ℝ => (1 + C + |t|) ^ k * |gaussianActDeriv2 t| := by
  refine ((integrable_one_add_abs_pow_mul_abs_gaussianActDeriv2 k).const_mul
    ((1 + C) ^ k * 2 ^ k)).mono'
    (((continuous_const.add continuous_abs).pow k).mul
      continuous_gaussianActDeriv2.abs).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : (1 + C + |t|) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + |t| ^ k)) := by
    calc (1 + C + |t|) ^ k ≤ ((1 + C) * (1 + |t|)) ^ k := by
          gcongr
          nlinarith [abs_nonneg t]
      _ = (1 + C) ^ k * (1 + |t|) ^ k := mul_pow _ _ _
      _ ≤ (1 + C) ^ k * (2 ^ k * (1 + |t| ^ k)) := by
          gcongr
          exact one_add_pow_le_two_pow_mul (abs_nonneg t) k
  calc (1 + C + |t|) ^ k * |gaussianActDeriv2 t|
      ≤ (1 + C) ^ k * (2 ^ k * (1 + |t| ^ k)) * |gaussianActDeriv2 t| := by gcongr
    _ = (1 + C) ^ k * 2 ^ k * ((1 + |t| ^ k) * |gaussianActDeriv2 t|) := by ring

/-! ### The hinge representation of the Gaussian -/

/-- `(b² + 1) e^{-b²/2}` is integrable. -/
theorem integrable_sq_add_one_mul_exp :
    Integrable fun b : ℝ => (b ^ 2 + 1) * Real.exp (-b ^ 2 / 2) := by
  have h0 := integrable_abs_pow_mul_exp_neg_sq_half 0
  have h2 := integrable_abs_pow_mul_exp_neg_sq_half 2
  refine (h2.add h0).congr (Eventually.of_forall fun b => ?_)
  simp only [Pi.add_apply, sq_abs, pow_zero]
  ring

/-- `|b| (b² + 1) e^{-b²/2}` is integrable. -/
theorem integrable_abs_mul_sq_add_one_mul_exp :
    Integrable fun b : ℝ => |b| * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) := by
  have h1 := integrable_abs_pow_mul_exp_neg_sq_half 1
  have h3 := integrable_abs_pow_mul_exp_neg_sq_half 3
  refine (h3.add h1).congr (Eventually.of_forall fun b => ?_)
  simp only [Pi.add_apply, pow_one]
  have hb2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  rw [hb2]
  ring

/-- The pointwise bound `|ReLU(u - b) φ''(b)| ≤ (|u| + |b|) (b² + 1) e^{-b²/2}`. -/
theorem norm_relu_sub_mul_gaussianActDeriv2_le (u b : ℝ) :
    ‖relu (u - b) * gaussianActDeriv2 b‖ ≤
      |u| * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) +
        |b| * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (relu_nonneg _)]
  have hr : relu (u - b) ≤ |u| + |b| := by
    unfold relu
    exact max_le (by linarith [le_abs_self u, neg_abs_le b]) (by positivity)
  calc relu (u - b) * |gaussianActDeriv2 b|
      ≤ (|u| + |b|) * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) :=
        mul_le_mul hr (abs_gaussianActDeriv2_le b) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Lemma `lem:gaussian-hinge`(i)**, absolute convergence: `b ↦ ReLU(u - b) φ''(b)` is
integrable for every `u`. -/
theorem integrable_relu_sub_mul_gaussianActDeriv2 (u : ℝ) :
    Integrable fun b : ℝ => relu (u - b) * gaussianActDeriv2 b := by
  refine ((integrable_sq_add_one_mul_exp.const_mul |u|).add
    integrable_abs_mul_sq_add_one_mul_exp).mono' ?_
    (Eventually.of_forall fun b => norm_relu_sub_mul_gaussianActDeriv2_le u b)
  exact ((continuous_relu.comp (continuous_const.sub continuous_id)).mul
    continuous_gaussianActDeriv2).aestronglyMeasurable

/-- **Lemma `lem:gaussian-hinge`(i)**, the identity: `∫ ReLU(u - b) φ''(b) db = φ(u)`. -/
theorem integral_relu_sub_mul_gaussianActDeriv2 (u : ℝ) :
    ∫ b : ℝ, relu (u - b) * gaussianActDeriv2 b = gaussianFun u :=
  integral_max_sub_mul_gaussian_deriv2 u

/-- The `L¹` norm of the hinge integrand grows at most linearly in `u`:
`∫ |ReLU(u - b) φ''(b)| db ≤ |u| C₀ + C₁`. -/
theorem integral_norm_relu_sub_mul_gaussianActDeriv2_le (u : ℝ) :
    ∫ b : ℝ, ‖relu (u - b) * gaussianActDeriv2 b‖ ≤
      |u| * (∫ b : ℝ, (b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) +
        ∫ b : ℝ, |b| * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) := by
  rw [← integral_const_mul, ← integral_add (integrable_sq_add_one_mul_exp.const_mul _)
    integrable_abs_mul_sq_add_one_mul_exp]
  exact integral_mono (integrable_relu_sub_mul_gaussianActDeriv2 u).norm
    ((integrable_sq_add_one_mul_exp.const_mul _).add integrable_abs_mul_sq_add_one_mul_exp)
    fun b => norm_relu_sub_mul_gaussianActDeriv2_le u b

/-- The hinge integrand `(y, b) ↦ ReLU(u(y) - b) φ''(b)` is integrable on `m ⊗ db` whenever
`u` is integrable with respect to the σ-finite measure `m`. -/
theorem integrable_relu_sub_mul_gaussianActDeriv2_prod {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) [IsFiniteMeasure m] {u : Ω → ℝ} (hu : Integrable u m) :
    Integrable (fun p : Ω × ℝ => relu (u p.1 - p.2) * gaussianActDeriv2 p.2) (m.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : Ω × ℝ => relu (u p.1 - p.2) * gaussianActDeriv2 p.2) (m.prod volume) := by
    refine (continuous_relu.comp_aestronglyMeasurable
      ((hu.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
        measurable_snd.aestronglyMeasurable)).mul ?_
    exact continuous_gaussianActDeriv2.comp_aestronglyMeasurable measurable_snd.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun y => integrable_relu_sub_mul_gaussianActDeriv2 (u y), ?_⟩
  refine ((hu.norm.mul_const (∫ b : ℝ, (b ^ 2 + 1) * Real.exp (-b ^ 2 / 2))).add
    (integrable_const (∫ b : ℝ, |b| * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2))))).mono'
    hmeas.norm.integral_prod_right' (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun b => norm_nonneg _), Real.norm_eq_abs]
  exact integral_norm_relu_sub_mul_gaussianActDeriv2_le (u y)

end OperatorRidgelet
