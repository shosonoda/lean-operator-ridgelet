import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OperatorRidgelet.ToMathlib.SubtypeZeroExtend

/-! # Completeness of the sine family on the unit interval

An odd extension reduces uniqueness of sine coefficients to Parseval's identity on a circle.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal ComplexConjugate

namespace MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
/-- The real `L²` space of the open unit interval with restricted Lebesgue volume. -/
abbrev UnitIntervalL2 : Type := Lp ℝ 2 (volume : Measure (Ioo (0 : ℝ) 1))
/-- Lebesgue volume on the open unit interval is finite. -/
local instance : IsFiniteMeasure (volume : Measure (Ioo (0 : ℝ) 1)) :=
  ⟨by rw [Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]; simp⟩
/-- The period of the odd-extension circle is strictly positive. -/
local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- Extension of a unit-interval `L²` representative by zero to the real line. -/
def intervalZeroExtend (x : UnitIntervalL2) : ℝ → ℝ := subtypeZeroExtend (Ioo 0 1) x
/-- The odd extension formed from the zero extension and its reflection. -/
def intervalOddExtend (x : UnitIntervalL2) (t : ℝ) : ℝ :=
    intervalZeroExtend x t - intervalZeroExtend x (-t)

/-- Zero extension preserves square integrability. -/
theorem memLp_intervalZeroExtend (x : UnitIntervalL2) : MemLp (intervalZeroExtend x) 2 volume :=
  (memLp_subtypeZeroExtend_iff measurableSet_Ioo x 2 volume).mpr (Lp.memLp x)

/-- The zero extension is integrable because the original interval has finite volume. -/
theorem integrable_intervalZeroExtend (x : UnitIntervalL2) : Integrable
    (intervalZeroExtend x) volume := by
  rw [← memLp_one_iff_integrable]
  exact (memLp_subtypeZeroExtend_iff measurableSet_Ioo x 1 volume).mpr
    ((Lp.memLp x).mono_exponent one_le_two)

/-- Reflection and subtraction preserve square integrability of the odd extension. -/
theorem memLp_intervalOddExtend (x : UnitIntervalL2) : MemLp (intervalOddExtend x) 2 volume :=
  (memLp_intervalZeroExtend x).sub ((memLp_intervalZeroExtend x).comp_measurePreserving
    (Measure.measurePreserving_neg volume))

/-- The odd extension is integrable on the real line. -/
theorem integrable_intervalOddExtend (x : UnitIntervalL2) : Integrable
    (intervalOddExtend x) volume :=
  (integrable_intervalZeroExtend x).sub
      ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    (integrable_intervalZeroExtend x))

/-- The odd extension agrees with the original representative on the positive unit interval. -/
theorem intervalOddExtend_coe (x : UnitIntervalL2) (t : (Ioo (0 : ℝ) 1)) :
    intervalOddExtend x t = x t := by
  rw [intervalOddExtend, intervalZeroExtend, subtypeZeroExtend_coe]
  have hn : -(t : ℝ) ∉ Ioo (0 : ℝ) 1 := by intro h; linarith [t.property.1, h.1]
  rw [subtypeZeroExtend_of_not_mem _ _ hn, sub_zero]

/-- Reflection negates the odd extension. -/
theorem intervalOddExtend_neg (x : UnitIntervalL2) (t : ℝ) :
    intervalOddExtend x (-t) = -intervalOddExtend x t := by
  simp only [intervalOddExtend, neg_neg]
  ring

/-- The odd extension vanishes outside the interval from `-1` to `1`. -/
theorem intervalOddExtend_of_not_mem (x : UnitIntervalL2) {t : ℝ} (ht : t ∉ Ioc (-1 : ℝ) 1) :
    intervalOddExtend x t = 0 := by
  have h1 : t ∉ Ioo (0 : ℝ) 1 := by simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht; grind
  have h2 : -t ∉ Ioo (0 : ℝ) 1 := by simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht; grind
  simp only [intervalOddExtend, intervalZeroExtend, subtypeZeroExtend_of_not_mem _ _ h1,
    subtypeZeroExtend_of_not_mem _ _ h2, sub_self]

/-- The period-two Fourier character pulled back to the real line. -/
def intervalCharacter (n : ℤ) (t : ℝ) : ℂ := fourier n (t : AddCircle (2 : ℝ))

/-- Reflecting the argument negates the frequency of an interval character. -/
theorem intervalCharacter_neg_arg (n : ℤ) (t : ℝ) :
    intervalCharacter n (-t) = intervalCharacter (-n) t := by
  simp only [intervalCharacter, fourier_coe_apply, Int.cast_neg, Complex.ofReal_neg]
  congr 1
  ring

/-- The period-two character has the usual cosine-plus-imaginary-sine formula. -/
theorem intervalCharacter_eq (n : ℤ) (t : ℝ) :
    intervalCharacter n t = (Real.cos (n * Real.pi * t) : ℂ) +
      (Real.sin (n * Real.pi * t) : ℂ) * Complex.I := by
  rw [intervalCharacter, fourier_coe_apply]
  convert! Complex.exp_ofReal_mul_I ((n : ℝ) * Real.pi * t) using 1
  congr 1
  push_cast
  ring

/-- Multiplication by an interval character preserves integrability. -/
theorem integrable_intervalCharacter_mul (n : ℤ) {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun t => intervalCharacter n t * (g t : ℂ)) := by
  have h := hg.ofReal.mul_bdd (c := 1)
    ((fourier n).continuous.comp (AddCircle.continuous_mk' (2 : ℝ))).aestronglyMeasurable
    (Eventually.of_forall fun t : ℝ => by
      change ‖fourier n (t : AddCircle (2 : ℝ))‖ ≤ 1
      rw [fourier_apply]
      exact (Circle.norm_coe _).le)
  convert! h using 1
  funext t
  simp only [intervalCharacter, Function.comp_def, QuotientAddGroup.mk'_apply, mul_comm]
  rfl

/-- The Fourier integral of an odd extension reduces to its sine integral. -/
theorem integral_intervalCharacter_odd (x : UnitIntervalL2) (n : ℤ) :
    (∫ t, intervalCharacter (-n) t * (intervalOddExtend x t : ℂ)) =
      (-2 * Complex.I) * ∫ t, (Real.sin (n * Real.pi * t) : ℂ) * (intervalZeroExtend x t : ℂ) := by
  have hg := integrable_intervalZeroExtend x
  have hgn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hg
  change Integrable (fun t => intervalZeroExtend x (-t)) at hgn
  simp only [intervalOddExtend, Complex.ofReal_sub, mul_sub]
  rw [integral_sub (integrable_intervalCharacter_mul (-n) hg)
    (integrable_intervalCharacter_mul (-n) hgn)]
  have hn : (∫ t, intervalCharacter (-n) t * (intervalZeroExtend x (-t) : ℂ)) =
      ∫ t, intervalCharacter n t * (intervalZeroExtend x t : ℂ) := by
    rw [← integral_neg_eq_self (fun t => intervalCharacter (-n) t *
        (intervalZeroExtend x (-t) : ℂ))]
    simp only [intervalCharacter_neg_arg, neg_neg]
  rw [hn, ← integral_sub (integrable_intervalCharacter_mul (-n) hg)
    (integrable_intervalCharacter_mul n hg), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [intervalCharacter_eq, Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg]
  ring

/-- Each interval Fourier coefficient of the odd extension is its scaled sine integral. -/
theorem fourierCoeffOn_intervalOddExtend (x : UnitIntervalL2) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (fun t => (intervalOddExtend x t : ℂ)) n =
      -Complex.I * ∫ t, (Real.sin (n * Real.pi * t) : ℂ) * (intervalZeroExtend x t : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_neg_eq_add, one_add_one_eq_two]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hs : (∫ t in Ioc (-1 : ℝ) 1,
      intervalCharacter (-n) t * (intervalOddExtend x t : ℂ)) =
      ∫ t, intervalCharacter (-n) t * (intervalOddExtend x t : ℂ) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [intervalOddExtend_of_not_mem x ht, Complex.ofReal_zero, mul_zero]
  simp only [smul_eq_mul]
  have he : (∫ t in Ioc (-1 : ℝ) 1, (fourier (-n)) (t : AddCircle (2 : ℝ)) *
      (intervalOddExtend x t : ℂ)) =
      (-2 * Complex.I) * ∫ t, (Real.sin (n * Real.pi * t) : ℂ) *
        (intervalZeroExtend x t : ℂ) := hs.trans (integral_intervalCharacter_odd x n)
  simp only [fourier_coe_apply] at he ⊢
  norm_num only [sub_neg_eq_add, one_add_one_eq_two]
  rw [he]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The sine integral of the zero extension equals the integral on the original interval. -/
theorem integral_sin_zeroExtend (x : UnitIntervalL2) (n : ℤ) :
    (∫ t, Real.sin (n * Real.pi * t) * intervalZeroExtend x t) =
      ∫ t : (Ioo (0 : ℝ) 1), Real.sin (n * Real.pi * t) * x t := by
  have hf : (fun t => Real.sin (n * Real.pi * t) * intervalZeroExtend x t) =
      subtypeZeroExtend (Ioo (0 : ℝ) 1)
        (fun t : (Ioo (0 : ℝ) 1) => Real.sin (n * Real.pi * t) * x t) := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · change Real.sin (n * Real.pi * (⟨t,ht⟩ : (Ioo (0 : ℝ) 1))) *
        subtypeZeroExtend (Ioo 0 1) x (⟨t,ht⟩ : (Ioo (0 : ℝ) 1)) = _
      rw [subtypeZeroExtend_coe]
      exact (subtypeZeroExtend_coe (Ioo (0 : ℝ) 1)
        (fun t : (Ioo (0 : ℝ) 1) => Real.sin (n * Real.pi * t) * x t) ⟨t,ht⟩).symm
    · simp only [intervalZeroExtend, subtypeZeroExtend_of_not_mem _ _ ht, mul_zero]
  rw [hf, integral_subtypeZeroExtend measurableSet_Ioo]
  rfl

/-- Vanishing nonnegative-frequency sine integrals also gives vanishing integer frequencies. -/
theorem integral_sin_int_eq_zero {x : UnitIntervalL2}
    (hx : ∀ n : ℕ, (∫ t : (Ioo (0 : ℝ) 1), Real.sin (n * Real.pi * t) * x t) = 0) (n : ℤ) :
    (∫ t : (Ioo (0 : ℝ) 1), Real.sin (n * Real.pi * t) * x t) = 0 := by
  cases n with
  | ofNat n => exact hx n
  | negSucc n =>
    simp only [Int.cast_negSucc, neg_mul, Real.sin_neg]
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul, integral_neg, neg_zero] using
      congrArg Neg.neg (hx (n+1))

/-- Vanishing sine integrals force every Fourier coefficient of the odd extension to vanish. -/
theorem fourierCoeffOn_intervalOddExtend_eq_zero {x : UnitIntervalL2}
    (hx : ∀ n : ℕ, (∫ t : (Ioo (0 : ℝ) 1), Real.sin (n * Real.pi * t) * x t) = 0) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (fun t => (intervalOddExtend x t : ℂ)) n = 0 := by
  rw [fourierCoeffOn_intervalOddExtend]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, integral_sin_zeroExtend, integral_sin_int_eq_zero hx]
  simp

/-- A square-integrable unit-interval function with all sine integrals zero is zero in `L²`. -/
theorem eq_zero_of_integral_sin {x : UnitIntervalL2}
    (hx : ∀ n : ℕ, (∫ t : (Ioo (0 : ℝ) 1), Real.sin (n * Real.pi * t) * x t) = 0) : x = 0 := by
  have hL2 : MemLp (fun t => (intervalOddExtend x t : ℂ)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := (memLp_intervalOddExtend x).ofReal.mono_measure
    (Measure.restrict_le_self (s := Ioc (-1 : ℝ) 1))
  have hp := (hasSum_sq_fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) hL2).tsum_eq
  simp only [fourierCoeffOn_intervalOddExtend_eq_zero hx, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    tsum_zero, sub_neg_eq_add, one_add_one_eq_two, smul_eq_mul] at hp
  have hi : (∫ t in Ioc (-1 : ℝ) 1, ‖(intervalOddExtend x t : ℂ)‖ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hp
    linarith
  have hz : ∀ᵐ t ∂volume.restrict (Ioc (-1 : ℝ) 1), intervalOddExtend x t = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖(intervalOddExtend x t : ℂ)‖)
      ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2)).mp hi
    filter_upwards [h] with t ht
    simpa using ht
  have hs : (Ioo (0 : ℝ) 1) ⊆ Ioc (-1 : ℝ) 1 := by intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hz' := (ae_restrict_iff_subtype measurableSet_Ioo).mp
    (ae_restrict_of_ae_restrict_of_subset hs hz)
  apply Lp.ext
  filter_upwards [hz', Lp.coeFn_zero ℝ 2 (volume : Measure (Ioo (0 : ℝ) 1))] with t ht ht0
  rw [ht0, ← intervalOddExtend_coe x t]
  exact ht
end MeasureTheory
