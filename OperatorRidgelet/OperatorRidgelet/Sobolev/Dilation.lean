import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OperatorRidgelet.Sobolev.Basic

/-!
# Dilations of a Sobolev ray

The rays of the Gaussian-derivative filters of Appendix I are dilates `b ↦ γ(b/A)` of one
profile.  This module records what a dilation does to the three ingredients of
`lem:sobolev-tools`: the Sobolev class, the Sobolev norm, which grows by at most `A^{s+1/2}`
for `A ≥ 1`, and the frequency profile, which is dilated the other way.

The criterion `memRaySobolev_iff` restates the membership as the integrability of the weighted
square, which is the form in which the change of variables `b = At` is available.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Membership in the Sobolev class is the integrability of `⟨t⟩^{2s} ‖γ(t)‖²`. -/
theorem memRaySobolev_iff {s : ℝ} {γ : ℝ → Y} (hm : AEStronglyMeasurable γ volume) :
    MemRaySobolev s γ ↔
      Integrable (fun t => (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) volume := by
  have hmeas : AEStronglyMeasurable (fun t => (bracket t ^ s : ℝ) • γ t) volume :=
    ((continuous_bracket.rpow_const fun _ => Or.inl (bracket_pos _).ne').aestronglyMeasurable).smul
      hm
  rw [MemRaySobolev, memLp_two_iff_integrable_sq_norm hmeas]
  refine integrable_congr (Filter.Eventually.of_forall fun t => ?_)
  show ‖(bracket t ^ s : ℝ) • γ t‖ ^ 2 = (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (bracket_pos t) s), mul_pow,
    bracket_rpow_sq, bracket_rpow_two_mul]

/-- The bracket of a dilation, for `A ≥ 1`. -/
theorem bracket_mul_le {A : ℝ} (hA : 1 ≤ A) (t : ℝ) : bracket (A * t) ≤ A * bracket t := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hb : bracket t ^ 2 = 1 + t ^ 2 := by
    rw [bracket, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have hsq : 1 + (A * t) ^ 2 ≤ (A * bracket t) ^ 2 := by
    have h1 : (1 : ℝ) ≤ A ^ 2 := one_le_pow₀ hA
    have h2 : (A * bracket t) ^ 2 = A ^ 2 * (1 + t ^ 2) := by rw [mul_pow, hb]
    nlinarith [sq_nonneg t]
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (mul_nonneg hA0.le (bracket_pos t).le)] at hle
  rwa [show bracket (A * t) = Real.sqrt (1 + (A * t) ^ 2) by
    rw [bracket, Real.sqrt_eq_rpow]]

omit [NormedSpace ℂ Y] in
/-- Dilating the argument of a measurable ray keeps it measurable. -/
theorem aestronglyMeasurable_dilate {A : ℝ} (hA : A ≠ 0) {γ : ℝ → Y}
    (hm : AEStronglyMeasurable γ volume) :
    AEStronglyMeasurable (fun b : ℝ => γ (b / A)) volume := by
  refine hm.comp_quasiMeasurePreserving ⟨measurable_id.div_const A, ?_⟩
  have hfun : (fun b : ℝ => b / A) = fun b : ℝ => A⁻¹ * b := by
    funext b
    rw [div_eq_inv_mul]
  rw [hfun, Real.map_volume_mul_left (inv_ne_zero hA)]
  exact Measure.smul_absolutelyContinuous

/-- The dilated Sobolev weight is integrable against the square of the ray. -/
theorem integrable_bracket_mul_dilate {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) :
    Integrable (fun t => (bracket (A * t) ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) volume := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hbase := (memRaySobolev_iff (MemRaySobolev.aestronglyMeasurable hγ)).1 hγ
  refine Integrable.mono' (hbase.const_mul (A ^ (2 * s))) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_bracket.comp (continuous_const.mul continuous_id)).rpow_const
        fun _ => Or.inl (bracket_pos _).ne').aestronglyMeasurable
    · exact (((MemRaySobolev.aestronglyMeasurable hγ).norm).pow 2)
  refine Filter.Eventually.of_forall fun t => ?_
  have hpos : (0 : ℝ) < bracket (A * t) ^ (2 * s) :=
    Real.rpow_pos_of_pos (bracket_pos _) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmono : bracket (A * t) ^ (2 * s) ≤ (A * bracket t) ^ (2 * s) :=
    Real.rpow_le_rpow (bracket_pos _).le (bracket_mul_le hA t) (by linarith)
  have hsplit : (A * bracket t) ^ (2 * s) = A ^ (2 * s) * bracket t ^ (2 * s) :=
    Real.mul_rpow hA0.le (bracket_pos t).le
  calc bracket (A * t) ^ (2 * s) * ‖γ t‖ ^ 2
      ≤ (A ^ (2 * s) * bracket t ^ (2 * s)) * ‖γ t‖ ^ 2 := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_right hmono (by positivity)
    _ = A ^ (2 * s) * (bracket t ^ (2 * s) * ‖γ t‖ ^ 2) := by ring

/-- A dilation stays in the Sobolev class. -/
theorem memRaySobolev_dilate {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) : MemRaySobolev s fun b => γ (b / A) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  rw [memRaySobolev_iff
    (aestronglyMeasurable_dilate hA0.ne' (MemRaySobolev.aestronglyMeasurable hγ))]
  have hcomp := MeasureTheory.Integrable.comp_div
    (integrable_bracket_mul_dilate hs hA hγ) hA0.ne'
  refine MeasureTheory.Integrable.congr hcomp (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [show A * (b / A) = b by field_simp]

/-- The Sobolev norm of a dilation grows by at most `A^{s+1/2}` for `A ≥ 1`. -/
theorem raySobolevNorm_dilate_le {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) :
    raySobolevNorm s (fun b => γ (b / A)) ≤ A ^ (s + 1 / 2) * raySobolevNorm s γ := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hbase := (memRaySobolev_iff (MemRaySobolev.aestronglyMeasurable hγ)).1 hγ
  set X : ℝ := ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 with hX
  have hXnn : 0 ≤ X := by
    refine integral_nonneg fun t => ?_
    exact mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (by positivity)
  have hchange : ∫ b : ℝ, (bracket b ^ (2 * s) : ℝ) * ‖γ (b / A)‖ ^ 2 =
      A * ∫ t : ℝ, (bracket (A * t) ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
    have hcomp := Measure.integral_comp_div
      (fun t : ℝ => (bracket (A * t) ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) A
    rw [smul_eq_mul, abs_of_pos hA0] at hcomp
    rw [← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only
    rw [show A * (b / A) = b by field_simp]
  have hmono : ∫ t : ℝ, (bracket (A * t) ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 ≤ A ^ (2 * s) * X := by
    rw [hX, ← integral_const_mul]
    refine integral_mono (integrable_bracket_mul_dilate hs hA hγ) (hbase.const_mul _)
      fun t => ?_
    have hsplit : (A * bracket t) ^ (2 * s) = A ^ (2 * s) * bracket t ^ (2 * s) :=
      Real.mul_rpow hA0.le (bracket_pos t).le
    have hle : bracket (A * t) ^ (2 * s) ≤ A ^ (2 * s) * bracket t ^ (2 * s) := by
      rw [← hsplit]
      exact Real.rpow_le_rpow (bracket_pos _).le (bracket_mul_le hA t) (by linarith)
    calc bracket (A * t) ^ (2 * s) * ‖γ t‖ ^ 2
        ≤ (A ^ (2 * s) * bracket t ^ (2 * s)) * ‖γ t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = A ^ (2 * s) * (bracket t ^ (2 * s) * ‖γ t‖ ^ 2) := by ring
  have hfinal : ∫ b : ℝ, (bracket b ^ (2 * s) : ℝ) * ‖γ (b / A)‖ ^ 2 ≤ A ^ (2 * s + 1) * X := by
    rw [hchange, Real.rpow_add hA0, Real.rpow_one]
    calc A * ∫ t : ℝ, (bracket (A * t) ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2
        ≤ A * (A ^ (2 * s) * X) := mul_le_mul_of_nonneg_left hmono hA0.le
      _ = A ^ (2 * s) * A * X := by ring
  rw [raySobolevNorm, raySobolevNorm, ← hX]
  have hsqrt : Real.sqrt (2 * Real.pi * ∫ b : ℝ, (bracket b ^ (2 * s) : ℝ) * ‖γ (b / A)‖ ^ 2) ≤
      Real.sqrt (A ^ (2 * s + 1) * (2 * Real.pi * X)) := by
    refine Real.sqrt_le_sqrt ?_
    calc 2 * Real.pi * ∫ b : ℝ, (bracket b ^ (2 * s) : ℝ) * ‖γ (b / A)‖ ^ 2
        ≤ 2 * Real.pi * (A ^ (2 * s + 1) * X) := by
          exact mul_le_mul_of_nonneg_left hfinal (by positivity)
      _ = A ^ (2 * s + 1) * (2 * Real.pi * X) := by ring
  refine hsqrt.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (Real.rpow_nonneg hA0.le _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hA0.le]
  congr 2
  ring

/-- Dilating the coefficient dilates the profile the other way. -/
theorem rayProfile_dilate {A : ℝ} (hA : 0 < A) (γ : ℝ → Y) (ω : ℝ) :
    rayProfile (fun b => γ (b / A)) ω = (A : ℝ) • rayProfile γ (A * ω) := by
  unfold rayProfile
  have hcomp := Measure.integral_comp_div
    (fun t : ℝ => Complex.exp (((-(A * ω * t) : ℝ) : ℂ) * Complex.I) • γ t) A
  rw [abs_of_pos hA] at hcomp
  rw [← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [show A * ω * (b / A) = ω * b by field_simp]

/-! ### Scalar multiples of a ray -/

/-- The profile of a scalar multiple. -/
theorem rayProfile_const_smul (c : ℝ) (γ : ℝ → Y) (ω : ℝ) :
    rayProfile (fun b => c • γ b) ω = c • rayProfile γ ω := by
  unfold rayProfile
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [smul_comm]

/-- The profile of a scalar ray times a fixed vector. -/
theorem rayProfile_smul_const [CompleteSpace Y] (φ : ℝ → ℂ) (v : Y) (ω : ℝ) :
    rayProfile (fun b => φ b • v) ω = rayProfile φ ω • v := by
  unfold rayProfile
  rw [← integral_smul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [smul_assoc]

/-- A scalar multiple stays in the Sobolev class. -/
theorem memRaySobolev_const_smul {s c : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    MemRaySobolev s fun b => c • γ b := by
  have h := MeasureTheory.MemLp.const_smul hγ c
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
  show (c : ℝ) • ((bracket t ^ s : ℝ) • γ t) = (bracket t ^ s : ℝ) • c • γ t
  rw [smul_comm]

/-- The Sobolev norm of a scalar multiple. -/
theorem raySobolevNorm_const_smul (s c : ℝ) (γ : ℝ → Y) :
    raySobolevNorm s (fun b => c • γ b) = |c| * raySobolevNorm s γ := by
  have hint : ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖c • γ t‖ ^ 2
      = c ^ 2 * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (bracket t ^ (2 * s) : ℝ) * ‖c • γ t‖ ^ 2
        = c ^ 2 * ((bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  unfold raySobolevNorm
  rw [hint, show 2 * Real.pi * (c ^ 2 * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2)
      = c ^ 2 * (2 * Real.pi * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) from by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- A scalar ray times a fixed vector stays in the Sobolev class. -/
theorem memRaySobolev_smul_const {s : ℝ} {φ : ℝ → ℂ} (hφ : MemRaySobolev s φ) (v : Y) :
    MemRaySobolev s fun b => φ b • v := by
  have hg : MemLp (fun t => (‖v‖ : ℝ) • ((bracket t ^ s : ℝ) • φ t)) 2 volume :=
    MeasureTheory.MemLp.const_smul hφ ‖v‖
  have hbφ : AEStronglyMeasurable (fun t : ℝ => (bracket t ^ s : ℝ) • φ t) volume :=
    ((continuous_bracket.rpow_const fun _ =>
      Or.inl (bracket_pos _).ne').aestronglyMeasurable).smul
      (MemRaySobolev.aestronglyMeasurable hφ)
  refine MeasureTheory.MemLp.mono hg ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine AEStronglyMeasurable.congr (AEStronglyMeasurable.smul_const hbφ v)
      (Filter.Eventually.of_forall fun t => ?_)
    show ((bracket t ^ s : ℝ) • φ t) • v = (bracket t ^ s : ℝ) • φ t • v
    rw [smul_assoc]
  · show ‖(bracket t ^ s : ℝ) • φ t • v‖ ≤ ‖(‖v‖ : ℝ) • ((bracket t ^ s : ℝ) • φ t)‖
    rw [norm_smul, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    ring_nf
    exact le_rfl

/-- The Sobolev norm of a scalar ray times a fixed vector. -/
theorem raySobolevNorm_smul_const (s : ℝ) (φ : ℝ → ℂ) (v : Y) :
    raySobolevNorm s (fun b => φ b • v) = ‖v‖ * raySobolevNorm s φ := by
  have hint : ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖φ t • v‖ ^ 2
      = ‖v‖ ^ 2 * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖φ t‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (bracket t ^ (2 * s) : ℝ) * ‖φ t • v‖ ^ 2
        = ‖v‖ ^ 2 * ((bracket t ^ (2 * s) : ℝ) * ‖φ t‖ ^ 2)
    rw [norm_smul, mul_pow]
    ring
  unfold raySobolevNorm
  rw [hint, show 2 * Real.pi * (‖v‖ ^ 2 * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖φ t‖ ^ 2)
      = ‖v‖ ^ 2 * (2 * Real.pi * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖φ t‖ ^ 2) from by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

end OperatorRidgelet
