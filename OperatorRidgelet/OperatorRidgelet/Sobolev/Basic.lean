import OperatorRidgelet.Sobolev.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OperatorRidgelet.ToMathlib.L2Translation

/-!
# Weighted inverse Fourier estimates along a ray

The estimates of Lemma `lem:sobolev-tools` on the coefficient side: the Sobolev weight is
integrable in the range that makes the constant `A_{s,r}` finite, and weighted Cauchy–Schwarz
turns the Sobolev norm of a profile into a weighted `L¹` bound on its coefficient.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-! ### The Japanese bracket -/

/-- The bracket is positive. -/
theorem bracket_pos (t : ℝ) : 0 < bracket t := Real.rpow_pos_of_pos (by positivity) _

/-- The bracket is at least one. -/
theorem one_le_bracket (t : ℝ) : 1 ≤ bracket t :=
  Real.one_le_rpow (by nlinarith [sq_nonneg t]) (by norm_num)

/-- The bracket is continuous. -/
theorem continuous_bracket : Continuous bracket :=
  (continuous_const.add (continuous_pow 2)).rpow_const fun _ => Or.inr (by norm_num)

/-- Even powers of the bracket are powers of `1 + t²`. -/
theorem bracket_rpow_two_mul (t a : ℝ) : bracket t ^ (2 * a) = ((1 + t ^ 2) ^ a : ℝ) := by
  rw [bracket, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The square of a power of the bracket. -/
theorem bracket_rpow_sq (t a : ℝ) : (bracket t ^ a) ^ 2 = ((1 + t ^ 2) ^ a : ℝ) := by
  rw [← Real.rpow_natCast (bracket t ^ a) 2, ← Real.rpow_mul (bracket_pos t).le, mul_comm a]
  push_cast
  rw [bracket_rpow_two_mul]

/-- Powers of the bracket add. -/
theorem bracket_rpow_add (t a b : ℝ) : bracket t ^ (a + b) = bracket t ^ a * bracket t ^ b :=
  Real.rpow_add (bracket_pos t) a b

/-- The Sobolev weight `(1+t²)^{-(s-r)}` is integrable exactly in the range `s - r > 1/2` that
makes `A_{s,r}` finite. -/
theorem integrable_one_add_sq_rpow_neg {a : ℝ} (ha : 1 / 2 < a) :
    Integrable (fun t : ℝ => ((1 + t ^ 2) ^ (-a) : ℝ)) volume := by
  have hdim : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * a := by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hdim
  have hexp : -(2 * a) / 2 = -a := by ring
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs, hexp]

/-! ### The weighted `L¹` bound -/

/-- **Lemma [lem:sobolev-tools]**, the weighted inverse Fourier estimate
`∫ ⟨t⟩^r ‖γ(t)‖ dt ≤ A_{s,r} ‖h‖_{H^s_ω}` (`eq:sobolev-weighted-l1`), for `0 ≤ r < s - 1/2`. -/
theorem integral_bracket_rpow_norm_le {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s)
    {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    ∫ t : ℝ, (bracket t ^ r : ℝ) * ‖γ t‖ ≤ sobolevMomentConst s r * raySobolevNorm s γ := by
  have hsr : 1 / 2 < s - r := by linarith
  set f : ℝ → ℝ := fun t => bracket t ^ (-(s - r)) with hfdef
  set g : ℝ → ℝ := fun t => bracket t ^ s * ‖γ t‖ with hgdef
  have hsq2 : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ) = x ^ 2 := by
    intro x _
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfsq : ∀ t, f t ^ (2 : ℝ) = ((1 + t ^ 2) ^ (-(s - r)) : ℝ) := by
    intro t
    simp only [hfdef]
    rw [← Real.rpow_mul (bracket_pos t).le, mul_comm, bracket_rpow_two_mul]
  have hgsq : ∀ t, g t ^ (2 : ℝ) = (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
    intro t
    simp only [hgdef]
    rw [Real.mul_rpow (Real.rpow_nonneg (bracket_pos t).le s) (norm_nonneg _),
      ← Real.rpow_mul (bracket_pos t).le, mul_comm s 2, hsq2 _ (norm_nonneg _)]
  have hfg : ∀ t, f t * g t = (bracket t ^ r : ℝ) * ‖γ t‖ := by
    intro t
    simp only [hfdef, hgdef, ← mul_assoc, ← bracket_rpow_add]
    ring_nf
  have hfcont : Continuous f := by
    simp only [hfdef]
    exact continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
  have hw := integrable_one_add_sq_rpow_neg (a := s - r) hsr
  have hf2 : MemLp f 2 volume := by
    refine (memLp_two_iff_integrable_sq hfcont.aestronglyMeasurable).2 ?_
    refine hw.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← hsq2 (f t) (Real.rpow_nonneg (bracket_pos t).le _), hfsq t]
  have hgeq : ∀ t, ‖(bracket t ^ s : ℝ) • γ t‖ = g t := by
    intro t
    simp only [hgdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le s)]
  have hg2 : MemLp g 2 volume :=
    (memLp_congr_ae (Filter.Eventually.of_forall hgeq)).1 hγ.norm
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
    (p := 2) (q := 2) Real.HolderConjugate.two_two (f := f) (g := g)
    (Filter.Eventually.of_forall fun t => Real.rpow_nonneg (bracket_pos t).le _)
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (norm_nonneg _))
    (by simpa using hf2) (by simpa using hg2)
  have hfgint : ∫ t : ℝ, f t * g t = ∫ t : ℝ, (bracket t ^ r : ℝ) * ‖γ t‖ :=
    integral_congr_ae (Filter.Eventually.of_forall hfg)
  have hfint : ∫ t : ℝ, f t ^ (2 : ℝ) = ∫ t : ℝ, ((1 + t ^ 2) ^ (-(s - r)) : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall hfsq)
  have hgint : ∫ t : ℝ, g t ^ (2 : ℝ) =
      ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hgsq)
  rw [hfgint, hfint, hgint] at hholder
  refine hholder.trans (le_of_eq ?_)
  rw [sobolevMomentConst, raySobolevNorm, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  field_simp

/-! ### Reflection and modulation -/

/-- The bracket is even. -/
theorem bracket_neg (t : ℝ) : bracket (-t) = bracket t := by
  simp only [bracket, neg_pow, even_two.neg_pow]

/-- `⟨t - u⟩ ≤ (1 + |u|) ⟨t⟩`. -/
theorem bracket_sub_le (t u : ℝ) : bracket (t - u) ≤ (1 + |u|) * bracket t := by
  have h1 : bracket (t - u) ≤ bracket t + |u| := by
    simp only [bracket, ← Real.sqrt_eq_rpow]
    have habs : |t| ≤ Real.sqrt (1 + t ^ 2) := by
      rw [show |t| = Real.sqrt (t ^ 2) from (Real.sqrt_sq_eq_abs t).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hprod : -(t * u) ≤ Real.sqrt (1 + t ^ 2) * |u| := by
      calc -(t * u) ≤ |t * u| := neg_le_abs _
        _ = |t| * |u| := abs_mul t u
        _ ≤ Real.sqrt (1 + t ^ 2) * |u| := mul_le_mul_of_nonneg_right habs (abs_nonneg u)
    have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    have key : 1 + (t - u) ^ 2 ≤ (Real.sqrt (1 + t ^ 2) + |u|) ^ 2 := by
      nlinarith [sq_abs u, hprod, hs]
    calc Real.sqrt (1 + (t - u) ^ 2) ≤ Real.sqrt ((Real.sqrt (1 + t ^ 2) + |u|) ^ 2) :=
          Real.sqrt_le_sqrt key
      _ = Real.sqrt (1 + t ^ 2) + |u| :=
          Real.sqrt_sq (by positivity)
  have h2 : (1 : ℝ) ≤ bracket t := one_le_bracket t
  nlinarith [abs_nonneg u]

/-- Squared integrands of the Sobolev norm are integrable. -/
theorem integrable_bracket_rpow_norm_sq {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    Integrable (fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) volume := by
  have h := (memLp_two_iff_integrable_sq_norm hγ.aestronglyMeasurable).1 hγ
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le s),
    mul_pow, ← Real.rpow_natCast (bracket t ^ s) 2, ← Real.rpow_mul (bracket_pos t).le,
    mul_comm s]
  norm_num

/-- The Sobolev weight compares the two ends of a translation. -/
theorem bracket_rpow_le_translate {s : ℝ} (hs : 0 ≤ s) (t u : ℝ) :
    bracket t ^ s ≤ (1 + |u|) ^ s * bracket (t + u) ^ s := by
  have h := bracket_sub_le (t + u) u
  rw [add_sub_cancel_right] at h
  calc bracket t ^ s ≤ ((1 + |u|) * bracket (t + u)) ^ s :=
        Real.rpow_le_rpow (bracket_pos t).le h hs
    _ = (1 + |u|) ^ s * bracket (t + u) ^ s :=
        Real.mul_rpow (by positivity) (bracket_pos _).le

/-- Reflection preserves the Sobolev class. -/
theorem memRaySobolev_neg {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    MemRaySobolev s (fun t => γ (-t)) := by
  have h := hγ.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
  simp only [Function.comp_apply, bracket_neg]

/-- Reflection is an isometry of the Sobolev norm. -/
theorem raySobolevNorm_neg (s : ℝ) (γ : ℝ → Y) :
    raySobolevNorm s (fun t => γ (-t)) = raySobolevNorm s γ := by
  unfold raySobolevNorm
  congr 2
  rw [← integral_neg_eq_self fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
    simp only [bracket_neg])

/-- Reflecting the coefficient reflects the profile. -/
theorem rayProfile_neg (γ : ℝ → Y) (ω : ℝ) :
    rayProfile (fun t => γ (-t)) ω = rayProfile γ (-ω) := by
  unfold rayProfile
  rw [← integral_neg_eq_self fun b : ℝ =>
    Complex.exp (((-((-ω) * b) : ℝ) : ℂ) * Complex.I) • γ b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  norm_num

/-- Translating the coefficient modulates the profile. -/
theorem rayProfile_translate (γ : ℝ → Y) (u ω : ℝ) :
    rayProfile (fun t => γ (t + u)) ω =
      Complex.exp (((u * ω : ℝ) : ℂ) * Complex.I) • rayProfile γ ω := by
  unfold rayProfile
  set F : ℝ → Y := fun b => Complex.exp (((-(ω * (b - u)) : ℝ) : ℂ) * Complex.I) • γ b with hF
  have h1 : ∫ b : ℝ, Complex.exp (((-(ω * b) : ℝ) : ℂ) * Complex.I) • γ (b + u) =
      ∫ b : ℝ, F (b + u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [hF, add_sub_cancel_right]
  rw [h1, integral_add_right_eq_self F u, hF, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A ray coefficient of the Sobolev class is measurable. -/
theorem MemRaySobolev.aestronglyMeasurable {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    AEStronglyMeasurable γ volume := by
  have hw : Continuous fun t : ℝ => (bracket t ^ (-s) : ℝ) :=
    continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
  have key : ∀ t : ℝ, (bracket t ^ (-s) : ℝ) • ((bracket t ^ s : ℝ) • γ t) = γ t := by
    intro t
    rw [smul_smul, ← Real.rpow_add (bracket_pos t), neg_add_cancel, Real.rpow_zero, one_smul]
  exact (hw.aestronglyMeasurable.smul (MemLp.aestronglyMeasurable hγ)).congr
    (Filter.Eventually.of_forall key)

/-- Translation of the coefficient stays in the Sobolev class. -/
theorem memRaySobolev_translate {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (u : ℝ) : MemRaySobolev s (fun t => γ (t + u)) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + u) volume volume :=
    measurePreserving_add_right volume u
  have htr : MemLp (fun t => (bracket (t + u) ^ s : ℝ) • γ (t + u)) 2 volume :=
    hγ.comp_measurePreserving hmp
  have hw : Continuous fun t : ℝ => (bracket t ^ s : ℝ) :=
    continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
  have hγtr : AEStronglyMeasurable (fun t : ℝ => γ (t + u)) volume :=
    hγ.aestronglyMeasurable.comp_measurePreserving hmp
  have hg : MemLp
      (fun t : ℝ => ((1 + |u|) ^ s : ℝ) • ((bracket (t + u) ^ s : ℝ) • γ (t + u))) 2 volume :=
    htr.const_smul ((1 + |u|) ^ s : ℝ)
  refine MemLp.mono hg (hw.aestronglyMeasurable.smul hγtr)
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (bracket_pos _).le s),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |u|) s), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bracket_rpow_le_translate hs t u) (norm_nonneg _)

/-- **Lemma [lem:sobolev-tools]**, the modulation bound
`‖M_u h‖_{H^s_ω} ≤ (1 + |u|)^s ‖h‖_{H^s_ω}` (`eq:sobolev-modulation`). -/
theorem raySobolevNorm_translate_le {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (u : ℝ) :
    raySobolevNorm s (fun t => γ (t + u)) ≤ (1 + |u|) ^ s * raySobolevNorm s γ := by
  have hu0 : (0 : ℝ) ≤ 1 + |u| := by positivity
  have hI : Integrable (fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) volume :=
    integrable_bracket_rpow_norm_sq hγ
  have hItr : Integrable
      (fun t : ℝ => (bracket (t + u) ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2) volume :=
    hI.comp_add_right u
  have hbound : ∀ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2 ≤
      ((1 + |u|) ^ (2 * s) : ℝ) * ((bracket (t + u) ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2) := by
    intro t
    have hb : (bracket t ^ (2 * s) : ℝ) ≤ ((1 + |u|) ^ (2 * s) : ℝ) * bracket (t + u) ^ (2 * s) :=
      bracket_rpow_le_translate (by linarith) t u
    calc (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2
        ≤ (((1 + |u|) ^ (2 * s) : ℝ) * bracket (t + u) ^ (2 * s)) * ‖γ (t + u)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hIlhs : Integrable (fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2) volume := by
    refine Integrable.mono' (hItr.const_mul ((1 + |u|) ^ (2 * s) : ℝ)) ?_
      (Filter.Eventually.of_forall fun t => ?_)
    · have hw : Continuous fun t : ℝ => (bracket t ^ (2 * s) : ℝ) :=
        continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
      exact hw.aestronglyMeasurable.mul
        ((memRaySobolev_translate hs hγ u).aestronglyMeasurable.norm.pow 2)
    · rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (by positivity))]
      exact hbound t
  have hmono : ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2 ≤
      ((1 + |u|) ^ (2 * s) : ℝ) * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
    calc ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2
        ≤ ∫ t : ℝ, ((1 + |u|) ^ (2 * s) : ℝ) *
            ((bracket (t + u) ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2) :=
          integral_mono hIlhs (hItr.const_mul _) hbound
      _ = ((1 + |u|) ^ (2 * s) : ℝ) *
            ∫ t : ℝ, (bracket (t + u) ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2 := integral_const_mul _ _
      _ = ((1 + |u|) ^ (2 * s) : ℝ) * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
          rw [integral_add_right_eq_self
            (fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) u]
  have hsqrt : ((1 + |u|) ^ (2 * s) : ℝ) = ((1 + |u|) ^ s : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + |u|) ^ s) 2, ← Real.rpow_mul hu0, mul_comm s]
    norm_num
  unfold raySobolevNorm
  rw [show ((1 + |u|) ^ s : ℝ) = Real.sqrt (((1 + |u|) ^ s : ℝ) ^ 2) from
    (Real.sqrt_sq (Real.rpow_nonneg hu0 s)).symm, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [← hsqrt]
  calc 2 * Real.pi * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + u)‖ ^ 2
      ≤ 2 * Real.pi * (((1 + |u|) ^ (2 * s) : ℝ) *
          ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((1 + |u|) ^ (2 * s) : ℝ) *
          (2 * Real.pi * ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2) := by ring

/-! ### The Sobolev norm as an `L²` norm -/

/-- The Sobolev norm is `√(2π)` times the `L²` norm of the weighted coefficient. -/
theorem raySobolevNorm_eq_sqrt_mul_norm_toLp {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    raySobolevNorm s γ =
      Real.sqrt (2 * Real.pi) * ‖MemLp.toLp (fun t => (bracket t ^ s : ℝ) • γ t) hγ‖ := by
  have hsq : ‖MemLp.toLp (fun t => (bracket t ^ s : ℝ) • γ t) hγ‖ ^ 2 =
      ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ t‖ ^ 2 := by
    rw [MemLp.norm_toLp_two_sq hγ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le s),
      mul_pow, ← Real.rpow_natCast (bracket t ^ s) 2, ← Real.rpow_mul (bracket_pos t).le,
      mul_comm s]
    norm_num
  rw [raySobolevNorm, ← hsq, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg _)]

/-- The Sobolev norm obeys the triangle inequality. -/
theorem raySobolevNorm_add_le {s : ℝ} {γ δ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (hδ : MemRaySobolev s δ) :
    raySobolevNorm s (fun t => γ t + δ t) ≤ raySobolevNorm s γ + raySobolevNorm s δ := by
  have hsum : MemRaySobolev s (fun t => γ t + δ t) := by
    have h := hγ.add hδ
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
    simp only [Pi.add_apply, smul_add]
  have heq : MemLp.toLp (fun t => (bracket t ^ s : ℝ) • (γ t + δ t)) hsum =
      MemLp.toLp (fun t => (bracket t ^ s : ℝ) • γ t) hγ +
        MemLp.toLp (fun t => (bracket t ^ s : ℝ) • δ t) hδ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, smul_add]
  rw [raySobolevNorm_eq_sqrt_mul_norm_toLp hsum, raySobolevNorm_eq_sqrt_mul_norm_toLp hγ,
    raySobolevNorm_eq_sqrt_mul_norm_toLp hδ, heq, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

/-! ### Strong continuity of translation -/

/-- The Sobolev weight ratio of a translation is bounded by `(1 + |v|)^s`. -/
theorem bracket_rpow_div_le {s : ℝ} (hs : 0 ≤ s) (t v : ℝ) :
    bracket t ^ s / bracket (t + v) ^ s ≤ (1 + |v|) ^ s := by
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (bracket_pos _) s)]
  exact bracket_rpow_le_translate hs t v

/-- The Sobolev weight ratio of a translation is nonnegative. -/
theorem bracket_rpow_div_nonneg (s t v : ℝ) : 0 ≤ bracket t ^ s / bracket (t + v) ^ s :=
  div_nonneg (Real.rpow_nonneg (bracket_pos t).le s) (Real.rpow_nonneg (bracket_pos _).le s)

/-- The multiplier of the translated Sobolev weight tends to one. -/
theorem tendsto_bracket_rpow_div (s t : ℝ) :
    Filter.Tendsto (fun v : ℝ => bracket t ^ s / bracket (t + v) ^ s) (nhds 0) (nhds 1) := by
  have h1 : Filter.Tendsto (fun v : ℝ => bracket (t + v)) (nhds 0) (nhds (bracket t)) := by
    have hc : Continuous fun v : ℝ => bracket (t + v) :=
      continuous_bracket.comp (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  have h2 : Filter.Tendsto (fun v : ℝ => bracket (t + v) ^ s) (nhds 0) (nhds (bracket t ^ s)) :=
    ((Real.continuousAt_rpow_const _ s (Or.inl (bracket_pos t).ne')).tendsto).comp h1
  have hconst : Filter.Tendsto (fun _ : ℝ => (bracket t ^ s : ℝ)) (nhds 0)
      (nhds (bracket t ^ s)) := tendsto_const_nhds
  have h3 := hconst.div h2 (Real.rpow_pos_of_pos (bracket_pos t) s).ne'
  rwa [div_self (Real.rpow_pos_of_pos (bracket_pos t) s).ne'] at h3

/-- The multiplier error of the translated Sobolev weight tends to zero in `L²`. -/
theorem tendsto_integral_bracket_div_sub_one_sq {s : ℝ} (hs : 0 ≤ s) {F : ℝ → Y}
    (hF : MemLp F 2 (volume : Measure ℝ)) :
    Filter.Tendsto
      (fun v : ℝ => ∫ t : ℝ, ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2)
      (nhds 0) (nhds 0) := by
  have hFsq : Integrable (fun t : ℝ => ‖F t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have hbound : Integrable (fun t : ℝ => (((2 : ℝ) ^ s + 1) ^ 2) * ‖F t‖ ^ 2) volume :=
    hFsq.const_mul _
  have hmeas : ∀ v : ℝ, AEStronglyMeasurable
      (fun t : ℝ => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2) volume := by
    intro v
    have hb : Continuous fun t : ℝ => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) := by
      have h1 : Continuous fun t : ℝ => (bracket t ^ s : ℝ) :=
        continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
      have h2 : Continuous fun t : ℝ => (bracket (t + v) ^ s : ℝ) :=
        (continuous_bracket.comp (continuous_id.add continuous_const)).rpow_const fun t =>
          Or.inl (bracket_pos _).ne'
      exact ((h1.div h2 fun t => (Real.rpow_pos_of_pos (bracket_pos _) s).ne').sub
        continuous_const).pow 2
    exact hb.aestronglyMeasurable.mul (hF.aestronglyMeasurable.norm.pow 2)
  have hev : ∀ᶠ v : ℝ in nhds 0, ∀ᵐ t : ℝ,
      ‖((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2‖ ≤
        (((2 : ℝ) ^ s + 1) ^ 2) * ‖F t‖ ^ 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with v hv
    have hv1 : |v| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
      exact hv.le
    filter_upwards with t
    have hq0 := bracket_rpow_div_nonneg s t v
    have hq1 : bracket t ^ s / bracket (t + v) ^ s ≤ (2 : ℝ) ^ s := by
      refine (bracket_rpow_div_le hs t v).trans ?_
      exact Real.rpow_le_rpow (by positivity) (by linarith) hs
    have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs
    have habs : |bracket t ^ s / bracket (t + v) ^ s - 1| ≤ (2 : ℝ) ^ s + 1 := by
      rw [abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ)
        = |bracket t ^ s / bracket (t + v) ^ s - 1| ^ 2 := (sq_abs _).symm
      _ ≤ ((2 : ℝ) ^ s + 1) ^ 2 := by
          refine pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hlim : ∀ᵐ t : ℝ, Filter.Tendsto
      (fun v : ℝ => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2)
      (nhds 0) (nhds 0) := by
    filter_upwards with t
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) := tendsto_const_nhds
    have hsub : Filter.Tendsto
        (fun v : ℝ => bracket t ^ s / bracket (t + v) ^ s - 1) (nhds 0) (nhds 0) := by
      simpa using (tendsto_bracket_rpow_div s t).sub hone
    have hFc : Filter.Tendsto (fun _ : ℝ => ‖F t‖ ^ 2) (nhds 0) (nhds (‖F t‖ ^ 2)) :=
      tendsto_const_nhds
    simpa using (hsub.pow 2).mul hFc
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := nhds (0 : ℝ))
    (F := fun v t => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2)
    (f := fun _ : ℝ => (0 : ℝ)) (bound := fun t => (((2 : ℝ) ^ s + 1) ^ 2) * ‖F t‖ ^ 2)
    (Filter.Eventually.of_forall hmeas) hev hbound hlim
  simpa using h

/-- The difference of a translate and the original stays in the Sobolev class. -/
theorem memRaySobolev_translate_sub {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (v : ℝ) : MemRaySobolev s (fun t => γ (t + v) - γ t) := by
  have h := (memRaySobolev_translate hs hγ v).sub hγ
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
  simp only [Pi.sub_apply, smul_sub]

/-- **Lemma [lem:sobolev-tools]**, strong continuity of modulation: the Sobolev norm of
`M_v h - h` tends to zero with `v`. -/
theorem tendsto_raySobolevNorm_translate_sub {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) :
    Filter.Tendsto (fun v : ℝ => raySobolevNorm s (fun t => γ (t + v) - γ t))
      (nhds 0) (nhds 0) := by
  set F : ℝ → Y := fun t => (bracket t ^ s : ℝ) • γ t with hFdef
  have hF : MemLp F 2 (volume : Measure ℝ) := hγ
  have hFsq : Integrable (fun t : ℝ => ‖F t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  set A : ℝ → ℝ := fun v => ∫ t : ℝ, ‖F (t + v) - F t‖ ^ 2 with hAdef
  set B : ℝ → ℝ :=
    fun v => ∫ t : ℝ, ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2 with hBdef
  set Q : ℝ → ℝ := fun v => ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + v) - γ t‖ ^ 2 with hQdef
  -- the pointwise decomposition
  have hpt : ∀ v t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (t + v) - γ t‖ ^ 2 ≤
      2 * ((1 + |v|) ^ (2 * s) : ℝ) * ‖F (t + v) - F t‖ ^ 2 +
        2 * (((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2) := by
    intro v t
    set c : ℝ := bracket t ^ s / bracket (t + v) ^ s with hcdef
    have hc0 : 0 ≤ c := bracket_rpow_div_nonneg s t v
    have hcF : c • F (t + v) = (bracket t ^ s : ℝ) • γ (t + v) := by
      simp only [hFdef, hcdef, smul_smul, div_mul_cancel₀ _
        (Real.rpow_pos_of_pos (bracket_pos (t + v)) s).ne']
    have hsplit : (bracket t ^ s : ℝ) • (γ (t + v) - γ t) =
        c • (F (t + v) - F t) + (c - 1) • F t := by
      rw [smul_sub, smul_sub, sub_smul, one_smul, hcF]
      simp only [hFdef]
      abel
    have hnorm : ‖(bracket t ^ s : ℝ) • (γ (t + v) - γ t)‖ ≤
        c * ‖F (t + v) - F t‖ + |c - 1| * ‖F t‖ := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0]
    have hlhs : (bracket t ^ (2 * s) : ℝ) * ‖γ (t + v) - γ t‖ ^ 2 =
        ‖(bracket t ^ s : ℝ) • (γ (t + v) - γ t)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le s),
        mul_pow, ← Real.rpow_natCast (bracket t ^ s) 2, ← Real.rpow_mul (bracket_pos t).le,
        mul_comm s]
      norm_num
    have hcle : c ≤ ((1 + |v|) ^ s : ℝ) := bracket_rpow_div_le hs t v
    have hcsq : c ^ 2 ≤ ((1 + |v|) ^ (2 * s) : ℝ) := by
      have h2 : ((1 + |v|) ^ (2 * s) : ℝ) = (((1 + |v|) ^ s : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast ((1 + |v|) ^ s) 2, ← Real.rpow_mul (by positivity), mul_comm s]
        norm_num
      rw [h2]
      exact pow_le_pow_left₀ hc0 hcle 2
    rw [hlhs]
    have hsq : ‖(bracket t ^ s : ℝ) • (γ (t + v) - γ t)‖ ^ 2 ≤
        (c * ‖F (t + v) - F t‖ + |c - 1| * ‖F t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    refine hsq.trans ?_
    have hexp : (c * ‖F (t + v) - F t‖ + |c - 1| * ‖F t‖) ^ 2 ≤
        2 * (c ^ 2 * ‖F (t + v) - F t‖ ^ 2) + 2 * ((c - 1) ^ 2 * ‖F t‖ ^ 2) := by
      have h := sq_nonneg (c * ‖F (t + v) - F t‖ - |c - 1| * ‖F t‖)
      have habs : |c - 1| ^ 2 = (c - 1) ^ 2 := sq_abs _
      nlinarith [habs]
    refine hexp.trans ?_
    have h1 : c ^ 2 * ‖F (t + v) - F t‖ ^ 2 ≤
        ((1 + |v|) ^ (2 * s) : ℝ) * ‖F (t + v) - F t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcsq (by positivity)
    nlinarith [h1]
  -- integrability on both sides
  have hQint : ∀ v : ℝ, Integrable
      (fun t : ℝ => (bracket t ^ (2 * s) : ℝ) * ‖γ (t + v) - γ t‖ ^ 2) volume := fun v =>
    integrable_bracket_rpow_norm_sq (memRaySobolev_translate_sub hs hγ v)
  have hAint : ∀ v : ℝ, Integrable (fun t : ℝ => ‖F (t + v) - F t‖ ^ 2) volume := by
    intro v
    have h := (memRaySobolev_translate_sub hs hγ v)
    have h2 : MemLp (fun t : ℝ => F (t + v) - F t) 2 volume := by
      have h3 : MemLp (fun t : ℝ => F (t + v)) 2 volume :=
        hF.comp_measurePreserving (measurePreserving_add_right volume v)
      exact h3.sub hF
    exact (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
  have hBint : ∀ v : ℝ, Integrable
      (fun t : ℝ => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2) volume := by
    intro v
    have hb : Continuous fun t : ℝ => ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) := by
      have h1 : Continuous fun t : ℝ => (bracket t ^ s : ℝ) :=
        continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
      have h2 : Continuous fun t : ℝ => (bracket (t + v) ^ s : ℝ) :=
        (continuous_bracket.comp (continuous_id.add continuous_const)).rpow_const fun t =>
          Or.inl (bracket_pos _).ne'
      exact ((h1.div h2 fun t => (Real.rpow_pos_of_pos (bracket_pos _) s).ne').sub
        continuous_const).pow 2
    refine Integrable.mono' (hFsq.const_mul ((((1 + |v|) ^ s : ℝ) + 1) ^ 2))
      (hb.aestronglyMeasurable.mul (hF.aestronglyMeasurable.norm.pow 2))
      (Filter.Eventually.of_forall fun t => ?_)
    have hc0 := bracket_rpow_div_nonneg s t v
    have hcle := bracket_rpow_div_le hs t v
    have h1s : (1 : ℝ) ≤ ((1 + |v|) ^ s : ℝ) :=
      Real.one_le_rpow (by simp [abs_nonneg]) hs
    have habs : |bracket t ^ s / bracket (t + v) ^ s - 1| ≤ ((1 + |v|) ^ s : ℝ) + 1 := by
      rw [abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ)
        = |bracket t ^ s / bracket (t + v) ^ s - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (((1 + |v|) ^ s : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- the squeeze
  have hQle : ∀ v : ℝ, Q v ≤ 2 * ((1 + |v|) ^ (2 * s) : ℝ) * A v + 2 * B v := by
    intro v
    have h := integral_mono (hQint v)
      (((hAint v).const_mul (2 * ((1 + |v|) ^ (2 * s) : ℝ))).add ((hBint v).const_mul 2))
      (hpt v)
    calc Q v ≤ ∫ t : ℝ, (2 * ((1 + |v|) ^ (2 * s) : ℝ) * ‖F (t + v) - F t‖ ^ 2 +
            2 * (((bracket t ^ s / bracket (t + v) ^ s - 1) ^ 2 : ℝ) * ‖F t‖ ^ 2)) := h
      _ = 2 * ((1 + |v|) ^ (2 * s) : ℝ) * A v + 2 * B v := by
          rw [integral_add ((hAint v).const_mul _) ((hBint v).const_mul 2), integral_const_mul,
            integral_const_mul]
  have hQ0 : ∀ v : ℝ, 0 ≤ Q v :=
    fun v => integral_nonneg fun t =>
      mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (by positivity)
  have hA0 : Filter.Tendsto A (nhds 0) (nhds 0) := tendsto_integral_norm_translate_sub_sq hF
  have hB0 : Filter.Tendsto B (nhds 0) (nhds 0) :=
    tendsto_integral_bracket_div_sub_one_sq hs hF
  have hcoef : Filter.Tendsto (fun v : ℝ => 2 * ((1 + |v|) ^ (2 * s) : ℝ)) (nhds 0) (nhds 2) := by
    have hc : ContinuousAt (fun v : ℝ => 2 * ((1 + |v|) ^ (2 * s) : ℝ)) 0 := by
      refine ContinuousAt.mul continuousAt_const ?_
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))).comp
        (continuousAt_const.add continuous_abs.continuousAt)
    have := hc.tendsto
    simpa using this
  have hg : Filter.Tendsto (fun v : ℝ => 2 * ((1 + |v|) ^ (2 * s) : ℝ) * A v + 2 * B v)
      (nhds 0) (nhds 0) := by
    have h1 := hcoef.mul hA0
    have h2 := hB0.const_mul 2
    simpa using h1.add h2
  have hQlim : Filter.Tendsto Q (nhds 0) (nhds 0) :=
    squeeze_zero hQ0 hQle hg
  have hmul : Filter.Tendsto (fun v : ℝ => 2 * Real.pi * Q v) (nhds 0) (nhds 0) := by
    simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => 2 * Real.pi) (nhds 0)
      (nhds (2 * Real.pi))).mul hQlim
  have hcomp := (Real.continuous_sqrt.tendsto 0).comp hmul
  simp only [Function.comp_def, Real.sqrt_zero] at hcomp
  simpa only [raySobolevNorm, hQdef] using hcomp

/-- The Sobolev norm is nonnegative. -/
theorem raySobolevNorm_nonneg (s : ℝ) (γ : ℝ → Y) : 0 ≤ raySobolevNorm s γ :=
  Real.sqrt_nonneg _

/-- **Lemma [lem:sobolev-tools]**, joint continuity of modulation: if the biases converge and
the profiles converge in `H^s_ω`, then the modulated profiles converge. -/
theorem tendsto_raySobolevNorm_modulation {S : Type*} {l : Filter S} {s : ℝ} (hs : 0 ≤ s)
    {γ : ℝ → Y} {γ' : S → ℝ → Y} {u : S → ℝ} {u₀ : ℝ}
    (hγ : MemRaySobolev s γ) (hγ' : ∀ i, MemRaySobolev s (γ' i))
    (hu : Filter.Tendsto u l (nhds u₀))
    (hconv : Filter.Tendsto (fun i => raySobolevNorm s (fun t => γ' i t - γ t)) l (nhds 0)) :
    Filter.Tendsto (fun i => raySobolevNorm s (fun t => γ' i (t + u i) - γ (t + u₀)))
      l (nhds 0) := by
  have hdiff : ∀ i, MemRaySobolev s (fun t => γ' i t - γ t) := by
    intro i
    have h := (hγ' i).sub hγ
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
    simp only [Pi.sub_apply, smul_sub]
  have hstep : ∀ i, raySobolevNorm s (fun t => γ' i (t + u i) - γ (t + u₀)) ≤
      ((1 + |u i|) ^ s : ℝ) * raySobolevNorm s (fun t => γ' i t - γ t) +
        ((1 + |u₀|) ^ s : ℝ) *
          raySobolevNorm s (fun t => γ (t + (u i - u₀)) - γ t) := by
    intro i
    have hA : MemRaySobolev s (fun t => (fun r => γ' i r - γ r) (t + u i)) :=
      memRaySobolev_translate hs (hdiff i) (u i)
    have hB : MemRaySobolev s
        (fun t => (fun r => γ (r + (u i - u₀)) - γ r) (t + u₀)) :=
      memRaySobolev_translate hs (memRaySobolev_translate_sub hs hγ (u i - u₀)) u₀
    have hsplit : ∀ t : ℝ, γ' i (t + u i) - γ (t + u₀) =
        ((fun r => γ' i r - γ r) (t + u i)) +
          ((fun r => γ (r + (u i - u₀)) - γ r) (t + u₀)) := by
      intro t
      simp only
      rw [show t + u₀ + (u i - u₀) = t + u i by ring]
      abel
    calc raySobolevNorm s (fun t => γ' i (t + u i) - γ (t + u₀))
        = raySobolevNorm s (fun t => ((fun r => γ' i r - γ r) (t + u i)) +
            ((fun r => γ (r + (u i - u₀)) - γ r) (t + u₀))) := by
          exact congrArg (raySobolevNorm s) (funext hsplit)
      _ ≤ raySobolevNorm s (fun t => (fun r => γ' i r - γ r) (t + u i)) +
            raySobolevNorm s (fun t => (fun r => γ (r + (u i - u₀)) - γ r) (t + u₀)) :=
          raySobolevNorm_add_le hA hB
      _ ≤ ((1 + |u i|) ^ s : ℝ) * raySobolevNorm s (fun t => γ' i t - γ t) +
            ((1 + |u₀|) ^ s : ℝ) *
              raySobolevNorm s (fun t => γ (t + (u i - u₀)) - γ t) :=
          add_le_add (raySobolevNorm_translate_le hs (hdiff i) (u i))
            (raySobolevNorm_translate_le hs (memRaySobolev_translate_sub hs hγ (u i - u₀)) u₀)
  have hcoef : Filter.Tendsto (fun i => ((1 + |u i|) ^ s : ℝ)) l (nhds ((1 + |u₀|) ^ s)) := by
    have hc : ContinuousAt (fun x : ℝ => ((1 + |x|) ^ s : ℝ)) u₀ :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))).comp
        (continuousAt_const.add continuous_abs.continuousAt)
    exact hc.tendsto.comp hu
  have hv : Filter.Tendsto (fun i => u i - u₀) l (nhds 0) := by
    simpa using hu.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : S => u₀) l (nhds u₀))
  have hsecond : Filter.Tendsto
      (fun i => raySobolevNorm s (fun t => γ (t + (u i - u₀)) - γ t)) l (nhds 0) :=
    (tendsto_raySobolevNorm_translate_sub hs hγ).comp hv
  have hbound : Filter.Tendsto
      (fun i => ((1 + |u i|) ^ s : ℝ) * raySobolevNorm s (fun t => γ' i t - γ t) +
        ((1 + |u₀|) ^ s : ℝ) * raySobolevNorm s (fun t => γ (t + (u i - u₀)) - γ t))
      l (nhds 0) := by
    have h1 := hcoef.mul hconv
    have h2 := hsecond.const_mul ((1 + |u₀|) ^ s : ℝ)
    simpa using h1.add h2
  exact squeeze_zero (fun i => raySobolevNorm_nonneg _ _) hstep hbound

end OperatorRidgelet
