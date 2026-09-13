import OperatorRidgelet.Sobolev.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

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

end OperatorRidgelet
