import OperatorRidgelet.Sobolev.Basic
import OperatorRidgelet.ToMathlib.IntegralCauchySchwarz

/-!
# The bilinear Sobolev pairing

The pairing `L_σ^Y(h) = ∫ σ(t) γ(-t) dt` of Lemma `lem:sobolev-pairing`, where `γ = ȟ` is the
coefficient of the profile `h`.  For an activation of polynomial growth `p` and `s > p + 1/2`
the weighted activation `⟨·⟩^{-s} σ` is square integrable, the pairing integral converges
absolutely with `‖L_σ^Y(h)‖ ≤ (2π)^{-1/2} b_{σ,s} ‖h‖_{H^s_ω}`, and the bias translation of the
activation is the modulation of the profile (`eq:sobolev-bias-pairing`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- `1 + |t| ≤ √2 ⟨t⟩`. -/
theorem one_add_abs_le_sqrt_two_mul_bracket (t : ℝ) : 1 + |t| ≤ Real.sqrt 2 * bracket t := by
  have h1 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_abs t, sq_nonneg (1 - |t|), abs_nonneg t]
  have h2 : Real.sqrt 2 * bracket t = Real.sqrt (2 * (1 + t ^ 2)) := by
    rw [bracket, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
  rw [h2]
  have h3 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h3

/-- The weighted activation of an activation of polynomial growth `p` is square integrable for
`s > p + 1/2`: the constant `b_{σ,s}` of Lemma `lem:sobolev-pairing` is finite. -/
theorem memLp_bracket_rpow_neg_smul {σ : ℝ → ℂ} {p s C : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    (hσ : Continuous σ) (hbound : ∀ t : ℝ, ‖σ t‖ ≤ C * (1 + |t|) ^ p) :
    MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume := by
  have hC : 0 ≤ C := by
    have h := hbound 0
    simpa using le_trans (norm_nonneg (σ 0)) h
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) volume := by
    have hw : Continuous fun t : ℝ => (bracket t ^ (-s) : ℝ) :=
      continuous_bracket.rpow_const fun t => Or.inl (bracket_pos t).ne'
    exact (hw.smul hσ).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hdom : Integrable
      (fun t : ℝ => (C * Real.sqrt 2 ^ p) ^ 2 * ((1 + t ^ 2) ^ (-(s - p)) : ℝ)) volume :=
    (integrable_one_add_sq_rpow_neg (a := s - p) (by linarith)).const_mul _
  refine Integrable.mono' hdom (hmeas.norm.pow 2) (Filter.Eventually.of_forall fun t => ?_)
  have hb : ‖(bracket t ^ (-s) : ℝ) • σ t‖ ≤ (C * Real.sqrt 2 ^ p) * bracket t ^ (p - s) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le _)]
    have h1 : ‖σ t‖ ≤ C * (Real.sqrt 2 ^ p * bracket t ^ p) := by
      refine (hbound t).trans ?_
      have h2 : ((1 + |t|) ^ p : ℝ) ≤ (Real.sqrt 2 * bracket t) ^ p :=
        Real.rpow_le_rpow (by positivity) (one_add_abs_le_sqrt_two_mul_bracket t) hp
      rw [Real.mul_rpow (by positivity) (bracket_pos t).le] at h2
      exact mul_le_mul_of_nonneg_left h2 hC
    calc bracket t ^ (-s) * ‖σ t‖
        ≤ bracket t ^ (-s) * (C * (Real.sqrt 2 ^ p * bracket t ^ p)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (bracket_pos t).le _)
      _ = (C * Real.sqrt 2 ^ p) * (bracket t ^ (-s) * bracket t ^ p) := by ring
      _ = (C * Real.sqrt 2 ^ p) * bracket t ^ (p - s) := by
          rw [← bracket_rpow_add]
          ring_nf
  have hsq : ‖(bracket t ^ (-s) : ℝ) • σ t‖ ^ 2 ≤
      (C * Real.sqrt 2 ^ p) ^ 2 * ((1 + t ^ 2) ^ (-(s - p)) : ℝ) := by
    have h3 : ‖(bracket t ^ (-s) : ℝ) • σ t‖ ^ 2 ≤
        ((C * Real.sqrt 2 ^ p) * bracket t ^ (p - s)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    refine h3.trans (le_of_eq ?_)
    rw [mul_pow, bracket_rpow_sq]
    congr 2
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hsq

/-- The pairing integral converges absolutely. -/
theorem integrable_smul_neg {σ : ℝ → ℂ} {s : ℝ} {γ : ℝ → Y}
    (hσ : MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume)
    (hγ : MemRaySobolev s γ) :
    Integrable (fun t : ℝ => σ t • γ (-t)) volume := by
  have hneg : MemLp (fun t : ℝ => (bracket t ^ s : ℝ) • γ (-t)) 2 volume := memRaySobolev_neg hγ
  have h := hneg.smul (𝕜 := ℂ) (p := 2) (q := 2) (r := 1) hσ
  refine (memLp_one_iff_integrable.1 ?_)
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun t => ?_)).1 h
  show ((bracket t ^ (-s) : ℝ) • σ t) • ((bracket t ^ s : ℝ) • γ (-t)) = σ t • γ (-t)
  rw [smul_assoc, smul_comm (σ t) ((bracket t ^ s : ℝ)), smul_smul,
    ← Real.rpow_add (bracket_pos t)]
  norm_num

/-- **Lemma [lem:sobolev-pairing]** the pairing bound
`‖L_σ^Y(h)‖ ≤ (2π)^{-1/2} b_{σ,s} ‖h‖_{H^s_ω}`. -/
theorem norm_sobolevPairing_le {σ : ℝ → ℂ} {s : ℝ} {γ : ℝ → Y}
    (hσ : MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume)
    (hγ : MemRaySobolev s γ) :
    ‖sobolevPairing σ γ‖ ≤
      sobolevPairingConst σ s / Real.sqrt (2 * Real.pi) * raySobolevNorm s γ := by
  have hneg : MemRaySobolev s (fun t => γ (-t)) := memRaySobolev_neg hγ
  set f : ℝ → ℝ := fun t => (bracket t ^ (-s) : ℝ) * ‖σ t‖ with hfdef
  set g : ℝ → ℝ := fun t => (bracket t ^ s : ℝ) * ‖γ (-t)‖ with hgdef
  have hfeq : ∀ t : ℝ, ‖(bracket t ^ (-s) : ℝ) • σ t‖ = f t := by
    intro t
    rw [hfdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le _)]
  have hgeq : ∀ t : ℝ, ‖(bracket t ^ s : ℝ) • γ (-t)‖ = g t := by
    intro t
    rw [hgdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (bracket_pos t).le _)]
  have hfL : MemLp f 2 volume :=
    (memLp_congr_ae (Filter.Eventually.of_forall hfeq)).1 hσ.norm
  have hgL : MemLp g 2 volume :=
    (memLp_congr_ae (Filter.Eventually.of_forall hgeq)).1 (MemLp.norm hneg)
  have hprod : ∀ t : ℝ, ‖σ t • γ (-t)‖ = f t * g t := by
    intro t
    rw [hfdef, hgdef, norm_smul]
    calc ‖σ t‖ * ‖γ (-t)‖
        = (bracket t ^ (-s) * bracket t ^ s) * (‖σ t‖ * ‖γ (-t)‖) := by
          rw [← bracket_rpow_add]
          norm_num
      _ = bracket t ^ (-s) * ‖σ t‖ * (bracket t ^ s * ‖γ (-t)‖) := by ring
  have hCS := integral_mul_le_sqrt_mul_sqrt (μ := (volume : Measure ℝ))
    (Filter.Eventually.of_forall fun t => by
      rw [hfdef]; exact mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (norm_nonneg _))
    (Filter.Eventually.of_forall fun t => by
      rw [hgdef]; exact mul_nonneg (Real.rpow_nonneg (bracket_pos t).le _) (norm_nonneg _))
    hfL hgL
  have hb : sobolevPairingConst σ s = Real.sqrt (∫ t : ℝ, f t ^ 2) := by
    rw [sobolevPairingConst]
    exact congrArg Real.sqrt (integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only
      rw [hfeq t]))
  have hgint : Real.sqrt (∫ t : ℝ, g t ^ 2) = raySobolevNorm s γ / Real.sqrt (2 * Real.pi) := by
    have hQ : ∫ t : ℝ, g t ^ 2 = ∫ t : ℝ, (bracket t ^ (2 * s) : ℝ) * ‖γ (-t)‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hgdef]
      rw [mul_pow, ← Real.rpow_natCast (bracket t ^ s) 2,
        ← Real.rpow_mul (bracket_pos t).le, mul_comm s]
      push_cast
      rfl
    rw [hQ, ← raySobolevNorm_neg s γ, raySobolevNorm, Real.sqrt_mul (by positivity)]
    field_simp
  calc ‖sobolevPairing σ γ‖
      ≤ ∫ t : ℝ, ‖σ t • γ (-t)‖ := norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, f t * g t := integral_congr_ae (Filter.Eventually.of_forall hprod)
    _ ≤ Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) := hCS
    _ = sobolevPairingConst σ s / Real.sqrt (2 * Real.pi) * raySobolevNorm s γ := by
        rw [hb, hgint]
        ring

/-- **Lemma [lem:sobolev-pairing]** the translation formula
`∫ σ(u - b) γ(b) db = L_σ^Y(M_u h)` (`eq:sobolev-bias-pairing`). -/
theorem integral_smul_sub_eq_sobolevPairing_translate (σ : ℝ → ℂ) (γ : ℝ → Y) (u : ℝ) :
    ∫ b : ℝ, σ (u - b) • γ b = sobolevPairing σ (fun t => γ (t + u)) := by
  rw [sobolevPairing, ← integral_sub_left_eq_self (fun b : ℝ => σ (u - b) • γ b) volume u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [sub_sub_cancel, show u - t = -t + u by ring]

end OperatorRidgelet
