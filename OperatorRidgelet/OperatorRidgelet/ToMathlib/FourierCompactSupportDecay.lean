import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Decay of the Fourier integral of a compactly supported smooth function

For a smooth compactly supported `f : ℝ → E` with values in a complex normed space the Fourier
integral `c ↦ ∫ e^{iωc} f(ω) dω` decays faster than every power of `c`, with the explicit bound
`|c|^n ‖∫ e^{iωc} f(ω) dω‖ ≤ ∫ ‖∂_ω^n f(ω)‖ dω`,
which is `n`-fold integration by parts.  The proof reads the integral as Mathlib's Fourier
integral `𝓕 f` at `-(2π)^{-1} c` and applies `Real.fourier_iteratedDeriv`.

The auxiliary facts that every iterated derivative of a compactly supported function has compact
support, and is therefore integrable when the function is smooth, are recorded first.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Real Filter

open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated derivative of a compactly supported function has compact support. -/
theorem hasCompactSupport_iteratedDeriv {f : ℝ → E} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  refine (hf.iteratedFDeriv (𝕜 := ℝ) n).of_isClosed_subset isClosed_closure (closure_mono ?_)
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro h
  exact hx (by rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h, norm_zero])

/-- Every derivative of a smooth compactly supported function is integrable. -/
theorem integrable_iteratedDeriv_of_hasCompactSupport {f : ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f) (n : ℕ) :
    Integrable (iteratedDeriv n f) :=
  (hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hsupp n)

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Decay of a compactly supported smooth Fourier integral.**  In the convention
`∫ e^{iωc} f(ω) dω`, `n`-fold integration by parts gives
`|c|^n ‖∫ e^{iωc} f(ω) dω‖ ≤ ∫ ‖∂_ω^n f(ω)‖ dω`. -/
theorem norm_integral_exp_mul_I_smul_le {f : ℝ → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (n : ℕ) (c : ℝ) :
    |c| ^ n * ‖∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • f ω‖ ≤
      ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  set w : ℝ := -((2 * Real.pi)⁻¹ * c) with hw
  have hw2 : 2 * Real.pi * w = -c := by
    rw [hw, mul_neg, ← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
  have hFT : ∀ g : ℝ → F,
      𝓕 g w = ∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • g ω := by
    intro g
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    beta_reduce
    have harg : (-2 * Real.pi * v * w : ℝ) = v * c := by linear_combination (-v) * hw2
    rw [harg]
  have hint : ∀ m : ℕ, Integrable (iteratedDeriv m f) := fun m =>
    integrable_iteratedDeriv_of_hasCompactSupport hf hsupp m
  have hd := congrFun (Real.fourier_iteratedDeriv (E := F) (N := (⊤ : ℕ∞)) (n := n) hf
    (fun m _ => hint m) le_top) w
  have hb : ‖𝓕 (iteratedDeriv n f) w‖ ≤ ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := by
    rw [hFT]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
    filter_upwards with ω
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcast : (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) = ((2 * Real.pi * w : ℝ) : ℂ) *
      Complex.I := by
    push_cast
    ring
  have hval : |2 * Real.pi * w| = |c| := by
    rw [hw2, abs_neg]
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ n‖ = |c| ^ n := by
    rw [norm_pow, hcast, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hval]
  calc |c| ^ n * ‖∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • f ω‖
      = ‖(2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ n • 𝓕 f w‖ := by
        rw [norm_smul, hnorm, hFT]
    _ = ‖𝓕 (iteratedDeriv n f) w‖ := by rw [hd]
    _ ≤ ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := hb

/-- A compactly supported `Cⁿ` function has a Fourier integral bounded by its `n`-th
 derivative, with the angular-frequency convention. -/
theorem norm_integral_exp_mul_I_smul_le_of_contDiff {f : ℝ → F} (n : ℕ)
    (hf : ContDiff ℝ n f) (hsupp : HasCompactSupport f) (c : ℝ) :
    |c| ^ n * ‖∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • f ω‖ ≤
      ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  set w : ℝ := -((2 * Real.pi)⁻¹ * c) with hw
  have hw2 : 2 * Real.pi * w = -c := by
    rw [hw, mul_neg, ← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
  have hFT : ∀ g : ℝ → F,
      𝓕 g w = ∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • g ω := by
    intro g
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    beta_reduce
    have harg : (-2 * Real.pi * v * w : ℝ) = v * c := by linear_combination (-v) * hw2
    rw [harg]
  have hint : ∀ m ≤ n, Integrable (iteratedDeriv m f) := fun m hm =>
    (hf.continuous_iteratedDeriv m (by exact_mod_cast hm)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv hsupp m)
  have hd := congrFun (Real.fourier_iteratedDeriv (E := F) (N := n) (n := n) hf
    (fun m hm => hint m (by exact_mod_cast hm)) le_rfl) w
  have hb : ‖𝓕 (iteratedDeriv n f) w‖ ≤ ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := by
    rw [hFT]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
    filter_upwards with ω
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcast : (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) = ((2 * Real.pi * w : ℝ) : ℂ) *
      Complex.I := by
    push_cast
    ring
  have hval : |2 * Real.pi * w| = |c| := by
    rw [hw2, abs_neg]
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ n‖ = |c| ^ n := by
    rw [norm_pow, hcast, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hval]
  calc |c| ^ n * ‖∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • f ω‖
      = ‖(2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ n • 𝓕 f w‖ := by
        rw [norm_smul, hnorm, hFT]
    _ = ‖𝓕 (iteratedDeriv n f) w‖ := by rw [hd]
    _ ≤ ∫ ω : ℝ, ‖iteratedDeriv n f ω‖ := hb

end Complex

end OperatorRidgelet
