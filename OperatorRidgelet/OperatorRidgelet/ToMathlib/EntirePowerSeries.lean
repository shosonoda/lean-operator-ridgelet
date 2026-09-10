import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Entire functions given by an everywhere convergent scalar power series

If `∑ aₙ zⁿ` converges to `F z` for every `z : ℂ`, then the formal power series
`FormalMultilinearSeries.ofScalars ℂ a` has infinite radius of convergence and is the power
series of `F` at `0`:

* `hasFPowerSeriesOnBall_ofScalars_of_hasSum`;
* `differentiable_of_hasSum_pow`: `F` is entire;
* `iteratedDeriv_eq_of_hasSum_pow`: `F⁽ⁿ⁾(0) = n! aₙ`;
* `iteratedDeriv_ofReal_of_hasSum_pow`: the same for the restriction of `F` to the real line,
  using `iteratedDeriv_comp_ofReal`, which says that the derivatives along `ℝ` of the
  restriction of an entire function are the restrictions of its complex derivatives.
-/

open Filter Topology

namespace OperatorRidgelet

/-- The radius of convergence of an everywhere convergent scalar power series is infinite. -/
theorem ofScalars_radius_eq_top_of_summable {a : ℕ → ℂ}
    (h : ∀ z : ℂ, Summable fun n => a n * z ^ n) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine FormalMultilinearSeries.le_radius_of_tendsto (l := 0) _ ?_
  have h0 := (h ((r : ℝ) : ℂ)).tendsto_atTop_zero.norm
  simp only [norm_zero] at h0
  refine h0.congr fun n => ?_
  rw [norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]

/-- An everywhere convergent scalar power series is the power series of its sum. -/
theorem hasFPowerSeriesOnBall_ofScalars_of_hasSum {a : ℕ → ℂ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (F z)) :
    HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ a) 0 ⊤ where
  r_le := by rw [ofScalars_radius_eq_top_of_summable fun z => (h z).summable]
  r_pos := by simp
  hasSum := by
    intro y _
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using h y

/-- A function given by an everywhere convergent scalar power series is entire. -/
theorem differentiable_of_hasSum_pow {a : ℕ → ℂ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (F z)) : Differentiable ℂ F := by
  have hball := (hasFPowerSeriesOnBall_ofScalars_of_hasSum h).analyticOnNhd
  intro z
  exact (hball z (by simp)).differentiableAt

/-- The Taylor coefficients of an everywhere convergent scalar power series are its
coefficients: `F⁽ⁿ⁾(0) = n! aₙ`. -/
theorem iteratedDeriv_eq_of_hasSum_pow {a : ℕ → ℂ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (F z)) (n : ℕ) :
    iteratedDeriv n F 0 = (n.factorial : ℂ) * a n := by
  have hp : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 :=
    ⟨⊤, hasFPowerSeriesOnBall_ofScalars_of_hasSum h⟩
  have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have ha : a = fun n => iteratedDeriv n F 0 / (n.factorial : ℂ) :=
    FormalMultilinearSeries.ofScalars_series_injective (𝕜 := ℂ) (E := ℂ) heq
  rw [show a n = iteratedDeriv n F 0 / (n.factorial : ℂ) from congrFun ha n,
    mul_div_cancel₀ _ (by exact_mod_cast n.factorial_ne_zero)]

/-- The iterated derivatives along `ℝ` of the restriction of an entire function to the real
line are the restrictions of its complex iterated derivatives. -/
theorem iteratedDeriv_comp_ofReal (n : ℕ) :
    ∀ (G : ℂ → ℂ), Differentiable ℂ G → ∀ t : ℝ,
      iteratedDeriv n (fun s : ℝ => G s) t = iteratedDeriv n G t := by
  induction n with
  | zero => intro G _ t; simp
  | succ n ih =>
    intro G hG t
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hd : (deriv fun s : ℝ => G (s : ℂ)) = fun s : ℝ => deriv G (s : ℂ) := by
      funext s
      exact ((hG (s : ℂ)).hasDerivAt.comp_ofReal).deriv
    rw [hd]
    exact ih (deriv G) hG.deriv t

/-- `F⁽ⁿ⁾(0) = n! aₙ` for the restriction of `F` to the real line. -/
theorem iteratedDeriv_ofReal_of_hasSum_pow {a : ℕ → ℂ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (F z)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => F t) 0 = (n.factorial : ℂ) * a n := by
  rw [show (0 : ℝ) = ((0 : ℝ) : ℝ) from rfl,
    iteratedDeriv_comp_ofReal n F (differentiable_of_hasSum_pow h) 0]
  simpa using iteratedDeriv_eq_of_hasSum_pow h n

end OperatorRidgelet
