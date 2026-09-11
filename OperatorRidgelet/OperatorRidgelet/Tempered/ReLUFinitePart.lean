import OperatorRidgelet.Tempered.ReLU
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OperatorRidgelet.ToMathlib.CauchyBoundary

/-!
# The Fourier transform of ReLU at the origin

The Hadamard finite-part formula follows by damping the positive half-line integral,
applying Fubini and the elementary Laplace integral, and taking the Cauchy boundary limit.
-/

noncomputable section
open MeasureTheory Complex Filter Topology Set LeanRidgelet LeanRidgelet.Fourier
open scoped FourierTransform ENNReal
namespace OperatorRidgelet

/-- Differentiation of the test function becomes coordinate multiplication in the angular Fourier convention. -/
theorem angularFourierSchwartz_deriv (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    angularFourierSchwartz (SchwartzMap.derivCLM ℂ ℂ φ) x =
      I * (x : ℂ) * angularFourierSchwartz φ x := by
  rw [angularFourierSchwartz_eq_fourier, coe_derivCLM,
    Real.fourier_deriv φ.integrable ((φ.smooth 1).differentiable one_ne_zero)
      (by rw [← coe_derivCLM]; exact (SchwartzMap.derivCLM ℂ ℂ φ).integrable),
    angularFourierSchwartz_eq_fourier]
  simp only [smul_eq_mul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The Fourier distribution of ReLU is its angular Fourier test function paired with the positive half-line coordinate. -/
theorem angularFourierDistribution_relu_eq_half (φ : SchwartzMap ℝ ℂ) :
    angularFourierDistribution reluDistribution φ =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) * angularFourierSchwartz φ x := by
  rw [angularFourierDistribution_apply]
  unfold reluDistribution
  rw [reluTemperedDistribution_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [relu, max_eq_left (le_of_lt hx)]
    ring
  · intro x hx
    rw [mem_Ioi, not_lt] at hx
    rw [relu, max_eq_right hx]
    simp

/-- Exponential damping converges to the Fourier distributional pairing of ReLU. -/
theorem tendsto_damped_relu (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ),
      (Real.exp (-ε * x) : ℂ) * ((x : ℂ) * angularFourierSchwartz φ x))
      (𝓝[>] 0) (𝓝 (angularFourierDistribution reluDistribution φ)) := by
  rw [angularFourierDistribution_relu_eq_half]
  let ψ := coordMulSchwartz (angularFourierSchwartz φ)
  have hψ : (fun x : ℝ => (x : ℂ) * angularFourierSchwartz φ x) = ψ :=
    (funext (coordMulSchwartz_apply _)).symm
  rw [hψ]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖ψ x‖)
    (Eventually.of_forall fun ε => by fun_prop) ?_ ψ.integrable.norm.integrableOn ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change 0 < ε at hε
    change 0 < x at hx
    rw [show ψ x = (x : ℂ) * angularFourierSchwartz φ x from coordMulSchwartz_apply _ _]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hx.le)
  · filter_upwards with x
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have he : Tendsto (fun ε : ℝ => (Real.exp (-ε * x) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      simpa only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (Real.continuous_exp.continuousAt.tendsto.comp ((ht.neg).mul_const x))
    simpa only [one_mul, ← coordMulSchwartz_apply] using he.mul_const (ψ x)

/-- Exponential damping of the Fourier integral on the positive half-line gives the Cauchy resolvent. -/
theorem integral_damped_fourier (ψ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) * angularFourierSchwartz ψ x) =
      ∫ ω : ℝ, ((ε : ℂ) + I * (ω : ℂ))⁻¹ * ψ ω := by
  simp_rw [angularFourierSchwartz_apply]
  exact ψ.integral_damped_fourier hε

/-- The damped Fourier pairing of ReLU splits into odd Cauchy and Poisson integrals. -/
theorem integral_damped_relu (φ : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) *
      ((x : ℂ) * angularFourierSchwartz φ x)) =
      -(∫ x : ℝ, ((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) *
        SchwartzMap.derivCLM ℂ ℂ φ x) -
      I * (∫ x : ℝ, ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) *
        SchwartzMap.derivCLM ℂ ℂ φ x) := by
  let D := SchwartzMap.derivCLM ℂ ℂ φ
  have hid : (∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) *
      ((x : ℂ) * angularFourierSchwartz φ x)) =
      -I * ∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) * angularFourierSchwartz D x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [D]
    rw [angularFourierSchwartz_deriv]
    ring_nf
    simp only [I_sq]
    ring
  rw [hid, integral_damped_fourier D hε]
  rw [← integral_const_mul]
  calc
    _ = ∫ x : ℝ, -(((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x) -
        I * (((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hc : (ε : ℂ) + I * (x : ℂ) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hd : (ε : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast ne_of_gt (by positivity : 0 < ε ^ 2 + x ^ 2)
      push_cast
      field_simp
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      calc
        _ = (∫ x : ℝ, -(((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x)) -
            ∫ x : ℝ, I * (((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x) :=
          integral_sub (D.integrable_cauchyOdd hε).neg ((D.integrable_poisson hε).const_mul I)
        _ = _ := by rw [integral_neg, integral_const_mul]

/-- The Fourier transform of ReLU equals minus the Hadamard finite part plus the derivative of the Dirac mass. -/
theorem angularFourierDistribution_relu_finitePart (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ =>
      (∫ ω in {ω : ℝ | ε < |ω|}, φ ω / (ω : ℂ) ^ 2) - 2 * φ 0 / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (-(angularFourierDistribution reluDistribution φ) -
        (Real.pi : ℂ) * I * deriv φ 0)) := by
  let D := SchwartzMap.derivCLM ℂ ℂ φ
  have hlim := D.tendsto_integral_cauchyOdd.neg.sub (D.tendsto_integral_poisson.const_mul I)
  have heq := hlim.congr' (show
      (fun ε : ℝ => -(∫ x : ℝ, ((x / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x) -
        I * (∫ x : ℝ, ((ε / (ε ^ 2 + x ^ 2) : ℝ) : ℂ) * D x)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), (Real.exp (-ε * x) : ℂ) *
        ((x : ℂ) * angularFourierSchwartz φ x)) from by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_damped_relu φ hε).symm)
  have hvalue := tendsto_nhds_unique (tendsto_damped_relu φ) heq
  have hv : -(angularFourierDistribution reluDistribution φ) -
      (Real.pi : ℂ) * I * deriv φ 0 =
      ∫ x in Ioi (0 : ℝ), SchwartzMap.symmetricSlope D x := by
    rw [hvalue]
    dsimp [D]
    ring
  rw [hv]
  exact φ.tendsto_finitePart

end OperatorRidgelet

