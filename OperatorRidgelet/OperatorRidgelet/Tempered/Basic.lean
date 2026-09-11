import OperatorRidgelet.Tempered.Defs
import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.Transform.Plancherel
import OperatorRidgelet.ToMathlib.SchwartzAwayFromZero
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Auxiliary lemmas for Section 5 and Appendix C

Lemmas about the definitions of `OperatorRidgelet.Tempered.Defs` used by the proofs in
`OperatorRidgelet.Paper.Tempered`: the action and the activation-space membership of the
weighted realization `weightedDistribution`, square integrability of `⟨x⟩^{-t} β` for bounded
measurable `β`, the fact that a bounded nonconstant function is not a polynomial, and the
elementary properties (bounds, Lipschitz continuity, derivatives) of the standard activations,
the mollifier family `bumpApproximateIdentity` built from Mathlib's normalized bump
functions, which is an approximate identity in the sense of `IsApproximateIdentity`, the
existence of an even cutoff `IsCutoff ρ χ` for a band-pass `ρ` (a difference of two bumps),
Fourier uniqueness for real Schwartz filters, the test filter `ω ↦ ρ̂(-ω)|ω|^{-α}` of a band-pass
filter as a Schwartz function, and the behaviour of the distributional admissibility constant
under rescaling of the filter.  Not imported by `Challenge`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped ENNReal NNReal FourierTransform

/-! ### The weighted realization -/

/-- The weighted realization acts by integration against `β`. -/
theorem weightedDistribution_apply {t : ℝ} {β : ℝ → ℝ}
    (h : MemLp (fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    weightedDistribution t β φ = ∫ x : ℝ, φ x * (β x : ℂ) := by
  classical
  rw [weightedDistribution, dif_pos h]
  unfold temperedWeightMultiplier
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight t), hx]
  change temperedWeight t x * φ x * ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ) =
    φ x * (β x : ℂ)
  rw [show temperedWeight t x * φ x * ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ) =
    φ x * (temperedWeight t x * ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) by ring]
  congr 1
  unfold temperedWeight
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, ← japaneseBracketPow_add]
  simp

/-- The weighted realization lies in `𝒜_{0,t} = ⟨·⟩^t L²(ℝ)`. -/
theorem memActivationSpace_weightedDistribution {t : ℝ} {β : ℝ → ℝ}
    (h : MemLp (fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) 2 volume) :
    MemActivationSpace 0 t (weightedDistribution t β) := by
  classical
  refine ⟨h.toLp _, ?_⟩
  rw [angularBesselPotential_zero_apply, weightedDistribution, dif_pos h]
  unfold temperedWeightMultiplier
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_temperedWeight t) (hasTemperateGrowth_temperedWeight (-t))]
  rw [temperedWeight_mul_neg]
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ ↦ (1 : ℂ)) _ = _
  simp

/-- `⟨x⟩^{-t} β ∈ L²(ℝ)` for bounded measurable `β` and `t > 1/2`. -/
theorem memLp_japaneseBracketPow_mul_of_bounded {β : ℝ → ℝ} (hβ : Measurable β) {M : ℝ}
    (hM : ∀ x, |β x| ≤ M) {t : ℝ} (ht : (1 : ℝ) / 2 < t) :
    MemLp (fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) 2 volume := by
  have hj : Continuous (japaneseBracketPow (-t) : ℝ → ℝ) := by
    unfold japaneseBracketPow
    apply Continuous.rpow_const
    · fun_prop
    · intro x
      left
      positivity
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => ((japaneseBracketPow (-t) x * β x : ℝ) : ℂ)) volume :=
    (Complex.measurable_ofReal.comp (hj.measurable.mul hβ)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  apply ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := 2 * t) (by simp; linarith)).const_mul (M ^ 2)).mono'
  · exact hmeas.norm.pow 2
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Complex.norm_real]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (japaneseBracketPow_pos _ _), mul_pow]
    have hb : |β x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
    have hjx : japaneseBracketPow (-t) x ^ 2 = (1 + ‖x‖ ^ 2) ^ (-(2 * t) / 2) := by
      rw [japaneseBracketPow_sq]
      unfold japaneseBracketPow
      rw [show (2 * -t) / 2 = -(2 * t) / 2 by ring]
    rw [hjx]
    calc (1 + ‖x‖ ^ 2) ^ (-(2 * t) / 2) * |β x| ^ 2
        ≤ (1 + ‖x‖ ^ 2) ^ (-(2 * t) / 2) * M ^ 2 := by gcongr
      _ = M ^ 2 * (1 + ‖x‖ ^ 2) ^ (-(2 * t) / 2) := mul_comm _ _

/-- A bounded measurable function belongs to `𝒜_{0,t}` for every `t > 1/2`. -/
theorem memActivationSpaceFun_of_bounded {β : ℝ → ℝ} (hβ : Measurable β) {M : ℝ}
    (hM : ∀ x, |β x| ≤ M) {t : ℝ} (ht : (1 : ℝ) / 2 < t) :
    MemActivationSpaceFun 0 t β :=
  ⟨weightedDistribution t β,
    weightedDistribution_apply (memLp_japaneseBracketPow_mul_of_bounded hβ hM ht),
    memActivationSpace_weightedDistribution (memLp_japaneseBracketPow_mul_of_bounded hβ hM ht)⟩

/-! ### Polynomials -/

/-- A bounded function taking two different values is not a polynomial. -/
theorem not_isPolynomialFun_of_bounded {β : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |β x| ≤ M) {x₀ x₁ : ℝ}
    (hne : β x₀ ≠ β x₁) : ¬ IsPolynomialFun β := by
  rintro ⟨p, hp⟩
  by_cases hdeg : 0 < p.degree
  · obtain ⟨x, hx⟩ :=
      ((Polynomial.abs_tendsto_atTop p hdeg).eventually (eventually_gt_atTop M)).exists
    rw [← hp x] at hx
    exact absurd (hM x) (not_le.mpr hx)
  · rw [not_lt] at hdeg
    obtain hpC := Polynomial.degree_le_zero_iff.mp hdeg
    apply hne
    rw [hp x₀, hp x₁, hpC, Polynomial.eval_C, Polynomial.eval_C]

/-- ReLU is not a polynomial: a polynomial vanishing on `(-∞, 0]` is zero. -/
theorem not_isPolynomialFun_relu : ¬ IsPolynomialFun relu := by
  rintro ⟨p, hp⟩
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.Iic_infinite (0 : ℝ))
    intro x hx
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, ← hp x, relu]
    exact max_eq_right hx
  have h1 := hp 1
  rw [hp0, Polynomial.eval_zero] at h1
  norm_num [relu] at h1

/-! ### ReLU and tanh -/

/-- ReLU is `1`-Lipschitz. -/
theorem lipschitzWith_relu : LipschitzWith 1 relu :=
  LipschitzWith.id.max_const 0

/-- The absolute value of `tanh` is bounded by one. -/
theorem abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 :=
  (Real.abs_tanh_lt_one x).le

/-- The values of `tanh` at zero and one differ. -/
theorem tanh_zero_ne_tanh_one : Real.tanh 0 ≠ Real.tanh 1 := by
  intro h
  have := Real.tanh_injective h
  norm_num at this

/-- The derivative of `tanh` is `1 / cosh²`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have hfun : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  rw [hfun] at h
  have hc : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    rw [← sq, ← sq, Real.cosh_sq]
    ring
  exact h.congr_deriv (by rw [hc])

/-- `tanh` is `1`-Lipschitz. -/
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_tanh x).differentiableAt)
  intro x
  rw [(hasDerivAt_tanh x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
  nlinarith [Real.one_le_cosh x]

/-! ### The Gaussian -/

/-- The Gaussian activation is strictly positive. -/
theorem gaussianFun_pos (u : ℝ) : 0 < gaussianFun u :=
  Real.exp_pos _

/-- The absolute value of the Gaussian activation is bounded by one. -/
theorem abs_gaussianFun_le_one (u : ℝ) : |gaussianFun u| ≤ 1 := by
  rw [gaussianFun, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])

/-- The Gaussian activation takes different values at zero and one. -/
theorem gaussianFun_zero_ne_gaussianFun_one : gaussianFun 0 ≠ gaussianFun 1 := by
  intro h
  have := Real.exp_injective h
  norm_num at this

/-- The Gaussian activation is continuous. -/
theorem continuous_gaussianFun : Continuous gaussianFun := by
  unfold gaussianFun
  fun_prop

/-- The derivative of the Gaussian activation is `-u * gaussianFun u`. -/
theorem hasDerivAt_gaussianFun (u : ℝ) : HasDerivAt gaussianFun (-u * gaussianFun u) u := by
  have h : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  refine h.exp.congr_deriv ?_
  unfold gaussianFun
  ring

/-- The Gaussian `e^{-u²/2}` is `1`-Lipschitz. -/
theorem lipschitzWith_gaussianFun : LipschitzWith 1 gaussianFun := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun u => (hasDerivAt_gaussianFun u).differentiableAt)
  intro u
  rw [(hasDerivAt_gaussianFun u).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (gaussianFun_pos u)]
  have h1 : |u| ≤ u ^ 2 / 2 + 1 := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
  have h2 : u ^ 2 / 2 + 1 ≤ Real.exp (u ^ 2 / 2) := Real.add_one_le_exp _
  have h3 : gaussianFun u = (Real.exp (u ^ 2 / 2))⁻¹ := by
    rw [gaussianFun, ← Real.exp_neg, neg_div]
  rw [h3, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact h1.trans h2

/-! ### The Gaussian distribution function -/

/-- The Gaussian distribution function is nonnegative. -/
theorem gaussianCdf_nonneg (u : ℝ) : 0 ≤ gaussianCdf u :=
  setIntegral_nonneg measurableSet_Iic fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x

/-- The Gaussian distribution function is bounded above by one. -/
theorem gaussianCdf_le_one (u : ℝ) : gaussianCdf u ≤ 1 := by
  unfold gaussianCdf
  rw [← ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero]
  exact setIntegral_le_integral (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
    (Filter.Eventually.of_forall fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)

/-- The absolute value of the Gaussian distribution function is bounded by one. -/
theorem abs_gaussianCdf_le_one (u : ℝ) : |gaussianCdf u| ≤ 1 :=
  abs_le.mpr ⟨by linarith [gaussianCdf_nonneg u], gaussianCdf_le_one u⟩

/-- The Gaussian distribution function is monotone. -/
theorem monotone_gaussianCdf : Monotone gaussianCdf := by
  intro a b hab
  unfold gaussianCdf
  exact setIntegral_mono_set (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)
    (Filter.Eventually.of_forall (Set.Iic_subset_Iic.mpr hab))

/-- The Gaussian distribution function is measurable. -/
theorem measurable_gaussianCdf : Measurable gaussianCdf :=
  monotone_gaussianCdf.measurable

/-- `Φ(x) - Φ(y) = ∫_y^x (2π)^{-1/2} e^{-v²/2} dv`. -/
theorem gaussianCdf_sub_gaussianCdf (x y : ℝ) :
    gaussianCdf x - gaussianCdf y = ∫ v in y..x, ProbabilityTheory.gaussianPDFReal 0 1 v :=
  intervalIntegral.integral_Iic_sub_Iic
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn

/-- The Gaussian distribution function increases strictly between zero and one. -/
theorem gaussianCdf_zero_lt_gaussianCdf_one : gaussianCdf 0 < gaussianCdf 1 := by
  have hpos : 0 < ∫ v in (0 : ℝ)..1, ProbabilityTheory.gaussianPDFReal 0 1 v :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (ProbabilityTheory.integrable_gaussianPDFReal 0 1).intervalIntegrable
      (fun x _ => ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero) one_pos
  linarith [gaussianCdf_sub_gaussianCdf 1 0]

/-- The standard Gaussian density is bounded by `(2π)^{-1/2}`. -/
theorem gaussianPDFReal_zero_one_le (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _

/-- `Φ` is Lipschitz with constant `(2π)^{-1/2}`. -/
theorem lipschitzWith_gaussianCdf :
    LipschitzWith (Real.toNNReal (Real.sqrt (2 * Real.pi))⁻¹) gaussianCdf := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, gaussianCdf_sub_gaussianCdf,
    Real.coe_toNNReal _ (by positivity)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
    (C := (Real.sqrt (2 * Real.pi))⁻¹) (f := ProbabilityTheory.gaussianPDFReal 0 1)
    (fun v _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 v)]
      exact gaussianPDFReal_zero_one_le v)
  rwa [Real.norm_eq_abs] at h

/-! ### An approximate identity -/

/-- The mollifier family `η_ε = ` the normalized smooth bump with inner radius `ε/2` and outer
radius `ε` (Mathlib's `ContDiffBump.normed`), and `0` for `ε ≤ 0`. -/
def bumpApproximateIdentity (ε : ℝ) (x : ℝ) : ℝ :=
  if hε : 0 < ε then
    ({ rIn := ε / 2, rOut := ε, rIn_pos := by positivity, rIn_lt_rOut := by linarith } :
      ContDiffBump (0 : ℝ)).normed volume x
  else 0

/-- For a positive scale, the mollifier is the normalized smooth bump. -/
theorem bumpApproximateIdentity_of_pos {ε : ℝ} (hε : 0 < ε) :
    bumpApproximateIdentity ε =
      ({ rIn := ε / 2, rOut := ε, rIn_pos := by positivity, rIn_lt_rOut := by linarith } :
        ContDiffBump (0 : ℝ)).normed volume := by
  funext x
  simp only [bumpApproximateIdentity, dif_pos hε]

/-- The mollifier family is an even, compactly supported, smooth approximate identity. -/
theorem isApproximateIdentity_bumpApproximateIdentity :
    IsApproximateIdentity bumpApproximateIdentity where
  contDiff ε hε := by
    rw [bumpApproximateIdentity_of_pos hε]
    exact ContDiffBump.contDiff_normed _
  hasCompactSupport ε hε := by
    rw [bumpApproximateIdentity_of_pos hε]
    exact ContDiffBump.hasCompactSupport_normed _
  even ε hε x := by
    rw [bumpApproximateIdentity_of_pos hε]
    exact ContDiffBump.normed_neg _ x
  nonneg ε hε x := by
    rw [bumpApproximateIdentity_of_pos hε]
    exact ContDiffBump.nonneg_normed _ x
  integral_eq_one ε hε := by
    rw [bumpApproximateIdentity_of_pos hε]
    exact ContDiffBump.integral_normed _
  tendsto_tsupport := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    rw [bumpApproximateIdentity_of_pos hε.1, ContDiffBump.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball hε.2).trans hδt

/-! ### Cutoffs -/

/-- For a band-pass `ρ` there is an even cutoff `χ ∈ C_c^∞(ℝ ∖ {0})` equal to one on a
neighbourhood of `supp ρ̂`: the difference of a bump equal to one on a large ball and a bump
supported near the origin. -/
theorem IsBandPass.exists_isCutoff {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) :
    ∃ χ : ℝ → ℝ, IsCutoff ρ χ := by
  obtain ⟨r, hr, hrK⟩ :=
    SchwartzMap.exists_pos_le_abs_of_zero_notMem_tsupport hρ.zero_notMem_tsupport
  obtain ⟨R₀, hR₀⟩ := hρ.hasCompactSupport.isBounded.subset_closedBall (0 : ℝ)
  set R : ℝ := max R₀ (r + 1) + 1 with hR
  have hrR : r + 1 ≤ R - 1 := by
    rw [hR]
    linarith [le_max_right R₀ (r + 1)]
  have hRpos : 0 < R := by linarith
  let bOut : ContDiffBump (0 : ℝ) :=
    { rIn := R, rOut := R + 1, rIn_pos := hRpos, rIn_lt_rOut := by linarith }
  let bIn : ContDiffBump (0 : ℝ) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  refine ⟨fun ω => bOut ω - bIn ω, bOut.contDiff.sub bIn.contDiff,
    bOut.hasCompactSupport.sub bIn.hasCompactSupport, ?_, ?_, ?_⟩
  · rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < r / 4)] with ω hω
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hω
    have h1 : bOut ω = 1 := bOut.one_of_mem_closedBall (by
      change ω ∈ Metric.closedBall (0 : ℝ) R
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      linarith)
    have h2 : bIn ω = 1 := bIn.one_of_mem_closedBall (by
      change ω ∈ Metric.closedBall (0 : ℝ) (r / 4)
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hω.le)
    simp [h1, h2]
  · intro ω
    simp only [bOut.neg, bIn.neg]
  · rw [eventually_nhdsSet_iff_exists]
    refine ⟨Metric.ball 0 R \ Metric.closedBall 0 (r / 2),
      Metric.isOpen_ball.sdiff Metric.isClosed_closedBall, fun ω hω => ⟨?_, ?_⟩, ?_⟩
    · have h := hR₀ hω
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      linarith [le_max_left R₀ (r + 1)]
    · intro h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      linarith [hrK ω hω]
    · rintro ω ⟨h1, h2⟩
      have hb1 : bOut ω = 1 := bOut.one_of_mem_closedBall (Metric.ball_subset_closedBall h1)
      have hb2 : bIn ω = 0 := bIn.zero_of_le_dist (by
        change r / 2 ≤ dist ω 0
        rw [Metric.mem_closedBall, not_le] at h2
        exact h2.le)
      simp [hb1, hb2]

/-! ### Fourier uniqueness for real filters -/

/-- The integrand of `ρ̂(ω)` is integrable. -/
theorem integrable_character_mul_schwartz (ρ : SchwartzMap ℝ ℝ) (ω : ℝ) :
    Integrable fun t : ℝ => Complex.exp (-Complex.I * ((inner ℝ t ω : ℝ) : ℂ)) * (ρ t : ℂ) := by
  have hint : Integrable fun t : ℝ => (ρ t : ℂ) := (SchwartzMap.ofReal ρ).integrable
  refine (hint.mul_unimodular ?_ ?_).congr (Filter.Eventually.of_forall fun t => mul_comm _ _)
  · exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)))).aestronglyMeasurable
  · filter_upwards with t
    rw [Complex.norm_exp]
    simp

/-- `ρ̂` is additive in the filter. -/
theorem filterFourier_sub (b b' : SchwartzMap ℝ ℝ) (ω : ℝ) :
    filterFourier (⇑(b - b')) ω = filterFourier b ω - filterFourier b' ω := by
  change filterFourier (⇑b - ⇑b') ω = _
  unfold filterFourier lineFourier LeanRidgelet.Fourier.angularFourierIntegralInner
  rw [← integral_sub (integrable_character_mul_schwartz b ω)
    (integrable_character_mul_schwartz b' ω)]
  congr 1
  funext t
  simp only [Pi.sub_apply, Complex.ofReal_sub, mul_sub]

/-- `ρ̂` is homogeneous in the filter (Schwartz-level scalar multiple). -/
theorem filterFourier_smul' (c : ℝ) (ρ : SchwartzMap ℝ ℝ) (ω : ℝ) :
    filterFourier (⇑(c • ρ)) ω = (c : ℂ) * filterFourier ρ ω := by
  rw [← filterFourier_smul]
  rfl

/-- Two real Schwartz functions with the same Fourier transform coincide. -/
theorem SchwartzMap.eq_of_filterFourier_eq {b b' : SchwartzMap ℝ ℝ}
    (h : ∀ ω : ℝ, filterFourier b ω = filterFourier b' ω) : b = b' := by
  rw [← sub_eq_zero]
  by_contra hne
  apply filterFourier_ne_zero hne
  funext ω
  rw [filterFourier_sub, h ω, sub_self, Pi.zero_apply]

/-! ### The test filter of a band-pass filter -/

/-- `ω ↦ ρ̂(-ω)` as a Schwartz function. -/
def filterFourierNegSchwartz (ρ : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realDilationCLE (-(2 * Real.pi)⁻¹) (neg_ne_zero.mpr (inv_ne_zero two_mul_pi_ne_zero)))
    (𝓕 (SchwartzMap.ofReal ρ))

/-- The reflected Fourier test function evaluates to `ρ̂(-ω)`. -/
theorem filterFourierNegSchwartz_apply (ρ : SchwartzMap ℝ ℝ) (ω : ℝ) :
    filterFourierNegSchwartz ρ ω = filterFourier ρ (-ω) := by
  rw [filterFourier_eq_fourier_ofReal, filterFourierNegSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, realDilationCLE_apply]
  congr 1
  ring

/-- The support of `ω ↦ ρ̂(-ω)` stays away from the origin for band-pass `ρ`. -/
theorem IsBandPass.zero_notMem_tsupport_neg {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) :
    (0 : ℝ) ∉ tsupport (filterFourierNegSchwartz ρ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have h := hρ.zero_notMem_tsupport
  rw [notMem_tsupport_iff_eventuallyEq] at h
  have hneg : Tendsto (fun ω : ℝ => -ω) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  filter_upwards [h.comp_tendsto hneg] with ω hω
  simpa [filterFourierNegSchwartz_apply] using hω

/-- For band-pass `ρ`, the test filter `ω ↦ ρ̂(-ω)|ω|^{-α}` is a Schwartz function. -/
theorem IsBandPass.exists_temperedTestFilter {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (α : ℝ) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ ω : ℝ, φ ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
  obtain ⟨ψ, hψ⟩ := SchwartzMap.exists_eq_abs_rpow_mul (filterFourierNegSchwartz ρ)
    hρ.zero_notMem_tsupport_neg (-α)
  exact ⟨ψ, fun ω => by rw [hψ ω, filterFourierNegSchwartz_apply, mul_comm]⟩

/-- The values of the test filter of a band-pass filter. -/
theorem IsBandPass.temperedTestFilter_apply {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (α : ℝ)
    (ω : ℝ) :
    temperedTestFilter α ρ ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) :=
  OperatorRidgelet.temperedTestFilter_apply (hρ.exists_temperedTestFilter α) ω

/-- The test filter of a band-pass filter is supported away from the origin. -/
theorem IsBandPass.zero_notMem_tsupport_temperedTestFilter {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) (α : ℝ) : (0 : ℝ) ∉ tsupport (temperedTestFilter α ρ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have h := hρ.zero_notMem_tsupport_neg
  rw [notMem_tsupport_iff_eventuallyEq] at h
  filter_upwards [h] with ω hω
  rw [filterFourierNegSchwartz_apply, Pi.zero_apply] at hω
  rw [hρ.temperedTestFilter_apply, hω, Pi.zero_apply, zero_mul]

/-! ### Rescaling a filter -/

/-- A nonzero multiple of a band-pass filter is band-pass. -/
theorem IsBandPass.smul {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {c : ℝ} (hc : c ≠ 0) :
    IsBandPass (c • ρ) := by
  have hF : filterFourier (⇑(c • ρ)) = fun ω => (c : ℂ) * filterFourier ρ ω :=
    funext (filterFourier_smul' c ρ)
  refine ⟨smul_ne_zero hc hρ.ne_zero, ?_, ?_, ?_⟩
  · rw [hF]
    exact contDiff_const.mul hρ.contDiff
  · rw [hF]
    exact hρ.hasCompactSupport.mul_left
  · rw [hF]
    exact fun h => hρ.zero_notMem_tsupport (tsupport_mul_subset_right h)

/-- The test filter is homogeneous in the filter. -/
theorem IsBandPass.temperedTestFilter_smul {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (α c : ℝ) :
    temperedTestFilter α (c • ρ) = (c : ℂ) • temperedTestFilter α ρ := by
  have hc : ∃ φ : SchwartzMap ℝ ℂ,
      ∀ ω : ℝ, φ ω = filterFourier (⇑(c • ρ)) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) :=
    ⟨(c : ℂ) • temperedTestFilter α ρ, fun ω => by
      change (c : ℂ) * temperedTestFilter α ρ ω = _
      rw [hρ.temperedTestFilter_apply, filterFourier_smul']
      ring⟩
  ext ω
  change temperedTestFilter α (c • ρ) ω = (c : ℂ) * temperedTestFilter α ρ ω
  rw [OperatorRidgelet.temperedTestFilter_apply hc ω, hρ.temperedTestFilter_apply,
    filterFourier_smul']
  ring

/-- The distributional admissibility constant is homogeneous in the filter. -/
theorem IsBandPass.temperedAdmissibilityConst_smul {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (α : ℝ) (β : TemperedDistribution ℝ ℂ) (c : ℝ) :
    temperedAdmissibilityConst α β (c • ρ) = (c : ℂ) * temperedAdmissibilityConst α β ρ := by
  unfold temperedAdmissibilityConst
  rw [hρ.temperedTestFilter_smul, map_smul, smul_eq_mul]
  ring

end OperatorRidgelet
