import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OperatorRidgelet.ToMathlib.FourierAlgebra
import OperatorRidgelet.ToMathlib.TemperateRpow

/-!
# Fourier integrability of fractional Schwartz multipliers

For every positive exponent, a Schwartz function multiplied by a power of the norm
has an integrable Fourier transform. Near zero, a smooth dyadic annular partition
has geometrically summable Fourier L¹ norms; convolution controls multiplication
by the test function. Away from zero, a positive smooth regularization of the norm
gives a multiplier of temperate growth.
-/

noncomputable section
open MeasureTheory Complex Filter Topology Set
open scoped FourierTransform ContDiff
namespace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A fractional norm multiplier localized to the difference of two nested smooth cutoffs. -/
def annularRpowFun (b : ContDiffBump (0 : E)) (β : ℝ) (x : E) : ℂ :=
  (‖x‖ ^ β : ℝ) * (b x - b ((2 : ℝ) • x))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The annular multiplier is smooth because it vanishes near zero. -/
theorem contDiff_annularRpowFun (b : ContDiffBump (0 : E)) (β : ℝ) :
    ContDiff ℝ ∞ (annularRpowFun b β) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hnear : annularRpowFun b β =ᶠ[𝓝 (0 : E)] (fun _ => 0) := by
      have hb : (fun x : E => b ((2 : ℝ) • x)) =ᶠ[𝓝 (0 : E)] (fun _ => 1) := by
        exact b.eventuallyEq_one.comp_tendsto (by simpa using (continuous_const_smul (2 : ℝ)).tendsto (0 : E))
      filter_upwards [b.eventuallyEq_one, hb] with x hx hx'
      simp [annularRpowFun, hx, hx']
    exact contDiffAt_const.congr_of_eventuallyEq hnear
  · have hr : ContDiffAt ℝ ∞ (fun y : E => ‖y‖ ^ β) x :=
      (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
    have hb : ContDiffAt ℝ ∞ (fun y : E => b y - b ((2 : ℝ) • y)) x :=
      b.contDiffAt.sub ((b.contDiff.comp (contDiff_const.smul contDiff_id)).contDiffAt)
    convert! (Complex.ofRealCLM.contDiff.contDiffAt.comp x hr).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x hb) using 1
    ext y
    simp [annularRpowFun]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The annular fractional multiplier has compact support. -/
theorem hasCompactSupport_annularRpowFun (b : ContDiffBump (0 : E)) (β : ℝ) :
    HasCompactSupport (annularRpowFun b β) := by
  have hb : HasCompactSupport (fun x : E => b x) := b.hasCompactSupport
  have hb2 : HasCompactSupport (fun x : E => b ((2 : ℝ) • x)) := by
    exact hb.comp_homeomorph (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num))
  have hb3 : HasCompactSupport (fun x : E => b x - b ((2 : ℝ) • x)) := hb.sub hb2
  have hb4 : HasCompactSupport (fun x : E => ((b x - b ((2 : ℝ) • x) : ℝ) : ℂ)) :=
    hb3.comp_left (by simp : Complex.ofReal 0 = 0)
  convert! (hb4.mul_left (f := fun x : E => ((‖x‖ ^ β : ℝ) : ℂ))) using 1
  ext y
  simp [annularRpowFun]

/-- The smooth compact annular fractional multiplier as a Schwartz function. -/
def annularRpow (b : ContDiffBump (0 : E)) (β : ℝ) : SchwartzMap E ℂ :=
  (hasCompactSupport_annularRpowFun b β).toSchwartzMap (contDiff_annularRpowFun b β)

/-- Pointwise formula for the annular Schwartz multiplier. -/
theorem annularRpow_apply (b : ContDiffBump (0 : E)) (β : ℝ) (x : E) :
    annularRpow b β x = (‖x‖ ^ β : ℝ) * (b x - b ((2 : ℝ) • x)) := rfl

/-- The geometrically weighted dyadic dilation of the annular multiplier. -/
def annularTerm (b : ContDiffBump (0 : E)) (β : ℝ) (j : ℕ) : SchwartzMap E ℂ :=
  (((2 : ℝ) ^ (-β)) ^ j : ℝ) • dilate (annularRpow b β) ((2 : ℝ) ^ j) (by positivity)

/-- The weighted dilation is a telescoping difference of consecutive cutoffs. -/
theorem annularTerm_apply (b : ContDiffBump (0 : E)) (β : ℝ) (j : ℕ) (x : E) :
    annularTerm b β j x = (‖x‖ ^ β : ℝ) *
      (b (((2 : ℝ) ^ j) • x) - b (((2 : ℝ) ^ (j + 1)) • x)) := by
  simp only [annularTerm, smul_apply, dilate_apply, annularRpow_apply,
    Complex.real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hp : ((2 : ℝ) ^ (-β)) ^ j * ((2 : ℝ) ^ j) ^ β = 1 := by
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    convert Real.rpow_zero 2 using 1
    congr 1
    ring
  have hs : (2 : ℝ) • ((2 : ℝ) ^ j • x) = (2 : ℝ) ^ (j + 1) • x := by
    rw [smul_smul, pow_succ']
  rw [hs, Complex.ofReal_mul]
  calc
    _ = ((((2 : ℝ) ^ (-β)) ^ j * ((2 : ℝ) ^ j) ^ β : ℝ) : ℂ) *
        ((‖x‖ ^ β : ℝ) : ℂ) *
        (b (((2 : ℝ) ^ j) • x) - b (((2 : ℝ) ^ (j + 1)) • x)) := by push_cast; ring
    _ = _ := by rw [hp]; simp

/-- The inverse Fourier L¹ norm of each annular term decays geometrically. -/
theorem integral_norm_fourierInv_annularTerm (b : ContDiffBump (0 : E)) (β : ℝ) (j : ℕ) :
    (∫ x, ‖𝓕⁻ (annularTerm b β j) x‖) =
      ((2 : ℝ) ^ (-β)) ^ j * (∫ x, ‖𝓕⁻ (annularRpow b β) x‖) := by
  simp only [annularTerm, FourierTransform.fourierInv_smul, smul_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ (-β)) ^ j)]
  rw [integral_const_mul, integral_norm_fourierInv_dilate _ (by positivity)]

/-- The dyadic annular series is pointwise absolutely summable. -/
theorem summable_norm_annularTerm (b : ContDiffBump (0 : E)) {β : ℝ} (hβ : 0 < β) (x : E) :
    Summable (fun j : ℕ => ‖annularTerm b β j x‖) := by
  have hr : |(2 : ℝ) ^ (-β)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hβ)
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => ?_) ((summable_geometric_of_abs_lt_one hr).mul_right
      (SchwartzMap.seminorm ℝ 0 0 (annularRpow b β)))
  simp only [annularTerm, smul_apply, dilate_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ (-β)) ^ j)]
  exact mul_le_mul_of_nonneg_left ((annularRpow b β).norm_le_seminorm ℝ _) (by positivity)

/-- The dyadic annular series sums to the cutoff fractional norm multiplier. -/
theorem hasSum_annularTerm (b : ContDiffBump (0 : E)) {β : ℝ} (hβ : 0 < β) (x : E) :
    HasSum (fun j : ℕ => annularTerm b β j x) ((‖x‖ ^ β : ℝ) * b x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simpa [annularTerm_apply, Real.zero_rpow hβ.ne'] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  apply (hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_annularTerm b hβ x)).mpr
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, annularTerm b β j x) =
      (‖x‖ ^ β : ℝ) * (b x - b (((2 : ℝ) ^ n) • x)) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_range_succ, hn, annularTerm_apply]
      ring
  simp_rw [hsum]
  have hgrow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * ‖x‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      (norm_pos_iff.mpr hx)
  have hevent : ∀ᶠ n : ℕ in atTop, b (((2 : ℝ) ^ n) • x) = 0 := by
    filter_upwards [hgrow.eventually_ge_atTop b.rOut] with n hn
    apply b.zero_of_le_dist
    simpa [dist_zero_right, norm_smul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ n)] using hn
  have ht : Tendsto (fun n : ℕ => (b (((2 : ℝ) ^ n) • x) : ℂ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    simp [hn]
  simpa using (tendsto_const_nhds.sub ht).const_mul ((‖x‖ ^ β : ℝ) : ℂ)

/-- Multiplication by a Schwartz function preserves summability of the annular Fourier L¹ norms. -/
theorem summable_integral_norm_fourierInv_annularProduct (b : ContDiffBump (0 : E))
    {β : ℝ} (hβ : 0 < β) (φ : SchwartzMap E ℂ) :
    Summable (fun j : ℕ => ∫ x, ‖𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ)
      (annularTerm b β j) φ) x‖) := by
  have hr : |(2 : ℝ) ^ (-β)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hβ)
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun x => norm_nonneg _))
    (fun j => ?_) ((summable_geometric_of_abs_lt_one hr).mul_right
      ((∫ x, ‖𝓕⁻ (annularRpow b β) x‖) * (∫ x, ‖𝓕⁻ φ x‖)))
  calc
    _ ≤ (∫ x, ‖𝓕⁻ (annularTerm b β j) x‖) * (∫ x, ‖𝓕⁻ φ x‖) :=
      integral_norm_fourierInv_pairing_le _ _
    _ = _ := by rw [integral_norm_fourierInv_annularTerm]; ring

/-- The inverse Fourier transform of the cutoff multiplier equals the sum of the annular transforms. -/
theorem fourierInv_norm_rpow_cutoff_mul_eq_tsum (b : ContDiffBump (0 : E))
    {β : ℝ} (hβ : 0 < β) (φ : SchwartzMap E ℂ) (x : E) :
    𝓕⁻ (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) x =
      ∑' j : ℕ, 𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) (annularTerm b β j) φ) x := by
  let r : ℝ := (2 : ℝ) ^ (-β)
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 (annularRpow b β)
  have hr : |r| < 1 := by
    dsimp [r]
    rw [abs_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hβ)
  have hb (j : ℕ) (y : E) : ‖annularTerm b β j y * φ y‖ ≤ r ^ j * C * ‖φ y‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [annularTerm, smul_apply, dilate_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ (-β)) ^ j)]
    exact mul_le_mul_of_nonneg_left ((annularRpow b β).norm_le_seminorm ℝ _) (by positivity)
  have hs : HasSum (fun j : ℕ => ∫ y : E,
      Real.fourierChar (inner ℝ y x) • (annularTerm b β j y * φ y))
      (∫ y : E, Real.fourierChar (inner ℝ y x) •
        (((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y)) := by
    refine hasSum_integral_of_dominated_convergence (fun j y => r ^ j * C * ‖φ y‖)
      (fun j => by fun_prop) (fun j => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ((summable_geometric_of_abs_lt_one hr).mul_right C).mul_right ‖φ y‖)
      ?_ (Eventually.of_forall fun y => ?_)
    · simpa using hb j y
    · simp_rw [tsum_mul_right]
      exact φ.integrable.norm.const_mul _
    · exact ((hasSum_annularTerm b hβ y).mul_right (φ y)).const_smul _
  simpa only [fourierInv_coe, Real.fourierInv_eq, pairing_apply_apply,
    ContinuousLinearMap.mul_apply'] using hs.tsum_eq.symm

/-- The inverse Fourier transform of the singular cutoff multiplier is integrable. -/
theorem integrable_fourierInv_norm_rpow_cutoff_mul (b : ContDiffBump (0 : E))
    {β : ℝ} (hβ : 0 < β) (φ : SchwartzMap E ℂ) :
    Integrable (𝓕⁻ (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y)) := by
  have hi := integrable_tsum_of_summable_integral_norm
    (fun j : ℕ => (𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) (annularTerm b β j) φ)).continuous.measurable)
    (fun j : ℕ => (𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) (annularTerm b β j) φ)).integrable)
    (summable_integral_norm_fourierInv_annularProduct b hβ φ)
  exact hi.congr (Eventually.of_forall fun x => (fourierInv_norm_rpow_cutoff_mul_eq_tsum b hβ φ x).symm)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Away from a smooth cutoff, multiplying a Schwartz function by a norm power remains Schwartz. -/
theorem exists_far_norm_rpow_schwartz (β : ℝ) (φ : SchwartzMap E ℂ) :
    ∃ (b : ContDiffBump (0 : E)) (ψ : SchwartzMap E ℂ),
      ∀ x : E, ψ x = ((‖x‖ ^ β : ℝ) : ℂ) * (1 - (b x : ℂ)) * φ x := by
  let b : ContDiffBump (0 : E) := ⟨2, 3, by norm_num, by norm_num⟩
  let c : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let q : E → ℝ := fun x => ‖x‖ ^ 2 + c x
  have hc : (fun x : E => c x).HasTemperateGrowth := c.hasCompactSupport.hasTemperateGrowth c.contDiff
  have hb : (fun x : E => b x).HasTemperateGrowth := b.hasCompactSupport.hasTemperateGrowth b.contDiff
  have hq : q.HasTemperateGrowth := (Function.hasTemperateGrowth_norm_sq E).add hc
  have hq1 : ∀ x : E, 1 ≤ q x := by
    intro x
    dsimp only [q]
    by_cases hx : ‖x‖ ≤ 1
    · rw [c.one_of_mem_closedBall (by simpa [c, Metric.mem_closedBall, dist_zero_right] using hx)]
      nlinarith [sq_nonneg ‖x‖]
    · have hc0 := c.nonneg' x
      nlinarith [norm_nonneg x]
  have hp := hq.rpow_of_one_le hq1 (β / 2)
  have hm : (fun x : E => q x ^ (β / 2) * (1 - b x)).HasTemperateGrowth :=
    hp.mul ((by fun_prop : (fun _ : E => (1 : ℝ)).HasTemperateGrowth).sub hb)
  refine ⟨b, smulLeftCLM ℂ (fun x => q x ^ (β / 2) * (1 - b x)) φ, ?_⟩
  intro x
  rw [smulLeftCLM_apply_apply hm, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one]
  by_cases hx : b x = 1
  · simp [hx]
  have hnorm : 2 < ‖x‖ := by
    by_contra h
    apply hx
    exact b.one_of_mem_closedBall (by simpa [b, Metric.mem_closedBall, dist_zero_right] using (not_lt.mp h))
  have hcx : c x = 0 := c.zero_of_le_dist (by simpa [c, dist_zero_right] using hnorm.le)
  have heq : q x ^ (β / 2) = ‖x‖ ^ β := by
    dsimp only [q]
    rw [hcx, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  rw [heq]

/-- A nonnegative norm power times a Schwartz function is integrable. -/
theorem integrable_norm_rpow_mul {β : ℝ} (hβ : 0 ≤ β) (φ : SchwartzMap E ℂ) :
    Integrable (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * φ y) := by
  obtain ⟨n, hn⟩ := exists_nat_ge β
  apply (φ.integrable.norm.add (φ.integrable_pow_mul volume n)).mono'
    (by fun_prop)
  filter_upwards with y
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  change ‖y‖ ^ β * ‖φ y‖ ≤ ‖φ y‖ + ‖y‖ ^ n * ‖φ y‖
  have hb : ‖y‖ ^ β ≤ 1 + ‖y‖ ^ n := by
    by_cases hy : ‖y‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg _) hy hβ).trans (le_add_of_nonneg_right (by positivity))
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy) hn
      rw [Real.rpow_natCast] at h
      exact h.trans (le_add_of_nonneg_left zero_le_one)
  nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg (φ y))]

/-- A positive fractional norm multiplier of a Schwartz function has integrable inverse Fourier transform. -/
theorem integrable_fourierInv_norm_rpow_mul {β : ℝ} (hβ : 0 < β) (φ : SchwartzMap E ℂ) :
    Integrable (𝓕⁻ (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * φ y)) := by
  obtain ⟨b, ψ, hψ⟩ := exists_far_norm_rpow_schwartz β φ
  have hi := integrable_fourierInv_norm_rpow_cutoff_mul b hβ φ
  have hnear : Integrable (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) := by
    have heq : (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) =
        (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * φ y) - ψ := by
      funext y
      simp only [Pi.sub_apply, hψ]
      ring
    rw [heq]
    exact (integrable_norm_rpow_mul hβ.le φ).sub ψ.integrable
  have hsum : (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * φ y) =
      (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) + ψ := by
    funext y
    simp only [Pi.add_apply, hψ]
    ring
  rw [hsum]
  have ha : 𝓕⁻ ((fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) + ψ) =
      𝓕⁻ (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * (b y : ℂ) * φ y) + 𝓕⁻ (ψ : E → ℂ) := by
    ext x
    simp only [Real.fourierInv_eq, Pi.add_apply, smul_add]
    apply integral_add
    · simpa only [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-x)).mpr hnear
    · simpa only [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-x)).mpr ψ.integrable
  rw [ha]
  exact hi.add (by simpa only [← fourierInv_coe] using (𝓕⁻ ψ).integrable)

/-- A positive fractional norm multiplier of a Schwartz function has integrable Fourier transform. -/
theorem integrable_fourier_norm_rpow_mul {β : ℝ} (hβ : 0 < β) (φ : SchwartzMap E ℂ) :
    Integrable (𝓕 (fun y : E => ((‖y‖ ^ β : ℝ) : ℂ) * φ y)) := by
  have h := (integrable_fourierInv_norm_rpow_mul hβ φ).comp_neg
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using h

end SchwartzMap

