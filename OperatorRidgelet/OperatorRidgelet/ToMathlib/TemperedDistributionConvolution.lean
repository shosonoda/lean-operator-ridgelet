import OperatorRidgelet.ToMathlib.TemperedDistributionTranslate
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pairing a tempered distribution with a convolution

For `u ∈ 𝓢'(ℝ, ℂ)`, a smooth compactly supported `η`, and a smooth compactly supported `T`,
the convolution `(u * η)(y) = u (η(y - ·))` pairs with `T` through the convolution of the test
functions:
`∫ T(y) u (η(y - ·)) dy = u (T ⋆ η(-·))` (`TemperedDistribution.integral_mul_apply_translate`).

The proof integrates the derivative of `y ↦ u (Ψ_y)`, where `Ψ_y = (1_{(-∞, y]} T) ⋆ η(-·)`,
which is `T(y) u (η(y - ·))` (`TemperedDistribution.hasDerivAt_apply_cutConv`): the difference
quotients of `y ↦ Ψ_y` converge in the Schwartz topology by a Lipschitz estimate
(`TemperedDistribution.seminorm_cutDiff_le`).  The derivatives of the convolutions are computed
with Mathlib's `HasCompactSupport.hasDerivAt_convolution_right`.

The module also contains the seminorm estimate for approximate identities: for a nonnegative
kernel `g` of integral one supported in `[-δ, δ]`, the Schwartz seminorms of `g ⋆ T - T` are
`O(δ)` (`TemperedDistribution.norm_iteratedDeriv_convolution_sub_le`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff NNReal Convolution Interval

namespace TemperedDistribution

/-- Multiplication, as the bilinear map of scalar convolutions. -/
local notation "mulL" => ContinuousLinearMap.mul ℝ ℂ

/-! ### Convolutions with a smooth compactly supported factor -/

/-- Convolution using complex multiplication is the usual convolution integral. -/
theorem convolution_mulL_apply (f g : ℝ → ℂ) (x : ℝ) : (f ⋆[mulL] g) x = ∫ t, f t * g (x - t) :=
  rfl

/-- The iterated derivatives of `f ⋆ g` fall on the smooth compactly supported factor `g`. -/
theorem iteratedDeriv_convolution_right {f g : ℝ → ℂ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (n : ℕ) :
    iteratedDeriv n (f ⋆[mulL] g) = f ⋆[mulL] iteratedDeriv n g := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact (HasCompactSupport.hasDerivAt_convolution_right mulL hf
      (hasCompactSupport_iteratedDeriv hcg n)
      ((contDiff_iteratedDeriv_of_contDiff hg n).of_le (WithTop.coe_le_coe.mpr le_top)) x).deriv

/-- The convolution of a compactly supported locally integrable function with a smooth
compactly supported function, as a Schwartz function. -/
def convolutionSchwartz (f g : ℝ → ℂ) (hf : LocallyIntegrable f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) : SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap (f := f ⋆[mulL] g) (hcf.convolution (L := mulL) hcg)
    (hcg.contDiff_convolution_right mulL hf hg)

/-- The underlying function of `convolutionSchwartz` is the convolution. -/
theorem coe_convolutionSchwartz {f g : ℝ → ℂ} (hf : LocallyIntegrable f)
    (hcf : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ⇑(convolutionSchwartz f g hf hcf hg hcg) = f ⋆[mulL] g :=
  rfl

/-- Reflection preserves smoothness. -/
theorem contDiff_reflect {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ fun t => η (-t) :=
  hη.comp contDiff_neg

/-- Reflection preserves compact support. -/
theorem hasCompactSupport_reflect {η : ℝ → ℂ} (hcη : HasCompactSupport η) :
    HasCompactSupport fun t => η (-t) :=
  hcη.comp_homeomorph (Homeomorph.neg ℝ)

/-- A smooth compactly supported function times a smooth function of `t - x` is integrable. -/
theorem integrable_mul_shift {T g : ℝ → ℂ} (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) : Integrable fun t => T t * g (t - x) :=
  (hT.continuous.mul (hg.continuous.comp (continuous_id.sub continuous_const)))
    |>.integrable_of_hasCompactSupport hcT.mul_right

/-- A Lipschitz bound for `t ↦ T(t) g(t - x)`, uniform in `x`. -/
theorem exists_lipschitz_mul_shift {T g : ℝ → ℂ} (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x t y : ℝ, ‖T t * g (t - x) - T y * g (y - x)‖ ≤ L * |t - y| := by
  obtain ⟨M0, hM0, hT0⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hT hcT 0
  obtain ⟨M1, hM1, hT1⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hT hcT 1
  obtain ⟨N0, hN0, hg0⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hg hcg 0
  obtain ⟨N1, hN1, hg1⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hg hcg 1
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hT0 hT1 hg0 hg1
  have hTd : Differentiable ℝ T :=
    (hT.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 1 T).differentiable one_ne_zero
  have hgd : Differentiable ℝ g :=
    (hg.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 1 g).differentiable one_ne_zero
  refine ⟨M1 * N0 + M0 * N1, by positivity, fun x t y => ?_⟩
  have hderiv : ∀ s ∈ Set.uIcc y t, HasDerivWithinAt (fun s => T s * g (s - x))
      (deriv T s * g (s - x) + T s * deriv g (s - x)) (Set.uIcc y t) s := by
    intro s _
    have h1 : HasDerivAt (fun s => g (s - x)) (deriv g (s - x)) s := by
      have := (hgd (s - x)).hasDerivAt.scomp s ((hasDerivAt_id s).sub_const x)
      rw [one_smul] at this
      exact this
    exact ((hTd s).hasDerivAt.mul h1).hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv (fun s _ => by
    calc ‖deriv T s * g (s - x) + T s * deriv g (s - x)‖
        ≤ ‖deriv T s‖ * ‖g (s - x)‖ + ‖T s‖ * ‖deriv g (s - x)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M1 * N0 + M0 * N1 :=
          add_le_add (mul_le_mul (hT1 s) (hg0 _) (norm_nonneg _) hM1)
            (mul_le_mul (hT0 s) (hg1 _) (norm_nonneg _) hM0)) (convex_uIcc y t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-! ### The cut-off convolutions `Ψ_y = (1_{(-∞, y]} T) ⋆ η(-·)` -/

section CutConv

variable {η T : ℝ → ℂ}

/-- Restricting a smooth function to a closed half-line preserves local integrability. -/
theorem locallyIntegrable_indicator_Iic (hT : ContDiff ℝ ∞ T) (y : ℝ) :
    LocallyIntegrable ((Iic y).indicator T) :=
  hT.continuous.locallyIntegrable.indicator measurableSet_Iic

/-- Restricting a compactly supported function to a half-line preserves compact support. -/
theorem hasCompactSupport_indicator_Iic (hcT : HasCompactSupport T) (y : ℝ) :
    HasCompactSupport ((Iic y).indicator T) :=
  hcT.mono (by
    rw [Set.support_indicator]
    exact inter_subset_right)

/-- `Ψ_y = (1_{(-∞, y]} T) ⋆ η(-·)` as a Schwartz function. -/
def cutConv (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hT : ContDiff ℝ ∞ T)
    (hcT : HasCompactSupport T) (y : ℝ) : SchwartzMap ℝ ℂ :=
  convolutionSchwartz ((Iic y).indicator T) (fun t => η (-t))
    (locallyIntegrable_indicator_Iic hT y) (hasCompactSupport_indicator_Iic hcT y)
    (contDiff_reflect hη) (hasCompactSupport_reflect hcη)

/-- The iterated derivative of `Ψ_y`. -/
theorem iteratedDeriv_cutConv (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T) (y : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (cutConv hη hcη hT hcT y) x =
      (-1 : ℂ) ^ n * ∫ t in Iic y, T t * iteratedDeriv n η (t - x) := by
  rw [cutConv, coe_convolutionSchwartz,
    iteratedDeriv_convolution_right (locallyIntegrable_indicator_Iic hT y) (contDiff_reflect hη)
      (hasCompactSupport_reflect hcη), convolution_mulL_apply,
    ← integral_indicator measurableSet_Iic, ← integral_const_mul]
  congr 1
  funext t
  rw [iteratedDeriv_comp_neg, neg_sub, Set.indicator_mul_left, Complex.real_smul]
  push_cast
  ring

/-- The second order difference `Ψ_{y+h} - Ψ_y - h T(y) η(y - ·)`. -/
def cutDiff (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hT : ContDiff ℝ ∞ T)
    (hcT : HasCompactSupport T) (y h : ℝ) : SchwartzMap ℝ ℂ :=
  cutConv hη hcη hT hcT (y + h) - cutConv hη hcη hT hcT y - ((h : ℂ) * T y) • translate η y

/-- The derivative of the convolution remainder is the integral of its derivative difference. -/
theorem iteratedDeriv_cutDiff (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T) (y h : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (cutDiff hη hcη hT hcT y h) x = (-1 : ℂ) ^ n *
      ∫ t in y..(y + h), (T t * iteratedDeriv n η (t - x) - T y * iteratedDeriv n η (y - x)) := by
  have hgs : ContDiff ℝ ∞ (iteratedDeriv n η) := contDiff_iteratedDeriv_of_contDiff hη n
  have hint : ∀ y : ℝ, IntegrableOn (fun t => T t * iteratedDeriv n η (t - x)) (Iic y) := fun y =>
    (integrable_mul_shift hT hcT hgs x).integrableOn
  have h1 : ContDiff ℝ n ⇑(cutConv hη hcη hT hcT (y + h)) :=
    (cutConv hη hcη hT hcT (y + h)).smooth n
  have h2 : ContDiff ℝ n ⇑(cutConv hη hcη hT hcT y) := (cutConv hη hcη hT hcT y).smooth n
  have h3 : ContDiff ℝ n fun x => η (y - x) :=
    (hη.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_const.sub contDiff_id)
  have hcoe : ⇑(cutDiff hη hcη hT hcT y h) = (⇑(cutConv hη hcη hT hcT (y + h)) -
      ⇑(cutConv hη hcη hT hcT y)) - fun x => ((h : ℂ) * T y) • η (y - x) := by
    funext x
    simp only [cutDiff, sub_apply, smul_apply, Pi.sub_apply, translate_apply hη hcη]
  rw [hcoe, iteratedDeriv_sub_apply' (f := ⇑(cutConv hη hcη hT hcT (y + h)) -
    ⇑(cutConv hη hcη hT hcT y)) (h1.sub h2) (h3.const_smul _), iteratedDeriv_sub_apply' h1 h2,
    iteratedDeriv_const_smul' h3, iteratedDeriv_cutConv, iteratedDeriv_cutConv,
    iteratedDeriv_comp_const_sub, intervalIntegral.integral_sub
      (integrable_mul_shift hT hcT hgs x).intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const,
    ← intervalIntegral.integral_Iic_sub_Iic (hint y) (hint (y + h)), add_sub_cancel_left]
  simp only [smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- The Schwartz seminorms of the second order difference are `O(h²)`. -/
theorem seminorm_cutDiff_le (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T) (y : ℝ) (k n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (cutDiff hη hcη hT hcT y h) ≤ K * h ^ 2 := by
  obtain ⟨Rη, hRη⟩ := hcη.isBounded.subset_closedBall 0
  set g := iteratedDeriv n η with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_iteratedDeriv_of_contDiff hη n
  have hgc : HasCompactSupport g := hasCompactSupport_iteratedDeriv hcη n
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_mul_shift hT hcT hgs hgc
  have hgzero : ∀ z : ℝ, |Rη| < |z| → g z = 0 := fun z hz => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hRη (tsupport_iteratedDeriv_subset n hmem)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self Rη]
  refine ⟨(|y| + 1 + |Rη|) ^ k * L, by positivity, fun h hh => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (by positivity)
  intro x
  rw [iteratedDeriv_cutDiff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hmem : ∀ t ∈ Ι y (y + h), |t - y| ≤ |h| := by
    intro t ht
    rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact abs_le.mpr ⟨by linarith [neg_abs_le h, le_abs_self h],
        by linarith [neg_abs_le h, le_abs_self h]⟩
  by_cases hx : |x| ≤ |y| + 1 + |Rη|
  · have hb : ‖∫ t in y..(y + h), (T t * g (t - x) - T y * g (y - x))‖ ≤
        (L * |h|) * |y + h - y| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t ht =>
        (hL x t y).trans (mul_le_mul_of_nonneg_left (hmem t ht) hL0)
    rw [add_sub_cancel_left] at hb
    calc |x| ^ k * ‖∫ t in y..(y + h), (T t * g (t - x) - T y * g (y - x))‖
        ≤ (|y| + 1 + |Rη|) ^ k * (L * |h| * |h|) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx k) hb (norm_nonneg _) (by positivity)
      _ = (|y| + 1 + |Rη|) ^ k * L * h ^ 2 := by
          rw [mul_assoc, ← sq_abs h, sq]
          ring
  · rw [not_le] at hx
    have hzero : ∀ t ∈ Ι y (y + h), T t * g (t - x) - T y * g (y - x) = 0 := by
      intro t ht
      have ht' := hmem t ht
      have e1 : g (t - x) = 0 := hgzero _ (by
        have e := abs_sub_abs_le_abs_sub x t
        have e' := abs_sub_abs_le_abs_sub t y
        rw [abs_sub_comm x t] at e
        linarith)
      have e2 : g (y - x) = 0 := hgzero _ (by
        have e := abs_sub_abs_le_abs_sub x y
        rw [abs_sub_comm x y] at e
        linarith)
      rw [e1, e2, mul_zero, mul_zero, sub_zero]
    have hb : ‖∫ t in y..(y + h), (T t * g (t - x) - T y * g (y - x))‖ ≤ 0 * |y + h - y| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
        rw [hzero t ht, norm_zero]
    rw [zero_mul] at hb
    calc |x| ^ k * ‖∫ t in y..(y + h), (T t * g (t - x) - T y * g (y - x))‖
        ≤ |x| ^ k * 0 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 0 := mul_zero _
      _ ≤ (|y| + 1 + |Rη|) ^ k * L * h ^ 2 := by positivity

/-- `y ↦ u (Ψ_y)` is differentiable with derivative `T(y) u (η(y - ·))`. -/
theorem hasDerivAt_apply_cutConv (u : TemperedDistribution ℝ ℂ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T) (y : ℝ) :
    HasDerivAt (fun y => u (cutConv hη hcη hT hcT y)) (T y * u (translate η y)) y := by
  obtain ⟨s, C, hC0, hC⟩ := exists_seminorm_bound u
  have hK : ∀ m : ℕ × ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 →
      SchwartzMap.seminorm ℂ m.1 m.2 (cutDiff hη hcη hT hcT y h) ≤ K * h ^ 2 :=
    fun m => seminorm_cutDiff_le hη hcη hT hcT y m.1 m.2
  choose K hK0 hK using hK
  set K' := ∑ m ∈ s, K m with hK'
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun m _ => hK0 m
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hΔ : (fun h : ℝ => u (cutConv hη hcη hT hcT (y + h)) - u (cutConv hη hcη hT hcT y) -
      h • (T y * u (translate η y))) = fun h => u (cutDiff hη hcη hT hcT y h) := by
    funext h
    simp only [cutDiff, map_sub, map_smul, smul_eq_mul, Complex.real_smul]
    ring
  rw [hΔ, isLittleO_iff]
  intro c hc'
  have hlim : Tendsto (fun h : ℝ => C * K' * |h|) (𝓝 0) (𝓝 0) := by
    have := (continuous_const.mul continuous_abs).tendsto (0 : ℝ) (f := fun h : ℝ => C * K' * |h|)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hc'), Metric.ball_mem_nhds (0 : ℝ) one_pos]
    with h h1 h2
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
  calc ‖u (cutDiff hη hcη hT hcT y h)‖
      ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (cutDiff hη hcη hT hcT y h) := hC _
    _ ≤ C * (K' * h ^ 2) := by
        gcongr
        apply Seminorm.finset_sup_apply_le (by positivity)
        intro m hm
        calc schwartzSeminormFamily ℂ ℝ ℂ m (cutDiff hη hcη hT hcT y h) ≤ K m * h ^ 2 :=
              hK m h h2.le
          _ ≤ K' * h ^ 2 := by
              gcongr
              exact Finset.single_le_sum (f := K) (fun m _ => hK0 m) hm
    _ = (C * K' * |h|) * ‖h‖ := by
        rw [Real.norm_eq_abs, ← sq_abs]
        ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)

/-- **Pairing with a convolution**: `∫ T(y) u (η(y - ·)) dy = u (T ⋆ η(-·))`. -/
theorem integral_mul_apply_translate (u : TemperedDistribution ℝ ℂ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hT : ContDiff ℝ ∞ T) (hcT : HasCompactSupport T) :
    ∫ y, T y * u (translate η y) = u (convolutionSchwartz T (fun t => η (-t))
      hT.continuous.locallyIntegrable hcT (contDiff_reflect hη)
      (hasCompactSupport_reflect hcη)) := by
  obtain ⟨R, hR⟩ := hcT.isBounded.subset_closedBall 0
  set R' := |R| + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hTz : ∀ t : ℝ, R' ≤ |t| → T t = 0 := fun t ht => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self R]
  have hcont : Continuous fun y => T y * u (translate η y) :=
    hT.continuous.mul (contDiff_apply_translate u hη hcη).continuous
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -R') (b := R')
    (fun y _ => hasDerivAt_apply_cutConv u hη hcη hT hcT y) (hcont.intervalIntegrable _ _)
  have h1 : cutConv hη hcη hT hcT (-R') = 0 := by
    ext x
    change (((Iic (-R')).indicator T) ⋆[mulL] fun t => η (-t)) x = 0
    have : (Iic (-R')).indicator T = 0 := by
      funext t
      by_cases ht : t ∈ Iic (-R')
      · rw [Set.indicator_of_mem ht, hTz t (by
          rw [Set.mem_Iic] at ht
          rw [abs_of_nonpos (by linarith [hR'pos])]
          linarith)]
        rfl
      · rw [Set.indicator_of_notMem ht]
        rfl
    rw [this, zero_convolution]
    rfl
  have h2 : cutConv hη hcη hT hcT R' = convolutionSchwartz T (fun t => η (-t))
      hT.continuous.locallyIntegrable hcT (contDiff_reflect hη)
      (hasCompactSupport_reflect hcη) := by
    ext x
    change (((Iic R').indicator T) ⋆[mulL] fun t => η (-t)) x = (T ⋆[mulL] fun t => η (-t)) x
    have : (Iic R').indicator T = T := by
      funext t
      by_cases ht : t ∈ Iic R'
      · exact Set.indicator_of_mem ht _
      · rw [Set.indicator_of_notMem ht, hTz t (by
          rw [Set.mem_Iic, not_le] at ht
          rw [abs_of_pos (by linarith [hR'pos])]
          linarith)]
    rw [this]
  rw [h1, h2, map_zero, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_of_le (by linarith [hR'pos]),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro y hy
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
  rw [hTz y ?_, zero_mul]
  rcases hy with h | h
  · rw [abs_of_nonpos (by linarith [hR'pos])]
    linarith
  · rw [abs_of_pos (by linarith [hR'pos])]
    linarith

end CutConv

/-! ### Approximate identities -/

/-- For a smooth compactly supported `T` and a nonnegative kernel `g` of integral one supported
in `[-δ, δ]`, the weighted derivatives of `g ⋆ T - T` are `O(δ)`. -/
theorem norm_iteratedDeriv_convolution_sub_le {T : ℝ → ℂ} (hT : ContDiff ℝ ∞ T)
    (hcT : HasCompactSupport T) (k n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ s, 0 ≤ g s) → Integrable g →
      (∫ s, g s) = 1 → tsupport g ⊆ Metric.closedBall 0 δ →
      ∀ x : ℝ, |x| ^ k * ‖iteratedDeriv n (((fun s => (g s : ℂ)) ⋆[mulL] T) - T) x‖ ≤ K * δ := by
  obtain ⟨R, hR⟩ := hcT.isBounded.subset_closedBall 0
  set gn := iteratedDeriv n T with hgn
  have hgns : ContDiff ℝ ∞ gn := contDiff_iteratedDeriv_of_contDiff hT n
  have hgnc : HasCompactSupport gn := hasCompactSupport_iteratedDeriv hcT n
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hT hcT (n + 1)
  have hL : ∀ a b : ℝ, ‖gn a - gn b‖ ≤ M * |a - b| := by
    intro a b
    have hd : Differentiable ℝ gn :=
      (hgns.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 1 gn).differentiable one_ne_zero
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := gn)
      (f' := iteratedDeriv (n + 1) T) (s := Set.uIcc b a)
      (fun z _ => by
        rw [iteratedDeriv_succ]
        exact (hd z).hasDerivAt.hasDerivWithinAt) (fun z _ => hM z) (convex_uIcc _ _)
      Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  have hzero : ∀ z : ℝ, |R| < |z| → gn z = 0 := fun z hz => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hR (tsupport_iteratedDeriv_subset n hmem)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self R]
  refine ⟨(|R| + 1) ^ k * M, by positivity, fun g δ hδ hδ1 hg0 hgi hg1 hgs x => ?_⟩
  have hgC : Integrable fun s => (g s : ℂ) := hgi.ofReal
  have hgl : LocallyIntegrable fun s => (g s : ℂ) := hgC.locallyIntegrable
  have hconv : ContDiff ℝ n ((fun s => (g s : ℂ)) ⋆[mulL] T) :=
    hcT.contDiff_convolution_right mulL hgl (hT.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgsδ : ∀ s, g s ≠ 0 → |s| ≤ δ := fun s hs => by
    have := hgs (subset_closure (Function.mem_support.mpr hs))
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have hgn_bdd : ∃ C, ∀ z, ‖gn z‖ ≤ C := by
    obtain ⟨C, _, hC⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hT hcT n
    exact ⟨C, hC⟩
  have hint1 : Integrable fun s => (g s : ℂ) * gn (x - s) := by
    obtain ⟨C, hC⟩ := hgn_bdd
    have hcont : Continuous fun s => gn (x - s) :=
      hgns.continuous.comp (continuous_const.sub continuous_id)
    exact hgC.mul_bdd hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => hC _)
  have hgn_x : ∫ s, (g s : ℂ) * gn x = gn x := by
    rw [integral_mul_const, integral_complex_ofReal, hg1, Complex.ofReal_one, one_mul]
  rw [iteratedDeriv_sub_apply' hconv (hT.of_le (WithTop.coe_le_coe.mpr le_top)),
    iteratedDeriv_convolution_right hgl hT hcT, convolution_mulL_apply]
  change |x| ^ k * ‖(∫ s, (g s : ℂ) * gn (x - s)) - gn x‖ ≤ (|R| + 1) ^ k * M * δ
  rw [← hgn_x, ← integral_sub hint1 (hgC.mul_const _)]
  have hpt : ∀ s, ‖(g s : ℂ) * gn (x - s) - (g s : ℂ) * gn x‖ ≤ g s * (M * δ) := by
    intro s
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 s)]
    by_cases hs : g s = 0
    · rw [hs]
      simp
    · apply mul_le_mul_of_nonneg_left _ (hg0 s)
      calc ‖gn (x - s) - gn x‖ ≤ M * |x - s - x| := hL _ _
        _ = M * |s| := by rw [sub_sub_cancel_left, abs_neg]
        _ ≤ M * δ := mul_le_mul_of_nonneg_left (hgsδ s hs) hM0
  have hb : ‖∫ s, ((g s : ℂ) * gn (x - s) - (g s : ℂ) * gn x)‖ ≤ M * δ := by
    calc ‖∫ s, ((g s : ℂ) * gn (x - s) - (g s : ℂ) * gn x)‖ ≤ ∫ s, g s * (M * δ) :=
          norm_integral_le_of_norm_le (hgi.mul_const _) (Filter.Eventually.of_forall hpt)
      _ = M * δ := by rw [integral_mul_const, hg1, one_mul]
  by_cases hx : |x| ≤ |R| + 1
  · calc |x| ^ k * ‖∫ s, ((g s : ℂ) * gn (x - s) - (g s : ℂ) * gn x)‖
        ≤ (|R| + 1) ^ k * (M * δ) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx k) hb (norm_nonneg _) (by positivity)
      _ = (|R| + 1) ^ k * M * δ := by ring
  · rw [not_le] at hx
    have hz : ∀ s, (g s : ℂ) * gn (x - s) - (g s : ℂ) * gn x = 0 := by
      intro s
      by_cases hs : g s = 0
      · rw [hs]
        simp
      · have h1 : gn (x - s) = 0 := hzero _ (by
          have := abs_sub_abs_le_abs_sub x s
          have := hgsδ s hs
          linarith)
        have h2 : gn x = 0 := hzero _ (by linarith)
        rw [h1, h2, mul_zero, sub_zero]
    simp only [hz, integral_zero, norm_zero, mul_zero]
    positivity

end TemperedDistribution
