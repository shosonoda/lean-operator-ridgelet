import OperatorRidgelet.ToMathlib.TemperedDistributionPointSupport
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of the convolution of a tempered distribution with a test function

For `u ∈ 𝓢'(ℝ, ℂ)` and a smooth compactly supported `η : ℝ → ℂ`, the translates
`η(w - ·)` are Schwartz functions (`TemperedDistribution.translate`), the function
`w ↦ u (η(w - ·))` is differentiable with derivative `u (η'(w - ·))`
(`TemperedDistribution.hasDerivAt_apply_translate`), and therefore smooth, with
`∂^n_w u (η(w - ·)) = u (η^{(n)}(w - ·))` (`TemperedDistribution.contDiff_apply_translate`).

The derivative is obtained from the bound of `u` by finitely many Schwartz seminorms
(`TemperedDistribution.exists_seminorm_bound`) and a second order Taylor estimate for the
difference quotients of the translates (`TemperedDistribution.seminorm_translate_sub_le`).
-/

noncomputable section

open Set Filter Topology Asymptotics
open scoped ContDiff NNReal

namespace TemperedDistribution

/-! ### Bounds -/

/-- A tempered distribution is bounded by finitely many Schwartz seminorms. -/
theorem exists_seminorm_bound (u : TemperedDistribution ℝ ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ φ : SchwartzMap ℝ ℂ,
      ‖u φ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ)
    ((normSeminorm ℂ ℂ).comp u.toLinearMap) (by
      change Continuous fun φ : SchwartzMap ℝ ℂ => ‖u φ‖
      exact u.continuous.norm)
  refine ⟨s, C, C.2, fun φ => ?_⟩
  have h := Seminorm.le_def.mp hC φ
  rw [Seminorm.comp_apply, smul_apply, coe_normSeminorm, NNReal.smul_def, smul_eq_mul] at h
  exact h

/-- The support of an iterated derivative is contained in the support of the function. -/
theorem tsupport_iteratedDeriv_subset {f : ℝ → ℂ} (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) n
  intro h
  apply hx
  rw [iteratedDeriv_eq_iteratedFDeriv, h]
  rfl

/-- A smooth compactly supported function has smooth compactly supported derivatives. -/
theorem contDiff_deriv_of_contDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (deriv η) :=
  (contDiff_infty_iff_deriv.mp hη).2

/-- Every iterated derivative of a smooth function is smooth. -/
theorem contDiff_iteratedDeriv_of_contDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n η) := by
  rw [iteratedDeriv_eq_iterate]
  exact hη.iterate_deriv n

/-- Every iterated derivative of a compactly supported function has compact support. -/
theorem hasCompactSupport_iteratedDeriv {η : ℝ → ℂ} (hc : HasCompactSupport η) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n η) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- A smooth compactly supported function on `ℝ` has bounded derivatives of all orders. -/
theorem exists_bound_iteratedDeriv_of_hasCompactSupport {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedDeriv j η x‖ ≤ M := by
  have hj : ContDiff ℝ j η := hη.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨M, hM⟩ := (ContDiff.continuous_iteratedFDeriv (m := j) le_rfl
    hj).bounded_above_of_compact_support (hc.iteratedFDeriv j)
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hM x).trans (le_max_left _ _)

/-- The iterated derivative of a difference. -/
theorem iteratedDeriv_sub_apply' {f g : ℝ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (x : ℝ) : iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simp only [iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt]
  rfl

/-- The iterated derivative of a scalar multiple. -/
theorem iteratedDeriv_const_smul' {f : ℝ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) (c : ℂ) (x : ℝ) :
    iteratedDeriv n (fun x => c • f x) x = c • iteratedDeriv n f x :=
  iteratedDeriv_const_smul hf.contDiffAt c

/-! ### A second order Taylor bound -/

/-- `‖g(y + h) - g(y) - h g'(y)‖ ≤ M h²` when `‖g''‖ ≤ M`. -/
theorem norm_sub_sub_smul_deriv_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv 2 g y‖ ≤ M) (y h : ℝ) :
    ‖g (y + h) - g y - h • deriv g y‖ ≤ M * h ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgd : Differentiable ℝ (deriv g) := by
    have := hg2.differentiable_iteratedDeriv' 1
    rwa [iteratedDeriv_one] at this
  have hderiv_bound : ∀ t : ℝ, ‖deriv g (y + t) - deriv g y‖ ≤ M * |t| := by
    intro t
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv g)
      (f' := iteratedDeriv 2 g) (s := Set.uIcc y (y + t)) (fun z _ => by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
        exact (hgd z).hasDerivAt.hasDerivWithinAt) (fun z _ => hM z) (convex_uIcc _ _)
      Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  have hF : ∀ t ∈ Set.uIcc 0 h, HasDerivWithinAt (fun t : ℝ => g (y + t) - g y - t • deriv g y)
      (deriv g (y + t) - deriv g y) (Set.uIcc 0 h) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => g (y + t)) (deriv g (y + t)) t := by
      have := ((hg1.differentiable one_ne_zero) (y + t)).hasDerivAt.scomp t
        ((hasDerivAt_id t).const_add y)
      rw [one_smul] at this
      exact this
    have h2 : HasDerivAt (fun t : ℝ => t • deriv g y) (deriv g y) t := by
      simpa using (hasDerivAt_id t).smul_const (deriv g y)
    exact ((h1.sub_const (g y)).sub h2).hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF (fun t ht =>
    (hderiv_bound t).trans (mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_uIcc_zero ht) hM0))
    (convex_uIcc 0 h) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [add_zero, sub_self, zero_smul, sub_zero, Real.norm_eq_abs] at this
  calc ‖g (y + h) - g y - h • deriv g y‖ ≤ M * |h| * |h| := this
    _ = M * h ^ 2 := by rw [mul_assoc, ← sq_abs, sq]

/-! ### Translates -/

/-- The translate `x ↦ η (w - x)` of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_translateFun {η : ℝ → ℂ} (hc : HasCompactSupport η) (w : ℝ) :
    HasCompactSupport fun x => η (w - x) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall w R) fun x hx => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h := hR hmem
  apply hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_sub_comm] at h
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact h

open Classical in
/-- The translate `x ↦ η (w - x)` of a smooth compactly supported function, as a Schwartz
function (and `0` if `η` is not smooth with compact support). -/
def translate (η : ℝ → ℂ) (w : ℝ) : SchwartzMap ℝ ℂ :=
  if h : ContDiff ℝ ∞ η ∧ HasCompactSupport η then
    HasCompactSupport.toSchwartzMap (f := fun x => η (w - x)) (hasCompactSupport_translateFun h.2 w)
      (h.1.comp (contDiff_const.sub contDiff_id))
  else 0

/-- The translated Schwartz function evaluates to `η (w - x)`. -/
theorem translate_apply {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (w x : ℝ) :
    translate η w x = η (w - x) := by
  rw [translate, dif_pos ⟨hη, hc⟩]
  rfl

/-- The underlying function of the Schwartz translate is `x ↦ η (w - x)`. -/
theorem coe_translate {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (w : ℝ) :
    ⇑(translate η w) = fun x => η (w - x) :=
  funext (translate_apply hη hc w)

/-- The second order difference of the translates. -/
def translateDiff (η : ℝ → ℂ) (w h : ℝ) : SchwartzMap ℝ ℂ :=
  translate η (w + h) - translate η w - (h : ℂ) • translate (deriv η) w

/-- The underlying function of the translation remainder is its pointwise difference. -/
theorem coe_translateDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (w h : ℝ) :
    ⇑(translateDiff η w h) =
      (fun x => η (w + h - x)) - (fun x => η (w - x)) - fun x => (h : ℂ) • deriv η (w - x) := by
  funext x
  simp only [translateDiff, sub_apply, smul_apply, Pi.sub_apply,
    translate_apply hη hc, translate_apply (contDiff_deriv_of_contDiff hη) hc.deriv]

/-- The iterated derivative of the second order difference of the translates. -/
theorem iteratedDeriv_translateDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (w h : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (translateDiff η w h) x = (-1 : ℝ) ^ n •
      (iteratedDeriv n η (w + h - x) - iteratedDeriv n η (w - x) -
        (h : ℂ) • iteratedDeriv (n + 1) η (w - x)) := by
  have hn : ContDiff ℝ n η := hη.of_le (WithTop.coe_le_coe.mpr le_top)
  have hn' : ContDiff ℝ n (deriv η) :=
    (contDiff_deriv_of_contDiff hη).of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiff ℝ n fun x => η (w + h - x) := hn.comp (contDiff_const.sub contDiff_id)
  have h2 : ContDiff ℝ n fun x => η (w - x) := hn.comp (contDiff_const.sub contDiff_id)
  have h3 : ContDiff ℝ n fun x => deriv η (w - x) := hn'.comp (contDiff_const.sub contDiff_id)
  rw [coe_translateDiff hη hc,
    iteratedDeriv_sub_apply' (f := (fun x => η (w + h - x)) - fun x => η (w - x)) (h1.sub h2)
      (h3.const_smul _),
    iteratedDeriv_sub_apply' h1 h2, iteratedDeriv_const_smul' h3,
    iteratedDeriv_comp_const_sub, iteratedDeriv_comp_const_sub, iteratedDeriv_comp_const_sub,
    ← iteratedDeriv_succ']
  simp only [smul_sub, smul_comm ((h : ℂ)) ((-1 : ℝ) ^ n)]

/-- The Schwartz seminorms of the second order difference of the translates are `O(h²)`. -/
theorem seminorm_translateDiff_le {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (w : ℝ) (k n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (translateDiff η w h) ≤ K * h ^ 2 := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDeriv_of_hasCompactSupport hη hc (n + 2)
  have hzero : ∀ j : ℕ, ∀ y : ℝ, |R| < |y| → iteratedDeriv j η y = 0 := by
    intro j y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hR (tsupport_iteratedDeriv_subset j hmem)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self R]
  refine ⟨(|w| + 1 + |R|) ^ k * M, by positivity, fun h hh => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (by positivity)
  intro x
  rw [iteratedDeriv_translateDiff hη hc, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  by_cases hx : |x| ≤ |w| + 1 + |R|
  · have htaylor := norm_sub_sub_smul_deriv_le (g := iteratedDeriv n η)
      (contDiff_iteratedDeriv_of_contDiff hη n) (M := M) (fun y => by
        have : iteratedDeriv 2 (iteratedDeriv n η) = iteratedDeriv (n + 2) η := by
          rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
            ← Function.iterate_add_apply, add_comm]
        rw [this]
        exact hM y) (w - x) h
    rw [show w - x + h = w + h - x by ring, ← iteratedDeriv_succ, Complex.real_smul] at htaylor
    calc |x| ^ k * ‖iteratedDeriv n η (w + h - x) - iteratedDeriv n η (w - x) -
          (h : ℂ) • iteratedDeriv (n + 1) η (w - x)‖
        ≤ (|w| + 1 + |R|) ^ k * (M * h ^ 2) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx k) htaylor (norm_nonneg _)
            (by positivity)
      _ = (|w| + 1 + |R|) ^ k * M * h ^ 2 := by ring
  · rw [not_le] at hx
    have h1 : iteratedDeriv n η (w + h - x) = 0 := hzero _ _ (by
      have e1 := abs_sub_abs_le_abs_sub x (w + h)
      have e2 := abs_add_le w h
      rw [abs_sub_comm x (w + h)] at e1
      linarith)
    have h2 : iteratedDeriv n η (w - x) = 0 := hzero _ _ (by
      have := abs_sub_abs_le_abs_sub x w
      rw [abs_sub_comm] at this
      linarith)
    have h3 : iteratedDeriv (n + 1) η (w - x) = 0 := hzero _ _ (by
      have := abs_sub_abs_le_abs_sub x w
      rw [abs_sub_comm] at this
      linarith)
    rw [h1, h2, h3]
    simp only [sub_zero, smul_zero, norm_zero, mul_zero]
    positivity

/-! ### The derivative of `w ↦ u (η(w - ·))` -/

/-- `w ↦ u (η(w - ·))` is differentiable with derivative `u (η'(w - ·))`. -/
theorem hasDerivAt_apply_translate (u : TemperedDistribution ℝ ℂ) {η : ℝ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (w : ℝ) :
    HasDerivAt (fun w => u (translate η w)) (u (translate (deriv η) w)) w := by
  obtain ⟨s, C, hC0, hC⟩ := exists_seminorm_bound u
  have hK : ∀ m : ℕ × ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 →
      SchwartzMap.seminorm ℂ m.1 m.2 (translateDiff η w h) ≤ K * h ^ 2 :=
    fun m => seminorm_translateDiff_le hη hc w m.1 m.2
  choose K hK0 hK using hK
  set K' := ∑ m ∈ s, K m with hK'
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun m _ => hK0 m
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hΔ : (fun h : ℝ => u (translate η (w + h)) - u (translate η w) -
      h • u (translate (deriv η) w)) = fun h => u (translateDiff η w h) := by
    funext h
    simp only [translateDiff, map_sub, map_smul, smul_eq_mul, Complex.real_smul]
  rw [hΔ, isLittleO_iff]
  intro c hc'
  have hlim : Tendsto (fun h : ℝ => C * K' * |h|) (𝓝 0) (𝓝 0) := by
    have := (continuous_const.mul continuous_abs).tendsto (0 : ℝ) (f := fun h : ℝ => C * K' * |h|)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hc'), Metric.ball_mem_nhds (0 : ℝ) one_pos]
    with h h1 h2
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
  calc ‖u (translateDiff η w h)‖
      ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (translateDiff η w h) := hC _
    _ ≤ C * (K' * h ^ 2) := by
        gcongr
        apply Seminorm.finset_sup_apply_le (by positivity)
        intro m hm
        calc schwartzSeminormFamily ℂ ℝ ℂ m (translateDiff η w h) ≤ K m * h ^ 2 := hK m h h2.le
          _ ≤ K' * h ^ 2 := by
              gcongr
              exact Finset.single_le_sum (f := K) (fun m _ => hK0 m) hm
    _ = (C * K' * |h|) * ‖h‖ := by
        rw [Real.norm_eq_abs, ← sq_abs]
        ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)

/-- `∂_w u (η(w - ·)) = u (η'(w - ·))`. -/
theorem deriv_apply_translate (u : TemperedDistribution ℝ ℂ) {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) :
    deriv (fun w => u (translate η w)) = fun w => u (translate (deriv η) w) :=
  funext fun w => (hasDerivAt_apply_translate u hη hc w).deriv

/-- `∂^n_w u (η(w - ·)) = u (η^{(n)}(w - ·))`. -/
theorem iteratedDeriv_apply_translate (u : TemperedDistribution ℝ ℂ) (n : ℕ) :
    ∀ {η : ℝ → ℂ}, ContDiff ℝ ∞ η → HasCompactSupport η →
      iteratedDeriv n (fun w => u (translate η w)) =
        fun w => u (translate (iteratedDeriv n η) w) := by
  induction n with
  | zero =>
    intro η _ _
    simp only [iteratedDeriv_zero]
  | succ n ih =>
    intro η hη hc
    rw [iteratedDeriv_succ', deriv_apply_translate u hη hc,
      ih (contDiff_deriv_of_contDiff hη) hc.deriv, ← iteratedDeriv_succ']

/-- **Smoothness of the convolution of a tempered distribution with a test function**:
`w ↦ u (η(w - ·))` is smooth for smooth compactly supported `η`. -/
theorem contDiff_apply_translate (u : TemperedDistribution ℝ ℂ) {η : ℝ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ContDiff ℝ ∞ (fun w => u (translate η w)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_apply_translate u m hη hc]
  exact fun w => (hasDerivAt_apply_translate u (contDiff_iteratedDeriv_of_contDiff hη m)
    (hasCompactSupport_iteratedDeriv hc m) w).differentiableAt

end TemperedDistribution
