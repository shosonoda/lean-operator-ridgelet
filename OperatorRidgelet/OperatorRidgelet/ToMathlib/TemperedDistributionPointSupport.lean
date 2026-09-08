import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Tempered distributions supported at the origin

A tempered distribution `u ∈ 𝓢'(ℝ, ℂ)` vanishing on every Schwartz function whose support avoids
`0` is a finite linear combination of derivatives of the Dirac mass at `0`:
`u φ = ∑_{k ≤ N} c_k φ^{(k)}(0)`
(`TemperedDistribution.exists_sum_iteratedDeriv_zero_of_forall_apply_eq_zero`).

The proof is the classical one.  Continuity of `u` bounds `‖u φ‖` by finitely many Schwartz
seminorms of orders `≤ N` (`Seminorm.bound_of_continuous`).  If `φ^{(k)}(0) = 0` for `k ≤ N`,
then `‖φ^{(m)}(x)‖ ≤ K |x|^{N+1-m}` for `m ≤ N` (`norm_iteratedDeriv_le_of_iteratedDeriv_zero`,
an iterated mean value bound), and with the cutoff `θ_ε(x) = θ(x/ε)` the seminorms of
`θ_ε φ` are `O(ε)` (`seminorm_cutoffMul_le`), while `u φ = u (θ_ε φ)` because `(1 - θ_ε) φ` is
supported away from `0`; hence `u φ = 0`.  Thus `u` factors through the linear map
`φ ↦ (φ^{(k)}(0))_{k ≤ N}` (`LinearMap.exists_comp_of_ker_le`).
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff NNReal

/-! ### Factoring a linear map through another with smaller kernel -/

/-- A linear map vanishing on the kernel of `T` factors through `T`. -/
theorem LinearMap.exists_comp_of_ker_le {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U] (T : V →ₗ[K] U) (u : V →ₗ[K] W)
    (h : LinearMap.ker T ≤ LinearMap.ker u) : ∃ c : U →ₗ[K] W, u = c ∘ₗ T := by
  let c₀ : LinearMap.range T →ₗ[K] W :=
    (Submodule.liftQ (LinearMap.ker T) u h) ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨c, hc⟩ := LinearMap.exists_extend c₀
  refine ⟨c, ?_⟩
  ext v
  have h1 : T v = (LinearMap.range T).subtype ⟨T v, LinearMap.mem_range_self T v⟩ := rfl
  rw [LinearMap.comp_apply, h1, ← LinearMap.comp_apply c, hc]
  simp only [c₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

namespace TemperedDistribution

/-! ### An iterated mean value bound -/

theorem abs_le_abs_of_mem_uIcc_zero {x y : ℝ} (hy : y ∈ Set.uIcc 0 x) : |y| ≤ |x| := by
  rcases Set.mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

/-- The mean value bound for `g^{(m)}` on the segment from `0` to `x`. -/
theorem norm_iteratedDeriv_sub_zero_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (m : ℕ) {x C : ℝ}
    (hC : ∀ y ∈ Set.uIcc 0 x, ‖iteratedDeriv (m + 1) g y‖ ≤ C) :
    ‖iteratedDeriv m g x - iteratedDeriv m g 0‖ ≤ C * |x| := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x,
      HasDerivWithinAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g y) (Set.uIcc 0 x) y := by
    intro y _
    have hd : Differentiable ℝ (iteratedDeriv m g) :=
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)).differentiable_iteratedDeriv' m
    rw [iteratedDeriv_succ]
    exact (hd y).hasDerivAt.hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hC (convex_uIcc 0 x)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-- If `g^{(k)}(0) = 0` for `k ≤ M` and `‖g^{(M+1)}‖ ≤ K`, then
`‖g^{(M-d)}(x)‖ ≤ K |x|^{d+1}` for `d ≤ M`. -/
theorem norm_iteratedDeriv_le_of_iteratedDeriv_zero {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {M : ℕ}
    (h0 : ∀ k ≤ M, iteratedDeriv k g 0 = 0) {K : ℝ}
    (hK : ∀ y : ℝ, ‖iteratedDeriv (M + 1) g y‖ ≤ K) :
    ∀ d ≤ M, ∀ x : ℝ, ‖iteratedDeriv (M - d) g x‖ ≤ K * |x| ^ (d + 1) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  intro d
  induction d with
  | zero =>
    intro _ x
    simpa [h0 M le_rfl] using norm_iteratedDeriv_sub_zero_le hg M (x := x) fun y _ => hK y
  | succ d ih =>
    intro hd x
    have hd' : d ≤ M := by omega
    have hsub : M - (d + 1) + 1 = M - d := by omega
    have := norm_iteratedDeriv_sub_zero_le hg (M - (d + 1)) (x := x) (C := K * |x| ^ (d + 1))
      (fun y hy => by
        rw [hsub]
        refine (ih hd' y).trans ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (abs_le_abs_of_mem_uIcc_zero hy) _) hK0)
    rw [h0 (M - (d + 1)) (Nat.sub_le _ _), sub_zero] at this
    calc ‖iteratedDeriv (M - (d + 1)) g x‖ ≤ K * |x| ^ (d + 1) * |x| := this
      _ = K * |x| ^ (d + 1 + 1) := by ring

/-! ### The cutoff `θ_ε` -/

/-- The bump equal to one on `[-1, 1]` and supported in `(-2, 2)`. -/
def unitBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }

/-- The rescaled cutoff `θ_ε(x) = θ(x/ε)`. -/
def cutoff (ε : ℝ) (x : ℝ) : ℝ := unitBump (ε⁻¹ * x)

theorem cutoff_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : |x| ≤ ε) : cutoff ε x = 1 := by
  apply unitBump.one_of_mem_closedBall
  change ε⁻¹ * x ∈ Metric.closedBall (0 : ℝ) 1
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hε),
    inv_mul_le_iff₀ hε, mul_one]
  exact hx

theorem cutoff_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : 2 * ε ≤ |x|) : cutoff ε x = 0 := by
  apply unitBump.zero_of_le_dist
  change (2 : ℝ) ≤ dist (ε⁻¹ * x) 0
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hε), le_inv_mul_iff₀ hε]
  linarith

theorem contDiff_cutoff (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff ε) := by
  unfold cutoff
  exact unitBump.contDiff.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_cutoff {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (cutoff ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ε)) fun x hx =>
    cutoff_eq_zero hε (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      exact hx.le)

theorem iteratedDeriv_cutoff (ε : ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (cutoff ε) x = ε⁻¹ ^ j * iteratedDeriv j unitBump (ε⁻¹ * x) :=
  congrFun (iteratedDeriv_comp_const_mul (unitBump.contDiff (n := j)) ε⁻¹) x

/-- The derivatives of the bump up to order `N` are uniformly bounded. -/
theorem exists_bound_iteratedDeriv_unitBump (N : ℕ) :
    ∃ Mθ : ℝ, 0 ≤ Mθ ∧ ∀ j ≤ N, ∀ x : ℝ, ‖iteratedDeriv j unitBump x‖ ≤ Mθ := by
  have hb : ∀ j : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedDeriv j unitBump x‖ ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (ContDiff.continuous_iteratedFDeriv (m := j) le_rfl
      (unitBump.contDiff (n := j))).bounded_above_of_compact_support
      (unitBump.hasCompactSupport.iteratedFDeriv j)
    exact ⟨M, fun x => by
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hM x⟩
  choose M hM using hb
  refine ⟨∑ j ∈ Finset.range (N + 1), |M j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro j hj x
  calc ‖iteratedDeriv j unitBump x‖ ≤ M j := hM j x
    _ ≤ |M j| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (N + 1), |M i| :=
        Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- The cutoff as a complex-valued function. -/
def cutoffC (ε : ℝ) (x : ℝ) : ℂ := (cutoff ε x : ℂ)

theorem contDiff_cutoffC (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoffC ε) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_cutoff ε)

theorem hasCompactSupport_cutoffC {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (cutoffC ε) :=
  (hasCompactSupport_cutoff hε).comp_left Complex.ofReal_zero

theorem hasTemperateGrowth_cutoffC {ε : ℝ} (hε : 0 < ε) :
    Function.HasTemperateGrowth (cutoffC ε) :=
  (hasCompactSupport_cutoffC hε).hasTemperateGrowth (contDiff_cutoffC ε)

theorem norm_iteratedFDeriv_cutoffC (ε : ℝ) (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (cutoffC ε) x‖ = ‖iteratedDeriv i (cutoff ε) x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_cutoff ε (n := i)).contDiffAt
    le_rfl

/-- The product of a Schwartz function with the cutoff `θ_ε`. -/
def cutoffMul (ε : ℝ) (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (cutoffC ε) φ

theorem cutoffMul_apply {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    cutoffMul ε φ x = cutoffC ε x * φ x := by
  rw [cutoffMul, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_cutoffC hε), smul_eq_mul]

theorem coe_cutoffMul {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    ⇑(cutoffMul ε φ) = fun x => cutoffC ε x * φ x :=
  funext (cutoffMul_apply hε φ)

theorem tsupport_cutoffMul_subset {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    tsupport (cutoffMul ε φ) ⊆ Metric.closedBall 0 (2 * ε) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hx'
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx'
  apply hx
  rw [cutoffMul_apply hε, cutoffC, cutoff_eq_zero hε hx'.le]
  simp

/-! ### The seminorm estimate -/

/-- One term of the Leibniz bound for `θ_ε φ`. -/
theorem cutoff_term_le {φ : SchwartzMap ℝ ℂ} {N : ℕ} {K Mθ : ℝ} (hMθ0 : 0 ≤ Mθ)
    (hMθ : ∀ j ≤ N, ∀ x : ℝ, ‖iteratedDeriv j unitBump x‖ ≤ Mθ) (hK0 : 0 ≤ K)
    (htaylor : ∀ d ≤ N, ∀ x : ℝ, ‖iteratedDeriv (N - d) φ x‖ ≤ K * |x| ^ (d + 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℝ} (hx : |x| ≤ 2 * ε) {i n : ℕ} (hi : i ≤ n)
    (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ i (cutoffC ε) x‖ * ‖iteratedFDeriv ℝ (n - i) φ x‖ ≤
      2 ^ (N + 1) * Mθ * K * ε := by
  have h1 : ‖iteratedFDeriv ℝ i (cutoffC ε) x‖ ≤ ε⁻¹ ^ i * Mθ := by
    rw [norm_iteratedFDeriv_cutoffC, iteratedDeriv_cutoff, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)]
    gcongr
    exact hMθ i (hi.trans hn) _
  have h2 : ‖iteratedFDeriv ℝ (n - i) φ x‖ ≤ K * |x| ^ (N + 1 - (n - i)) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have := htaylor (N - (n - i)) (Nat.sub_le _ _) x
    rw [show N - (N - (n - i)) = n - i by omega, show N - (n - i) + 1 = N + 1 - (n - i) by omega]
      at this
    exact this
  have h3 : |x| ^ (N + 1 - (n - i)) ≤ 2 ^ (N + 1) * ε ^ (N + 1 - (n - i)) := by
    calc |x| ^ (N + 1 - (n - i)) ≤ (2 * ε) ^ (N + 1 - (n - i)) :=
          pow_le_pow_left₀ (abs_nonneg _) hx _
      _ = 2 ^ (N + 1 - (n - i)) * ε ^ (N + 1 - (n - i)) := mul_pow _ _ _
      _ ≤ 2 ^ (N + 1) * ε ^ (N + 1 - (n - i)) := by
          gcongr
          · norm_num
          · omega
  have h4 : ε⁻¹ ^ i * ε ^ (N + 1 - (n - i)) ≤ ε := by
    rw [show N + 1 - (n - i) = (N + 1 - n) + i by omega, pow_add, ← mul_assoc,
      mul_comm (ε⁻¹ ^ i), mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
    exact pow_le_of_le_one hε.le hε1 (by omega)
  calc ‖iteratedFDeriv ℝ i (cutoffC ε) x‖ * ‖iteratedFDeriv ℝ (n - i) φ x‖
      ≤ (ε⁻¹ ^ i * Mθ) * (K * |x| ^ (N + 1 - (n - i))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (ε⁻¹ ^ i * Mθ) * (K * (2 ^ (N + 1) * ε ^ (N + 1 - (n - i)))) := by gcongr
    _ = 2 ^ (N + 1) * Mθ * K * (ε⁻¹ ^ i * ε ^ (N + 1 - (n - i))) := by ring
    _ ≤ 2 ^ (N + 1) * Mθ * K * ε := by gcongr

/-- The Schwartz seminorms of `θ_ε φ` of orders `≤ N` are `O(ε)` when `φ` vanishes to order
`N` at the origin. -/
theorem seminorm_cutoffMul_le (φ : SchwartzMap ℝ ℂ) {N : ℕ}
    (h0 : ∀ k ≤ N, iteratedDeriv k φ 0 = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k n : ℕ, k ≤ N → n ≤ N →
      SchwartzMap.seminorm ℂ k n (cutoffMul ε φ) ≤ D * ε := by
  obtain ⟨Mθ, hMθ0, hMθ⟩ := exists_bound_iteratedDeriv_unitBump N
  set K := SchwartzMap.seminorm ℂ 0 (N + 1) φ with hK
  have hK0 : 0 ≤ K := apply_nonneg _ _
  have hKb : ∀ y, ‖iteratedDeriv (N + 1) φ y‖ ≤ K := fun y => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ (N + 1) y
  have htaylor := norm_iteratedDeriv_le_of_iteratedDeriv_zero (φ.smooth ⊤) h0 hKb
  refine ⟨2 ^ (3 * N + 1) * Mθ * K, by positivity, ?_⟩
  intro ε hε hε1 k n hk hn
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (by positivity)
  intro x
  by_cases hx : 2 * ε < |x|
  · have hzero : iteratedDeriv n (cutoffMul ε φ) x = 0 := by
      have hF : iteratedFDeriv ℝ n (cutoffMul ε φ) x = 0 := by
        by_contra hne
        have hmem := tsupport_cutoffMul_subset hε φ (support_iteratedFDeriv_subset n hne)
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
        linarith
      rw [iteratedDeriv_eq_iteratedFDeriv, hF]
      rfl
    rw [hzero, norm_zero, mul_zero]
    positivity
  · rw [not_lt] at hx
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, coe_cutoffMul hε]
    have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (contDiff_cutoffC ε (n := n)) (φ.smooth n)
      x (n := n) le_rfl
    have hxk : |x| ^ k ≤ 2 ^ N := by
      calc |x| ^ k ≤ 2 ^ k := pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk
    calc |x| ^ k * ‖iteratedFDeriv ℝ n (fun y => cutoffC ε y * φ y) x‖
        ≤ 2 ^ N * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (cutoffC ε) x‖ * ‖iteratedFDeriv ℝ (n - i) φ x‖ :=
          mul_le_mul hxk hleib (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ N * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 ^ (N + 1) * Mθ * K * ε) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro i hi
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (cutoff_term_le hMθ0 hMθ hK0 htaylor hε hε1 hx
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hn) (by positivity)
      _ = 2 ^ N * 2 ^ n * (2 ^ (N + 1) * Mθ * K * ε) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ 2 ^ N * 2 ^ N * (2 ^ (N + 1) * Mθ * K * ε) := by
          gcongr
          · norm_num
      _ = 2 ^ (3 * N + 1) * Mθ * K * ε := by ring

/-! ### Vanishing on functions flat at the origin -/

/-- A tempered distribution vanishing on Schwartz functions supported away from `0`, and
bounded by seminorms of orders `≤ N`, vanishes on Schwartz functions vanishing to order `N`
at `0`. -/
theorem apply_eq_zero_of_iteratedDeriv_zero (u : TemperedDistribution ℝ ℂ)
    (hu : ∀ φ : SchwartzMap ℝ ℂ, (0 : ℝ) ∉ tsupport φ → u φ = 0) {s : Finset (ℕ × ℕ)} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ φ, ‖u φ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ) {N : ℕ}
    (hs : ∀ m ∈ s, m.1 ≤ N ∧ m.2 ≤ N) (φ : SchwartzMap ℝ ℂ)
    (h0 : ∀ k ≤ N, iteratedDeriv k φ 0 = 0) : u φ = 0 := by
  obtain ⟨D, hD0, hD⟩ := seminorm_cutoffMul_le φ h0
  have hcut : ∀ ε, 0 < ε → u φ = u (cutoffMul ε φ) := by
    intro ε hε
    have h := hu (φ - cutoffMul ε φ) (by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
      simp [cutoffMul_apply hε, cutoffC, cutoff_eq_one hε hx.le])
    rw [map_sub, sub_eq_zero] at h
    exact h
  have hbound : ∀ ε, 0 < ε → ε ≤ 1 → ‖u φ‖ ≤ (C * D) * ε := by
    intro ε hε hε1
    rw [hcut ε hε]
    calc ‖u (cutoffMul ε φ)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (cutoffMul ε φ) := hC _
      _ ≤ C * (D * ε) := by
          gcongr
          apply Seminorm.finset_sup_apply_le (by positivity)
          intro m hm
          exact hD ε hε hε1 m.1 m.2 (hs m hm).1 (hs m hm).2
      _ = (C * D) * ε := by ring
  have hC'0 : 0 ≤ C * D := by positivity
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < min 1 (δ / (C * D + 1)) := lt_min one_pos (by positivity)
  calc ‖u φ‖ ≤ (C * D) * min 1 (δ / (C * D + 1)) :=
        hbound _ hε (min_le_left _ _)
    _ ≤ (C * D) * (δ / (C * D + 1)) := by
        gcongr
        exact min_le_right _ _
    _ ≤ δ := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
    _ = 0 + δ := (zero_add δ).symm

/-! ### The cutoff at infinity -/

theorem tsupport_cutoffMul_subset_tsupport {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    tsupport (cutoffMul ε φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hx'
  apply hx
  rw [cutoffMul_apply hε, image_eq_zero_of_notMem_tsupport hx', mul_zero]

theorem hasCompactSupport_cutoffMul {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    HasCompactSupport (cutoffMul ε φ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (2 * ε))
    (subset_closure.trans (tsupport_cutoffMul_subset hε φ))

/-- The Schwartz seminorms of `φ - θ_R φ` are `O(1/R)`. -/
theorem seminorm_sub_cutoffMul_le (φ : SchwartzMap ℝ ℂ) (k n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      SchwartzMap.seminorm ℂ k n (φ - cutoffMul R φ) ≤ D / R := by
  obtain ⟨Mθ, hMθ0, hMθ⟩ := exists_bound_iteratedDeriv_unitBump n
  set K := ∑ i ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ (k + 1) i φ with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have hK : ∀ i ≤ n, ∀ x : ℝ, ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ i φ x‖ ≤ K := by
    intro i hi x
    calc ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ i φ x‖ ≤ SchwartzMap.seminorm ℂ (k + 1) i φ :=
          SchwartzMap.le_seminorm ℂ (k + 1) i φ x
      _ ≤ K := Finset.single_le_sum (f := fun i => SchwartzMap.seminorm ℂ (k + 1) i φ)
          (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨2 ^ n * (1 + Mθ) * K, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  by_cases hx : |x| < R
  · have hF : iteratedFDeriv ℝ n (φ - cutoffMul R φ) x = 0 := by
      by_contra hne
      have hmem := support_iteratedFDeriv_subset n hne
      have hsub : tsupport (φ - cutoffMul R φ) ⊆ {y : ℝ | R ≤ |y|} := by
        apply closure_minimal _ (isClosed_le continuous_const continuous_abs)
        intro y hy
        by_contra h
        rw [Set.mem_setOf_eq, not_le] at h
        apply hy
        simp [cutoffMul_apply hRpos, cutoffC, cutoff_eq_one hRpos h.le]
      exact absurd (hsub hmem) (not_le.mpr hx)
    rw [hF, norm_zero, mul_zero]
    positivity
  · rw [not_lt] at hx
    have hcoe : ⇑(φ - cutoffMul R φ) = fun y => (1 - cutoffC R y) * φ y := by
      funext y
      rw [sub_apply, cutoffMul_apply hRpos]
      ring
    rw [hcoe]
    have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y => 1 - cutoffC R y)
      (contDiff_const.sub (contDiff_cutoffC R (n := n))) (φ.smooth n) x (n := n) le_rfl
    have hθ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y => 1 - cutoffC R y) x‖ ≤ 1 + Mθ := by
      intro i hi
      change ‖iteratedFDeriv ℝ i ((fun _ : ℝ => (1 : ℂ)) - cutoffC R) x‖ ≤ 1 + Mθ
      rw [iteratedFDeriv_sub_apply contDiffAt_const (contDiff_cutoffC R (n := i)).contDiffAt]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rcases i with _ | i
        · simp
        · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i)]
          simp
      · rw [norm_iteratedFDeriv_cutoffC, iteratedDeriv_cutoff, norm_mul, norm_pow,
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
        calc R⁻¹ ^ i * ‖iteratedDeriv i unitBump (R⁻¹ * x)‖ ≤ 1 ^ i * Mθ := by
              gcongr
              · exact inv_le_one_of_one_le₀ hR
              · exact hMθ i hi _
          _ = Mθ := by rw [one_pow, one_mul]
    have hφ : ∀ i ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) φ x‖ ≤ K / R := by
      intro i hi
      have hxpos : 0 < ‖x‖ := by rw [Real.norm_eq_abs]; linarith
      have hxR : R ≤ ‖x‖ := by rw [Real.norm_eq_abs]; exact hx
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) φ x‖
          = (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) φ x‖) / ‖x‖ := by
            rw [pow_succ]
            field_simp
        _ ≤ K / ‖x‖ := by gcongr; exact hK (n - i) (Nat.sub_le _ _) x
        _ ≤ K / R := div_le_div_of_nonneg_left hK0 hRpos hxR
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (1 - cutoffC R y) * φ y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => 1 - cutoffC R y) x‖ * ‖iteratedFDeriv ℝ (n - i) φ x‖ :=
          mul_le_mul_of_nonneg_left hleib (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => 1 - cutoffC R y) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) φ x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + Mθ) * (K / R) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hθ i hi') (by positivity)) (hφ i hi')
            (by positivity) (by positivity)
      _ = 2 ^ n * (1 + Mθ) * K / R := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring

/-- The cutoffs `θ_R φ` converge to `φ` in the Schwartz space as `R → ∞`. -/
theorem tendsto_cutoffMul_atTop (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun R : ℝ => cutoffMul R φ) atTop (𝓝 φ) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  intro m ε hε
  obtain ⟨D, hD0, hD⟩ := seminorm_sub_cutoffMul_le φ m.1 m.2
  have hlim : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := D)).div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hε)] with R hR hRε
  have h : schwartzSeminormFamily ℂ ℝ ℂ m (cutoffMul R φ - φ) =
      SchwartzMap.seminorm ℂ m.1 m.2 (φ - cutoffMul R φ) := by
    rw [← neg_sub, map_neg_eq_map]
    rfl
  rw [h]
  exact lt_of_le_of_lt (hD R hR) hRε

/-- A tempered distribution vanishing on the compactly supported Schwartz functions supported
away from `0` vanishes on all Schwartz functions supported away from `0`. -/
theorem apply_eq_zero_of_forall_hasCompactSupport (u : TemperedDistribution ℝ ℂ)
    (hu : ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ → (0 : ℝ) ∉ tsupport φ → u φ = 0)
    (φ : SchwartzMap ℝ ℂ) (hφ : (0 : ℝ) ∉ tsupport φ) : u φ = 0 := by
  have h1 : Tendsto (fun R : ℝ => u (cutoffMul R φ)) atTop (𝓝 (u φ)) :=
    (u.continuous.tendsto φ).comp (tendsto_cutoffMul_atTop φ)
  have h2 : ∀ᶠ R : ℝ in atTop, u (cutoffMul R φ) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hu _ (hasCompactSupport_cutoffMul hR φ)
      fun h => hφ (tsupport_cutoffMul_subset_tsupport hR φ h)
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun R h => h.symm))

/-! ### The structure theorem -/

/-- The linear map `φ ↦ (φ^{(k)}(0))_{k ≤ N}`. -/
def derivsAtZero (N : ℕ) : SchwartzMap ℝ ℂ →ₗ[ℂ] (Fin (N + 1) → ℂ) :=
  LinearMap.pi fun k : Fin (N + 1) =>
    (TemperedDistribution.delta (0 : ℝ)).toLinearMap ∘ₗ
      ((SchwartzMap.derivCLM ℂ ℂ) ^ (k : ℕ)).toLinearMap

/-- Iterating the Schwartz derivative computes the iterated derivative. -/
theorem coe_pow_derivCLM (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    ⇑(((SchwartzMap.derivCLM ℂ ℂ) ^ n) φ) = iteratedDeriv n φ := by
  induction n generalizing φ with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [pow_succ']
    funext x
    change SchwartzMap.derivCLM ℂ ℂ (((SchwartzMap.derivCLM ℂ ℂ) ^ n) φ) x =
      iteratedDeriv (n + 1) φ x
    rw [SchwartzMap.derivCLM_apply, ih, iteratedDeriv_succ]

theorem derivsAtZero_apply (N : ℕ) (φ : SchwartzMap ℝ ℂ) (k : Fin (N + 1)) :
    derivsAtZero N φ k = iteratedDeriv k φ 0 := by
  change TemperedDistribution.delta (0 : ℝ) (((SchwartzMap.derivCLM ℂ ℂ) ^ (k : ℕ)) φ) = _
  rw [TemperedDistribution.delta_apply, coe_pow_derivCLM]

/-- **A tempered distribution supported at the origin is a combination of derivatives of the
Dirac mass**: if `u ∈ 𝓢'(ℝ, ℂ)` vanishes on every Schwartz function supported away from `0`,
then `u φ = ∑_{k ≤ N} c_k φ^{(k)}(0)` for some `N` and coefficients `c_k`. -/
theorem exists_sum_iteratedDeriv_zero_of_forall_apply_eq_zero (u : TemperedDistribution ℝ ℂ)
    (hu : ∀ φ : SchwartzMap ℝ ℂ, (0 : ℝ) ∉ tsupport φ → u φ = 0) :
    ∃ (N : ℕ) (c : ℕ → ℂ), ∀ φ : SchwartzMap ℝ ℂ,
      u φ = ∑ k ∈ Finset.range (N + 1), c k * iteratedDeriv k φ 0 := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ)
    ((normSeminorm ℂ ℂ).comp u.toLinearMap) (by
      change Continuous fun φ : SchwartzMap ℝ ℂ => ‖u φ‖
      exact u.continuous.norm)
  set N := s.sup fun m : ℕ × ℕ => max m.1 m.2 with hN
  have hs : ∀ m ∈ s, m.1 ≤ N ∧ m.2 ≤ N := fun m hm =>
    ⟨(le_max_left _ _).trans (Finset.le_sup (f := fun m : ℕ × ℕ => max m.1 m.2) hm),
      (le_max_right _ _).trans (Finset.le_sup (f := fun m : ℕ × ℕ => max m.1 m.2) hm)⟩
  have hC' : ∀ φ, ‖u φ‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ := fun φ => by
    have h := Seminorm.le_def.mp hC φ
    rw [Seminorm.comp_apply, smul_apply, coe_normSeminorm, NNReal.smul_def, smul_eq_mul] at h
    exact h
  have hker : LinearMap.ker (derivsAtZero N) ≤ LinearMap.ker u.toLinearMap := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    refine apply_eq_zero_of_iteratedDeriv_zero u hu C.2 hC' hs φ fun k hk => ?_
    have := congrFun hφ ⟨k, by omega⟩
    rwa [derivsAtZero_apply, Pi.zero_apply] at this
  obtain ⟨c, hc⟩ := LinearMap.exists_comp_of_ker_le (derivsAtZero N) u.toLinearMap hker
  refine ⟨N, fun k => if h : k < N + 1 then
    c (fun j : Fin (N + 1) => if (⟨k, h⟩ : Fin (N + 1)) = j then 1 else 0) else 0, fun φ => ?_⟩
  have huφ : u φ = c (derivsAtZero N φ) := by
    have := congrArg (fun f : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ => f φ) hc
    exact this
  rw [huφ, LinearMap.pi_apply_eq_sum_univ c (derivsAtZero N φ)]
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => (if h : k < N + 1 then
    c (fun j : Fin (N + 1) => if (⟨k, h⟩ : Fin (N + 1)) = j then 1 else 0) else 0) *
      iteratedDeriv k φ 0) (N + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, derivsAtZero_apply, smul_eq_mul, mul_comm]

/-- The structure theorem, assuming only vanishing on compactly supported Schwartz functions
supported away from the origin. -/
theorem exists_sum_iteratedDeriv_zero_of_forall_hasCompactSupport (u : TemperedDistribution ℝ ℂ)
    (hu : ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ → (0 : ℝ) ∉ tsupport φ → u φ = 0) :
    ∃ (N : ℕ) (c : ℕ → ℂ), ∀ φ : SchwartzMap ℝ ℂ,
      u φ = ∑ k ∈ Finset.range (N + 1), c k * iteratedDeriv k φ 0 :=
  exists_sum_iteratedDeriv_zero_of_forall_apply_eq_zero u
    (apply_eq_zero_of_forall_hasCompactSupport u hu)

end TemperedDistribution
