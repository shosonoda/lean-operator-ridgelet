import OperatorRidgelet.Reconstruction.Tempered
import OperatorRidgelet.Reconstruction.FiniteOrderDefs
import OperatorRidgelet.Sampling.Spectral

/-!
# Finite-order regularity and coefficient decay

The coefficient decay estimates use only as many ray derivatives as the requested decay order.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The ray function is smooth: it is a product of smooth functions on a neighbourhood of the
window, and vanishes on the open complement of the support of `ρ̂`. -/
theorem contDiff_rayFilterFun_of_contDiff {n : ℕ∞} {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hv : ContDiffOn ℝ n (fun ω : ℝ => G (-(ω • a))) U) :
    ContDiff ℝ n (rayFilterFun ρ G a) := by
  rw [contDiff_iff_contDiffAt]
  intro ω
  by_cases hω : ω ∈ U
  · exact (hρ.contDiff.of_le (by exact_mod_cast (le_top : n ≤ ⊤))).contDiffAt.smul
      (hv.contDiffAt (hU.mem_nhds hω))
  · have hns : ω ∉ tsupport (filterFourier ρ) := fun h => hω (hIU (hI.tsupport_subset h))
    refine (contDiffAt_const (c := (0 : Y))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (filterFourier ρ)).isOpen_compl.mem_nhds hns] with y hy
    rw [rayFilterFun, image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- **Leibniz' rule on the window.**  The derivatives of the ray function on `I` are bounded by
the derivatives of `ρ̂` times the ray derivatives of `G`; the window being symmetric, the ray
derivatives at `-a` are those at `a` reflected. -/
theorem norm_iteratedDeriv_rayFilterFun_le_of_contDiff {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    {m : ℕ} (hv : ContDiffOn ℝ m (fun ω : ℝ => G (-(ω • a))) U) {B D : ℝ}
    (hBb : ∀ j ≤ m, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B)
    (hDb : ∀ j ≤ m, ∀ ω ∈ I, ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ ≤ D)
    {k : ℕ} (hk : k ≤ m) {ω : ℝ} (hω : ω ∈ I) :
    ‖iteratedDeriv k (rayFilterFun ρ G a) ω‖ ≤ 2 ^ k * (B * D) := by
  have hωU : ω ∈ U := hIU hω
  have hray : rayFilterFun ρ G a = fun y : ℝ => filterFourier ρ y • G (-(y • a)) := rfl
  rw [hray]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBb 0 (Nat.zero_le m) 0)
  have hrefl : ∀ i : ℕ, ‖iteratedDeriv i (fun t : ℝ => G (-(t • a))) ω‖ =
      ‖iteratedDeriv i (fun t : ℝ => G (t • a)) (-ω)‖ := by
    intro i
    have hcn := iteratedDeriv_comp_neg (𝕜 := ℝ) i (fun s : ℝ => G (s • a)) ω
    have hfun : (fun t : ℝ => G (-(t • a))) = fun t : ℝ => (fun s : ℝ => G (s • a)) (-t) := by
      funext t
      show G (-(t • a)) = G ((-t) • a)
      rw [neg_smul]
    rw [hfun, hcn, norm_smul]
    simp
  have hLeib := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ)
    (f := fun t : ℝ => filterFourier ρ t) (g := fun t : ℝ => G (-(t • a)))
    (hρ.contDiff.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).contDiffOn hv
    hU.uniqueDiffOn hωU (n := k) (by exact_mod_cast hk)
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) _ hU hωU,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hLeib
  refine hLeib.trans ?_
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * ‖iteratedDeriv j (filterFourier ρ) ω‖ *
        ‖iteratedDeriv (k - j) (fun t : ℝ => G (-(t • a))) ω‖ ≤ (k.choose j : ℝ) * (B * D) := by
    intro j hj
    have hjm : j ≤ m := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hk
    have hkjm : k - j ≤ m := le_trans (Nat.sub_le k j) hk
    have h1 := hBb j hjm ω
    have h2 : ‖iteratedDeriv (k - j) (fun t : ℝ => G (-(t • a))) ω‖ ≤ D := by
      rw [hrefl]
      exact hDb (k - j) hkjm (-ω) (hI.neg_mem ω hω)
    have hD0 : 0 ≤ D := le_trans (norm_nonneg _) h2
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hB0) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose k)

/-- The `L¹` norm of the `k`-th derivative of the ray function is bounded by the measure of the
support of `ρ̂` times the pointwise bound. -/
theorem integral_norm_iteratedDeriv_rayFilterFun_le_of_contDiff {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U)
    (hIU : I ⊆ U) {m : ℕ} (hv : ContDiffOn ℝ m (fun ω : ℝ => G (-(ω • a))) U) {B D : ℝ}
    (hBb : ∀ j ≤ m, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B)
    (hDb : ∀ j ≤ m, ∀ ω ∈ I, ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ ≤ D)
    {k : ℕ} (hk : k ≤ m) :
    ∫ ω : ℝ, ‖iteratedDeriv k (rayFilterFun ρ G a) ω‖ ≤
      (volume (tsupport (filterFourier ρ))).toReal * (2 ^ k * (B * D)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBb 0 (Nat.zero_le m) 0)
  have hmeas : MeasurableSet (tsupport (filterFourier ρ)) :=
    (isClosed_tsupport (filterFourier ρ)).measurableSet
  have hfin : volume (tsupport (filterFourier ρ)) < ⊤ := hρ.hasCompactSupport.measure_lt_top
  have hbdd : ∀ ω : ℝ, ‖iteratedDeriv k (rayFilterFun ρ G a) ω‖ ≤
      (tsupport (filterFourier ρ)).indicator (fun _ => 2 ^ k * (B * D)) ω := by
    intro ω
    by_cases hω : ω ∈ tsupport (filterFourier ρ)
    · rw [Set.indicator_of_mem hω]
      exact norm_iteratedDeriv_rayFilterFun_le_of_contDiff hρ hI hU hIU hv hBb hDb hk
        (hI.tsupport_subset hω)
    · rw [Set.indicator_of_notMem hω, iteratedDeriv_rayFilterFun_eq_zero ρ G a k hω, norm_zero]
  have hint : Integrable
      ((tsupport (filterFourier ρ)).indicator fun _ : ℝ => 2 ^ k * (B * D)) := by
    rw [integrable_indicator_iff hmeas]
    exact integrableOn_const hfin.ne
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
    (Eventually.of_forall hbdd)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ hmeas, smul_eq_mul, measureReal_def]

/-- The coefficient decay from the derivative bounds of the ray function. -/
theorem norm_coefficientFormulaVec_le_of_finite_bounds {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U)
    (hIU : I ⊆ U) {m : ℕ} (hv : ContDiffOn ℝ m (fun ω : ℝ => G (-(ω • a))) U) {B D : ℝ}
    (hBb : ∀ j ≤ m, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B)
    (hDb : ∀ j ≤ m, ∀ ω ∈ I, ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ ≤ D)
    {k : ℕ} (hk : k ≤ m) (c : ℝ) :
    |c| ^ k * ‖coefficientFormulaVec ρ G (a, c)‖ ≤
      (2 * Real.pi)⁻¹ * ((volume (tsupport (filterFourier ρ))).toReal * (2 ^ k * (B * D))) := by
  have hdecay := norm_integral_exp_mul_I_smul_le_of_contDiff k
    ((contDiff_rayFilterFun_of_contDiff hρ hI hU hIU hv).of_le (by exact_mod_cast hk))
    (hasCompactSupport_rayFilterFun hρ G a) c
  have hint := integral_norm_iteratedDeriv_rayFilterFun_le_of_contDiff hρ hI hU hIU hv hBb hDb hk
  rw [coefficientFormulaVec_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), ← mul_assoc,
    mul_comm (|c| ^ k) ((2 * Real.pi)⁻¹ : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdecay.trans hint) (by positivity)

/-- **Uniform decay of the explicit coefficient, uniformly in the density.**  There is a
constant, depending only on `ρ`, `I` and `N`, with
`(1 + |c|)^N ‖γ_G(a,c)‖ₑ ≤ K max_{k ≤ N} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖ₑ` for every direction `a`
and every density `G` that is smooth along rays near the window. -/
theorem exists_const_forall_enorm_coefficientFormulaVec_le_of_contDiff {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I) (N : ℕ) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧ ∀ G : H → Y,
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ N (fun ω : ℝ => G (ω • a)) U) →
      ∀ (a : H) (c : ℝ),
        ENNReal.ofReal ((1 + |c|) ^ N) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
          K * rayDerivBound I G N a := by
  obtain ⟨B, hB0, hBb⟩ := exists_bound_iteratedDeriv_filterFourier hρ N
  set V : ℝ := (volume (tsupport (filterFourier ρ))).toReal with hVdef
  have hV0 : (0 : ℝ) ≤ V := ENNReal.toReal_nonneg
  have hE0 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * (V * B) :=
    mul_nonneg (by positivity) (mul_nonneg hV0 hB0)
  set Kr : ℝ := 2 ^ N * (1 + 2 ^ N) * ((2 * Real.pi)⁻¹ * (V * B)) + 1 with hKrdef
  have hKr0 : (0 : ℝ) < Kr := by
    have : (0 : ℝ) ≤ 2 ^ N * (1 + 2 ^ N) * ((2 * Real.pi)⁻¹ * (V * B)) := by
      exact mul_nonneg (by positivity) hE0
    linarith
  refine ⟨ENNReal.ofReal Kr, ENNReal.ofReal_pos.mpr hKr0, ENNReal.ofReal_lt_top,
    fun G hGs a c => ?_⟩
  by_cases hRtop : rayDerivBound I G N a = ⊤
  · rw [hRtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hKr0).ne']
    exact le_top
  set D : ℝ := (rayDerivBound I G N a).toReal with hDdef
  have hD0 : (0 : ℝ) ≤ D := ENNReal.toReal_nonneg
  have hDb : ∀ j ≤ N, ∀ ω ∈ I, ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ ≤ D := by
    intro j hj ω hω
    have h1 : ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ₑ ≤ rayDerivBound I G N a := by
      rw [rayDerivBound]
      exact le_iSup_of_le (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (N + 1))
        (le_iSup₂_of_le ω hω le_rfl)
    calc ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖
        = (‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ₑ).toReal := by
          rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ D := ENNReal.toReal_mono hRtop h1
  obtain ⟨U, hU, hIU, hv0⟩ := hGs (-a)
  have hv : ContDiffOn ℝ N (fun ω : ℝ => G (-(ω • a))) U := by
    have hfun : (fun ω : ℝ => G (-(ω • a))) = fun ω : ℝ => G (ω • (-a)) := by
      funext ω
      rw [smul_neg]
    rw [hfun]
    exact hv0
  have h0 := norm_coefficientFormulaVec_le_of_finite_bounds hρ hI hU hIU hv hBb hDb
    (Nat.zero_le N) c
  have hN := norm_coefficientFormulaVec_le_of_finite_bounds hρ hI hU hIU hv hBb hDb (le_refl N) c
  simp only [pow_zero, one_mul] at h0
  have hg0 : (0 : ℝ) ≤ ‖coefficientFormulaVec ρ G (a, c)‖ := norm_nonneg _
  have hbin : (1 + |c|) ^ N ≤ 2 ^ (N - 1) * (1 + |c| ^ N) := by
    simpa using add_pow_le (zero_le_one (α := ℝ)) (abs_nonneg c) N
  have hpow : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ one_le_two (Nat.sub_le N 1)
  have key : (1 + |c|) ^ N * ‖coefficientFormulaVec ρ G (a, c)‖ ≤ Kr * D := by
    calc (1 + |c|) ^ N * ‖coefficientFormulaVec ρ G (a, c)‖
        ≤ 2 ^ (N - 1) * (1 + |c| ^ N) * ‖coefficientFormulaVec ρ G (a, c)‖ :=
          mul_le_mul_of_nonneg_right hbin hg0
      _ = 2 ^ (N - 1) * (‖coefficientFormulaVec ρ G (a, c)‖ +
            |c| ^ N * ‖coefficientFormulaVec ρ G (a, c)‖) := by ring
      _ ≤ 2 ^ (N - 1) * ((2 * Real.pi)⁻¹ * (V * (B * D)) +
            (2 * Real.pi)⁻¹ * (V * (2 ^ N * (B * D)))) :=
          mul_le_mul_of_nonneg_left (add_le_add h0 hN) (by positivity)
      _ = 2 ^ (N - 1) * ((1 + 2 ^ N) * ((2 * Real.pi)⁻¹ * (V * B)) * D) := by ring
      _ ≤ 2 ^ N * ((1 + 2 ^ N) * ((2 * Real.pi)⁻¹ * (V * B)) * D) :=
          mul_le_mul_of_nonneg_right hpow
            (mul_nonneg (mul_nonneg (by positivity) hE0) hD0)
      _ ≤ Kr * D := by
          rw [hKrdef]
          nlinarith [hD0]
  have hR : rayDerivBound I G N a = ENNReal.ofReal D := by
    rw [hDdef, ENNReal.ofReal_toReal hRtop]
  rw [hR, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hKr0.le]
  exact ENNReal.ofReal_le_ofReal key


variable [MeasurableSpace H] [BorelSpace H]

/-- **The moment bound of Theorem `thm:E`.**  There is a constant, depending only on `ρ`, `I`
and `m`, with `∫ (1 + ‖a‖ + |c|)^m ‖γ_G‖ dλ_α ≤ c M_{m+2}(G)` for every density `G` regular
along rays. -/
theorem exists_const_lintegral_moment_enorm_coefficientFormulaVec_le_of_contDiff
    {ν : Measure H} [SFinite ν]
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I) (m : ℕ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ G : H → Y, StronglyMeasurable G →
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (m + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U) →
      ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) *
          ‖coefficientFormulaVec ρ G θ‖ₑ ∂parameterMeasure ν ≤
        c * finiteRayMoment ν I G (m + 2) m := by
  obtain ⟨K, _, hKtop, hK⟩ :=
    exists_const_forall_enorm_coefficientFormulaVec_le_of_contDiff (H := H) (Y := Y) hρ hI (m + 2)
  set Cw : ℝ≥0∞ := ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹) with hCwdef
  have hCwtop : Cw < ⊤ := lintegral_ofReal_inv_one_add_sq_lt_top
  have hne : K * Cw ≠ ⊤ := (ENNReal.mul_lt_top hKtop hCwtop).ne
  refine ⟨K * Cw, hne, fun G hG hGs => ?_⟩
  have hKG := hK G hGs
  have hmeas : Measurable fun θ : H × ℝ => ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) *
      ‖coefficientFormulaVec ρ G θ‖ₑ := by
    refine Measurable.mul ?_
      (stronglyMeasurable_coefficientFormulaVec ρ hG).enorm
    exact (ENNReal.continuous_ofReal.comp (by fun_prop :
      Continuous fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m)).measurable
  have hpt : ∀ (a : H) (c : ℝ),
      ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
        ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) *
          ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
    intro a c
    have hsplit : ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) ≤
        ENNReal.ofReal ((1 + ‖a‖) ^ m) * ENNReal.ofReal ((1 + |c|) ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ m)
      nlinarith [norm_nonneg a, abs_nonneg c]
    calc ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ
        ≤ ENNReal.ofReal ((1 + ‖a‖) ^ m) *
            (ENNReal.ofReal ((1 + |c|) ^ m) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ) := by
          rw [← mul_assoc]
          exact mul_le_mul' hsplit le_rfl
      _ ≤ ENNReal.ofReal ((1 + ‖a‖) ^ m) *
            (K * rayDerivBound I G (m + 2) a * ENNReal.ofReal ((1 + c ^ 2)⁻¹)) :=
          mul_le_mul' le_rfl (enorm_coefficientFormulaVec_mul_pow_le hKG a c)
      _ = _ := by ring
  have hinner : ∀ a : H, (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
      ‖coefficientFormulaVec ρ G (a, c)‖ₑ) ≤
      K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ m) * rayDerivBound I G (m + 2) a) := by
    intro a
    calc (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
            ‖coefficientFormulaVec ρ G (a, c)‖ₑ)
        ≤ ∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) *
            ENNReal.ofReal ((1 + c ^ 2)⁻¹) := lintegral_mono fun c => hpt a c
      _ = ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) * Cw :=
          lintegral_const_mul _ measurable_ofReal_inv_one_add_sq
      _ ≤ K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ m) * rayDerivBound I G (m + 2) a) := by
          rw [show ENNReal.ofReal ((1 + ‖a‖) ^ m) * (K * rayDerivBound I G (m + 2) a) * Cw =
              K * Cw * (ENNReal.ofReal ((1 + ‖a‖) ^ m) * rayDerivBound I G (m + 2) a) from by
                ring]
  rw [parameterMeasure, lintegral_prod _ hmeas.aemeasurable]
  calc (∫⁻ a : H, (∫⁻ c : ℝ, ENNReal.ofReal ((1 + ‖a‖ + |c|) ^ m) *
        ‖coefficientFormulaVec ρ G (a, c)‖ₑ) ∂ν)
      ≤ ∫⁻ a : H, K * Cw *
          (ENNReal.ofReal ((1 + ‖a‖) ^ m) * rayDerivBound I G (m + 2) a) ∂ν :=
        lintegral_mono hinner
    _ = K * Cw * finiteRayMoment ν I G (m + 2) m := lintegral_const_mul' _ _ hne

/-- **Finite moments of all orders.**  For a density regular along rays, the coefficient measure
`γ_G λ_α` has a finite moment of every order. -/
theorem integrable_moment_norm_coefficientFormulaVec_of_contDiff {ν : Measure H} [SFinite ν]
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I)
    {G : H → Y} (hG : StronglyMeasurable G) (m : ℕ)
    (hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (m + 2 : ℕ) (fun ω : ℝ => G (ω • a)) U)
    (hM : finiteRayMoment ν I G (m + 2) m < ⊤) :
    Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖)
      (parameterMeasure ν) := by
  obtain ⟨c, hctop, hc⟩ :=
    exists_const_lintegral_moment_enorm_coefficientFormulaVec_le_of_contDiff
      (ν := ν) (Y := Y) hρ hI m
  have hsm : StronglyMeasurable
      (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖) :=
    (Continuous.stronglyMeasurable (by fun_prop)).mul
      (stronglyMeasurable_coefficientFormulaVec ρ hG).norm
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcongr : ∀ θ : H × ℝ,
      ‖(1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖‖ₑ =
        ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ m) * ‖coefficientFormulaVec ρ G θ‖ₑ := by
    intro θ
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (by positivity), ofReal_norm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr hcongr)) ?_
  exact lt_of_le_of_lt (hc G hG hGs) (ENNReal.mul_lt_top hctop.lt_top hM)

/-- A finite ray moment implies integrability of the spectral density by homogeneity. -/
theorem integrable_of_finiteRayMoment {ν : Measure H} {α : ℝ}
    (hν : IsHomogeneous α ν) {I : Set ℝ} {ω₀ : ℝ} (hω₀ : ω₀ ∈ I) (hω₀' : ω₀ ≠ 0)
    {G : H → Y} (hG : StronglyMeasurable G) {m r : ℕ}
    (hM : finiteRayMoment ν I G m r < ⊤) : Integrable G ν := by
  have hle : ∫⁻ a, ‖G (ω₀ • a)‖ₑ ∂ν ≤ finiteRayMoment ν I G m r := by
    unfold finiteRayMoment
    refine lintegral_mono fun a => ?_
    calc ‖G (ω₀ • a)‖ₑ = 1 * ‖G (ω₀ • a)‖ₑ := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((1 + ‖a‖) ^ r) * rayDerivBound I G m a := by
          gcongr
          · rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg a]))
          · exact enorm_le_rayDerivBound I G m a hω₀
  rw [hν.lintegral_smul hω₀' hG.enorm] at hle
  have hc : ENNReal.ofReal (|ω₀| ^ (-α)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hω₀') _)).ne'
  refine ⟨hG.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.mul_top hc] at hle
  exact (lt_irrefl _ (lt_of_le_of_lt hle hM)).elim

/-- A bounded density with a finite ray moment is square integrable. -/
theorem memLp_two_of_finiteRayMoment {ν : Measure H} {α : ℝ}
    (hν : IsHomogeneous α ν) {I : Set ℝ} {ω₀ : ℝ} (hω₀ : ω₀ ∈ I) (hω₀' : ω₀ ≠ 0)
    {G : H → Y} (hG : StronglyMeasurable G) (hbound : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M)
    {m r : ℕ} (hM : finiteRayMoment ν I G m r < ⊤) : MemLp G 2 ν := by
  obtain ⟨M, hMb⟩ := hbound
  have hInt := integrable_of_finiteRayMoment hν hω₀ hω₀' hG hM
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  refine (hInt.norm.const_mul M).mono' (hG.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (hMb ξ) (norm_nonneg (G ξ))

omit [BorelSpace H] in
/-- The finite-order moment with matching derivative order is bounded by the smooth ray moment. -/
theorem finiteRayMoment_le_rayMoment (ν : Measure H) (I : Set ℝ) (G : H → Y) (m r : ℕ)
    (hr : r ≤ m + 2) : finiteRayMoment ν I G m r ≤ rayMoment ν I G m := by
  apply lintegral_mono
  intro a
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg a)) hr

end OperatorRidgelet
