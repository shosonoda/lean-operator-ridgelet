import OperatorRidgelet.Reconstruction.Representation
import OperatorRidgelet.Tempered.Polynomial
import OperatorRidgelet.ToMathlib.FourierCompactSupportDecay
import OperatorRidgelet.ToMathlib.InvOneAddSqLintegral

/-!
# Synthesis with a tempered activation

The material behind Theorem `thm:A`(iii): for a density `G` regular along rays and a band-pass
filter `ρ`, the ray function `ω ↦ ρ̂(ω) G(-ωa)` is smooth with compact support in the frequency
window `I`, so the explicit coefficient `γ_G(a, ·)` is a Schwartz function whose decay is
controlled, uniformly in the direction `a`, by the ray-derivative bound
`max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖` of Definition `def:ray-regular`.  Pairing `γ_G(a, ·)`
with a tempered activation that is a continuous function `b` of polynomial growth is therefore an
absolutely convergent integral on `ν ⊗ dc`, because the ray moments `M_m(G)` are finite; Fubini
then gives the absolute convergence of the inner and of the outer integral separately.

The identity itself is the one of Theorem `thm:A`(ii) with the concrete integral against `ρ`
replaced by the integral against `b`: after the translation `t = ⟪a,x⟫ + c` the direction
integral of `γ_G(a, t - ⟪a,x⟫)` separates by homogeneity into `(2π)⁻¹ g_G(x)` times the value at
`t` of the Fourier transform of the test filter `ω ↦ ρ̂(-ω)|ω|^{-α}`, and integrating against `b`
produces the pairing `C^{(α)}_{β,ρ}`.

Everything is proved for a density with values in a complex Banach space `Y` (the `Vec` objects
of `Reconstruction.Defs`), which is Theorem `thm:vector-valued`; the scalar statements of
`thm:A`(iii) are the case `Y = ℂ`, recorded at the end of the file.  The last section collects
the instances that Corollary `cor:relu-admissible`(viii) needs.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier

open scoped ENNReal RealInnerProductSpace

/-! ### The ray function `ω ↦ ρ̂(ω) G(-ωa)` -/

section RayFilter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The integrand `ω ↦ ρ̂(ω) G(-ωa)` of the explicit coefficient `γ_G(a, ·)`. -/
def rayFilterFun (ρ : SchwartzMap ℝ ℝ) (G : H → Y) (a : H) (ω : ℝ) : Y :=
  filterFourier ρ ω • G (-(ω • a))

/-- The explicit coefficient is `(2π)⁻¹` times the inverse Fourier integral of the ray
function. -/
theorem coefficientFormulaVec_eq (ρ : SchwartzMap ℝ ℝ) (G : H → Y) (a : H) (c : ℝ) :
    coefficientFormulaVec ρ G (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ ω : ℝ, Complex.exp ((ω * c : ℝ) * Complex.I) • rayFilterFun ρ G a ω := by
  unfold coefficientFormulaVec rayFilterFun
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show (filterFourier ρ ω * Complex.exp ((ω * c : ℝ) * Complex.I)) • G (-(ω • a)) =
    Complex.exp ((ω * c : ℝ) * Complex.I) • filterFourier ρ ω • G (-(ω • a))
  rw [smul_smul, mul_comm]

/-- The ray function is supported in the support of `ρ̂`. -/
theorem tsupport_rayFilterFun_subset (ρ : SchwartzMap ℝ ℝ) (G : H → Y) (a : H) :
    tsupport (rayFilterFun ρ G a) ⊆ tsupport (filterFourier ρ) := by
  refine closure_mono fun ω hω => ?_
  simp only [Function.mem_support, ne_eq] at hω ⊢
  intro h
  exact hω (by rw [rayFilterFun, h, zero_smul])

/-- The ray function of a band-pass filter has compact support. -/
theorem hasCompactSupport_rayFilterFun {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (G : H → Y)
    (a : H) : HasCompactSupport (rayFilterFun ρ G a) :=
  hρ.hasCompactSupport.of_isClosed_subset isClosed_closure (tsupport_rayFilterFun_subset ρ G a)

/-- Off the support of `ρ̂` every derivative of the ray function vanishes. -/
theorem iteratedDeriv_rayFilterFun_eq_zero (ρ : SchwartzMap ℝ ℝ) (G : H → Y) (a : H) (k : ℕ)
    {ω : ℝ} (hω : ω ∉ tsupport (filterFourier ρ)) :
    iteratedDeriv k (rayFilterFun ρ G a) ω = 0 := by
  have h : ω ∉ tsupport (rayFilterFun ρ G a) := fun h => hω (tsupport_rayFilterFun_subset ρ G a h)
  have h2 : iteratedFDeriv ℝ k (rayFilterFun ρ G a) ω = 0 := by
    by_contra hc
    exact h (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := rayFilterFun ρ G a) k hc)
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h2, norm_zero]

/-- The ray function is smooth: it is a product of smooth functions on a neighbourhood of the
window, and vanishes on the open complement of the support of `ρ̂`. -/
theorem contDiff_rayFilterFun {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (-(ω • a))) U) :
    ContDiff ℝ (⊤ : ℕ∞) (rayFilterFun ρ G a) := by
  rw [contDiff_iff_contDiffAt]
  intro ω
  by_cases hω : ω ∈ U
  · exact hρ.contDiff.contDiffAt.smul (hv.contDiffAt (hU.mem_nhds hω))
  · have hns : ω ∉ tsupport (filterFourier ρ) := fun h => hω (hIU (hI.tsupport_subset h))
    refine (contDiffAt_const (c := (0 : Y))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (filterFourier ρ)).isOpen_compl.mem_nhds hns] with y hy
    rw [rayFilterFun, image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- A single bound for all derivatives of `ρ̂` of order at most `m`. -/
theorem exists_bound_iteratedDeriv_filterFourier {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ m, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B := by
  classical
  have h : ∀ j : ℕ, ∃ C : ℝ, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ C := fun j =>
    (hρ.contDiff.continuous_iteratedDeriv j
      (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv hρ.hasCompactSupport j)
  choose C hC using h
  refine ⟨∑ j ∈ Finset.range (m + 1), |C j|, by positivity, fun j hj ω => ?_⟩
  refine (hC j ω).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

end RayFilter

/-! ### Decay of the explicit coefficient along a ray -/

section Decay

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Leibniz' rule on the window.**  The derivatives of the ray function on `I` are bounded by
the derivatives of `ρ̂` times the ray derivatives of `G`; the window being symmetric, the ray
derivatives at `-a` are those at `a` reflected. -/
theorem norm_iteratedDeriv_rayFilterFun_le {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (-(ω • a))) U) {m : ℕ} {B D : ℝ}
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
    hρ.contDiff.contDiffOn hv hU.uniqueDiffOn hωU (n := k) (by exact_mod_cast le_top)
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
theorem integral_norm_iteratedDeriv_rayFilterFun_le {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U)
    (hIU : I ⊆ U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (-(ω • a))) U) {m : ℕ} {B D : ℝ}
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
      exact norm_iteratedDeriv_rayFilterFun_le hρ hI hU hIU hv hBb hDb hk
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
theorem norm_coefficientFormulaVec_le_of_bounds {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y} {a : H} {U : Set ℝ} (hU : IsOpen U)
    (hIU : I ⊆ U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (-(ω • a))) U) {m : ℕ} {B D : ℝ}
    (hBb : ∀ j ≤ m, ∀ ω : ℝ, ‖iteratedDeriv j (filterFourier ρ) ω‖ ≤ B)
    (hDb : ∀ j ≤ m, ∀ ω ∈ I, ‖iteratedDeriv j (fun t : ℝ => G (t • a)) ω‖ ≤ D)
    {k : ℕ} (hk : k ≤ m) (c : ℝ) :
    |c| ^ k * ‖coefficientFormulaVec ρ G (a, c)‖ ≤
      (2 * Real.pi)⁻¹ * ((volume (tsupport (filterFourier ρ))).toReal * (2 ^ k * (B * D))) := by
  have hdecay := norm_integral_exp_mul_I_smul_le (contDiff_rayFilterFun hρ hI hU hIU hv)
    (hasCompactSupport_rayFilterFun hρ G a) k c
  have hint := integral_norm_iteratedDeriv_rayFilterFun_le hρ hI hU hIU hv hBb hDb hk
  rw [coefficientFormulaVec_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), ← mul_assoc,
    mul_comm (|c| ^ k) ((2 * Real.pi)⁻¹ : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdecay.trans hint) (by positivity)

/-- **Uniform decay of the explicit coefficient, uniformly in the density.**  There is a
constant, depending only on `ρ`, `I` and `N`, with
`(1 + |c|)^N ‖γ_G(a,c)‖ₑ ≤ K max_{k ≤ N} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖ₑ` for every direction `a`
and every density `G` that is smooth along rays near the window. -/
theorem exists_const_forall_enorm_coefficientFormulaVec_le {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) {I : Set ℝ} (hI : IsFrequencyWindow ρ I) (N : ℕ) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧ ∀ G : H → Y,
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U) →
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
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (-(ω • a))) U := by
    have hfun : (fun ω : ℝ => G (-(ω • a))) = fun ω : ℝ => G (ω • (-a)) := by
      funext ω
      rw [smul_neg]
    rw [hfun]
    exact hv0
  have h0 := norm_coefficientFormulaVec_le_of_bounds hρ hI hU hIU hv hBb hDb (Nat.zero_le N) c
  have hN := norm_coefficientFormulaVec_le_of_bounds hρ hI hU hIU hv hBb hDb (le_refl N) c
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

/-- **Uniform decay of the explicit coefficient.**  For a density that is smooth along rays near
the window there is a constant, depending only on `ρ` and `N`, with
`(1 + |c|)^N ‖γ_G(a,c)‖ₑ ≤ K max_{k ≤ N} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖ₑ` for every direction `a`. -/
theorem exists_const_enorm_coefficientFormulaVec_le {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) (G : H → Y)
    (hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U) (N : ℕ) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧ ∀ (a : H) (c : ℝ),
      ENNReal.ofReal ((1 + |c|) ^ N) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ ≤
        K * rayDerivBound I G N a := by
  obtain ⟨K, hK0, hKtop, hK⟩ :=
    exists_const_forall_enorm_coefficientFormulaVec_le (H := H) (Y := Y) hρ hI N
  exact ⟨K, hK0, hKtop, hK G hGs⟩

end Decay

/-! ### Absolute convergence of the tempered bias integral -/

section Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A function of polynomial growth is bounded by `C (1 + |t|)^n` with a natural exponent and a
nonnegative constant. -/
theorem HasPolynomialGrowth.exists_nat {b : ℝ → ℝ} (hb : HasPolynomialGrowth b) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ t : ℝ, |b t| ≤ C * (1 + |t|) ^ n := by
  obtain ⟨C, p, hC⟩ := hb
  refine ⟨max C 0, ⌈p⌉₊, le_max_right _ _, fun t => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
  have hx : (1 + |t|) ^ p ≤ (1 + |t|) ^ ((⌈p⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
  rw [Real.rpow_natCast] at hx
  refine (hC t).trans ?_
  calc C * (1 + |t|) ^ p ≤ max C 0 * (1 + |t|) ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * (1 + |t|) ^ (⌈p⌉₊ : ℕ) := mul_le_mul_of_nonneg_left hx (le_max_right _ _)

/-- `1 + |u + c| ≤ (1 + |u|)(1 + |c|)`. -/
theorem one_add_abs_add_le (u c : ℝ) : 1 + |u + c| ≤ (1 + |u|) * (1 + |c|) := by
  have h : |u + c| ≤ |u| + |c| := by
    simpa [Real.norm_eq_abs] using norm_add_le u c
  nlinarith [abs_nonneg u, abs_nonneg c]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The uniform bound behind the absolute convergence of Theorem `thm:A`(iii): the integrand of
the tempered bias integral is dominated, for *every* direction, by a product of a function of
the direction with finite ray moment and the integrable weight `(1 + c²)⁻¹`. -/
theorem exists_bound_enorm_smul_coefficientFormulaVec {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    {I : Set ℝ} (hI : IsFrequencyWindow ρ I) {G : H → Y}
    (hGs : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U)
    {b : ℝ → ℝ} (hbp : HasPolynomialGrowth b) (x : H) :
    ∃ (K : ℝ≥0∞) (n : ℕ), K < ⊤ ∧ ∀ (a : H) (c : ℝ),
      ‖(b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)‖ₑ ≤
        K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
          ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
  obtain ⟨C, n, hC0, hb⟩ := hbp.exists_nat
  obtain ⟨K₀, hK₀pos, hK₀top, hK₀⟩ :=
    exists_const_enorm_coefficientFormulaVec_le hρ hI G hGs (n + 2)
  refine ⟨K₀ * ENNReal.ofReal (C * (1 + ‖x‖) ^ n), n,
    ENNReal.mul_lt_top hK₀top ENNReal.ofReal_lt_top, fun a c => ?_⟩
  have hpos : (0 : ℝ) < 1 + |c| := by positivity
  have hbb : ‖((b (⟪a, x⟫ + c) : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n * (1 + |c|) ^ n) := by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (hb _).trans ?_
    have h1 : (1 + |⟪a, x⟫ + c|) ^ n ≤ ((1 + ‖x‖) * (1 + ‖a‖) * (1 + |c|)) ^ n := by
      refine pow_le_pow_left₀ (by positivity) ?_ n
      refine (one_add_abs_add_le _ c).trans ?_
      have h2 : |(⟪a, x⟫ : ℝ)| ≤ ‖a‖ * ‖x‖ := abs_real_inner_le_norm a x
      have h3 : (1 : ℝ) + |(⟪a, x⟫ : ℝ)| ≤ (1 + ‖x‖) * (1 + ‖a‖) := by
        nlinarith [norm_nonneg a, norm_nonneg x]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    calc C * (1 + |⟪a, x⟫ + c|) ^ n ≤ C * ((1 + ‖x‖) * (1 + ‖a‖) * (1 + |c|)) ^ n :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ = C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n * (1 + |c|) ^ n := by
          rw [mul_pow, mul_pow]
          ring
  have hsq : ((1 + |c|) ^ 2)⁻¹ ≤ (1 + c ^ 2)⁻¹ := by
    have h1 : (0 : ℝ) < 1 + c ^ 2 := by positivity
    have h2 : 1 + c ^ 2 ≤ (1 + |c|) ^ 2 := by nlinarith [abs_nonneg c, sq_abs c]
    exact inv_anti₀ h1 h2
  have hstep : ‖coefficientFormulaVec ρ G (a, c)‖ₑ * ENNReal.ofReal ((1 + |c|) ^ n) ≤
      K₀ * rayDerivBound I G (n + 2) a * ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
    have hmul := mul_le_mul' (hK₀ a c) (le_refl (ENNReal.ofReal (((1 + |c|) ^ 2)⁻¹)))
    have hleft : ENNReal.ofReal ((1 + |c|) ^ (n + 2)) * ‖coefficientFormulaVec ρ G (a, c)‖ₑ *
        ENNReal.ofReal (((1 + |c|) ^ 2)⁻¹) =
        ‖coefficientFormulaVec ρ G (a, c)‖ₑ * ENNReal.ofReal ((1 + |c|) ^ n) := by
      rw [mul_comm (ENNReal.ofReal ((1 + |c|) ^ (n + 2))), mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
    rw [hleft] at hmul
    exact hmul.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hsq))
  calc ‖(b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)‖ₑ
      = ‖((b (⟪a, x⟫ + c) : ℝ) : ℂ)‖ₑ * ‖coefficientFormulaVec ρ G (a, c)‖ₑ := by
        rw [enorm_smul]
    _ ≤ ENNReal.ofReal (C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n * (1 + |c|) ^ n) *
          ‖coefficientFormulaVec ρ G (a, c)‖ₑ := mul_le_mul' hbb le_rfl
    _ = ENNReal.ofReal (C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n) *
          (‖coefficientFormulaVec ρ G (a, c)‖ₑ * ENNReal.ofReal ((1 + |c|) ^ n)) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n)]
        ring
    _ ≤ ENNReal.ofReal (C * (1 + ‖x‖) ^ n * (1 + ‖a‖) ^ n) *
          (K₀ * rayDerivBound I G (n + 2) a * ENNReal.ofReal ((1 + c ^ 2)⁻¹)) :=
        mul_le_mul' le_rfl hstep
    _ = K₀ * ENNReal.ofReal (C * (1 + ‖x‖) ^ n) *
          (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
          ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C * (1 + ‖x‖) ^ n)]
        ring

/-- The measurable weight `(1 + c²)⁻¹` used as the integrable majorant in the bias. -/
theorem measurable_ofReal_inv_one_add_sq :
    Measurable fun c : ℝ => ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
  fun_prop

/-- **Theorem `thm:A`(iii), absolute convergence.**  For a density regular along rays the
integrand `γ_G(a,c) b(⟪a,x⟫+c)` is integrable on `ν ⊗ dc`. -/
theorem integrable_prod_smul_coefficientFormulaVec {ν : Measure H} [SFinite ν] {I : Set ℝ}
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I) {G : H → Y}
    (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    Integrable (fun p : H × ℝ =>
      (b (⟪p.1, x⟫ + p.2) : ℂ) • coefficientFormulaVec ρ G (p.1, p.2)) (ν.prod volume) := by
  obtain ⟨K, n, hKtop, hK⟩ :=
    exists_bound_enorm_smul_coefficientFormulaVec hρ hI hG.contDiffOn hbp x
  have hmeas : AEStronglyMeasurable (fun p : H × ℝ =>
      (b (⟪p.1, x⟫ + p.2) : ℂ) • coefficientFormulaVec ρ G (p.1, p.2)) (ν.prod volume) :=
    StronglyMeasurable.aestronglyMeasurable
      (((Complex.continuous_ofReal.comp (hbc.comp
        (by fun_prop : Continuous fun p : H × ℝ => (⟪p.1, x⟫ : ℝ) + p.2))).stronglyMeasurable).smul
        (stronglyMeasurable_coefficientFormulaVec ρ hG.stronglyMeasurable))
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm]
  have hCfin : (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) < ⊤ :=
    lintegral_ofReal_inv_one_add_sq_lt_top
  have hbound : ∀ a : H, (∫⁻ c : ℝ,
      ‖(b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)‖ₑ) ≤
        K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
          (ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) * rayDerivBound I G (n + 2) a) := by
    intro a
    have hmono : ENNReal.ofReal ((1 + ‖a‖) ^ n) ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) :=
      ENNReal.ofReal_le_ofReal
        (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg a)) (by omega))
    calc ∫⁻ c : ℝ, ‖(b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)‖ₑ
        ≤ ∫⁻ c : ℝ, K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
            ENNReal.ofReal ((1 + c ^ 2)⁻¹) := lintegral_mono (hK a)
      _ = K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
            ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹) :=
          lintegral_const_mul _ measurable_ofReal_inv_one_add_sq
      _ ≤ K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
            (ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) * rayDerivBound I G (n + 2) a) := by
          rw [show K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
              (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) =
              K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
                (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) from by ring]
          exact mul_le_mul' le_rfl (mul_le_mul' hmono le_rfl)
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_lt_top hKtop hCfin).ne]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hKtop hCfin) (hG.rayMoment_lt_top (n + 2))

/-- **Theorem `thm:A`(iii), first part.**  For a density regular along rays the bias integral
`∫ γ_G(a,c) b(⟪a,x⟫+c) dc` converges absolutely for `ν`-almost every direction. -/
theorem ae_integrable_smul_coefficientFormulaVec_activation {ν : Measure H} [SFinite ν]
    {I : Set ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I)
    {G : H → Y} (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    ∀ᵐ a ∂ν,
      Integrable fun c : ℝ => (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c) :=
  (integrable_prod_smul_coefficientFormulaVec hρ hI hG hbc hbp x).prod_right_ae

/-- **Theorem `thm:A`(iii), second part.**  The direction integral of the bias integral converges
absolutely: the ray moment `M_{n+2}(G)` dominates it. -/
theorem integrable_integral_smul_coefficientFormulaVec_activation {ν : Measure H} [SFinite ν]
    {I : Set ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I)
    {G : H → Y} (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    Integrable
      (fun a : H => ∫ c : ℝ, (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ν :=
  (integrable_prod_smul_coefficientFormulaVec hρ hI hG hbc hbp x).integral_prod_left

end Convergence

/-! ### The direction integral of the shifted coefficient -/

section Separation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

omit [MeasurableSpace H] [BorelSpace H] in
/-- For a band-pass filter the weighted integral `∫ ‖ρ̂(ω)‖ |ω|^{-α} dω` is finite: the
integrand is the modulus of the reflected test filter, a Schwartz function. -/
theorem IsBandPass.lintegral_enorm_filterFourier_mul_lt_top {α : ℝ} {ρ : SchwartzMap ℝ ℝ}
    (hρ : IsBandPass ρ) :
    (∫⁻ ω : ℝ, ‖filterFourier ρ ω‖ₑ * ENNReal.ofReal (|ω| ^ (-α))) < ⊤ := by
  have h := (reflectSchwartz (temperedTestFilter α ρ)).integrable
    (μ := (volume : Measure ℝ)) |>.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ω => ?_)) h
  rw [reflectSchwartz_apply, hρ.temperedTestFilter_apply, neg_neg, abs_neg, enorm_mul,
    ← ofReal_norm]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ω) _)]

omit [CompleteSpace Y] in
/-- The kernel `(a, ω) ↦ ρ̂(ω) e^{iωt} G(-ωa) e^{i⟪x,-ωa⟫}` is integrable on `ν ⊗ dω`. -/
theorem integrable_shift_kernel {ν : Measure H} [SFinite ν] {α : ℝ} (hν : IsHomogeneous α ν)
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {G : H → Y} (hGm : StronglyMeasurable G)
    (hG₁ : Integrable G ν) (x : H) (t : ℝ) :
    Integrable (fun p : H × ℝ =>
      (filterFourier ρ p.2 * Complex.exp ((p.2 * t : ℝ) * Complex.I)) •
        (Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I) • G (-(p.2 • p.1))))
      (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  have hK : StronglyMeasurable fun p : H × ℝ =>
      filterFourier ρ p.2 * Complex.exp ((p.2 * t : ℝ) * Complex.I) :=
    (((continuous_filterFourier ρ).comp continuous_snd).mul
      (by fun_prop : Continuous fun p : H × ℝ =>
        Complex.exp ((p.2 * t : ℝ) * Complex.I))).stronglyMeasurable
  have hF : StronglyMeasurable fun p : H × ℝ =>
      Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I) • G (-(p.2 • p.1)) :=
    (by fun_prop : Continuous fun p : H × ℝ =>
      Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I)).stronglyMeasurable.smul
      (hGm.comp_measurable hc.measurable)
  refine ⟨(hK.smul hF).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hnorm : ∀ p : H × ℝ,
      ‖(filterFourier ρ p.2 * Complex.exp ((p.2 * t : ℝ) * Complex.I)) •
        (Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I) • G (-(p.2 • p.1)))‖ₑ =
        ‖filterFourier ρ p.2‖ₑ * ‖G (-(p.2 • p.1))‖ₑ := by
    intro p
    rw [enorm_smul, enorm_smul, enorm_mul, Complex.enorm_exp_ofReal_mul_I,
      Complex.enorm_exp_ofReal_mul_I, mul_one, one_mul]
  simp_rw [hnorm]
  rw [hν.lintegral_prod_neg_smul (K := fun ω => ‖filterFourier ρ ω‖ₑ)
    (continuous_filterFourier ρ).measurable.enorm hGm.enorm]
  exact ENNReal.mul_lt_top hρ.lintegral_enorm_filterFourier_mul_lt_top
    (hasFiniteIntegral_iff_enorm.mp hG₁.hasFiniteIntegral)

/-- **Homogeneity separates the shifted coefficient.**  The direction integral of
`γ_G(a, t - ⟪a,x⟫)` is `(2π)⁻¹` times the Fourier integral of `ρ̂(·)|·|^{-α}` at `t` times the
target `g_G(x)`. -/
theorem integral_coefficientFormulaVec_shift {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {G : H → Y}
    (hGm : StronglyMeasurable G) (hG₁ : Integrable G ν) (x : H) (t : ℝ) :
    ∫ a : H, coefficientFormulaVec ρ G (a, t - ⟪a, x⟫) ∂ν =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ((∫ ω : ℝ, filterFourier ρ ω * ((|ω| ^ (-α) : ℝ) : ℂ) *
            Complex.exp ((ω * t : ℝ) * Complex.I)) • spectralTarget ν G x) := by
  have hint := integrable_shift_kernel hν hρ hGm hG₁ x t
  have hFmeas : StronglyMeasurable fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ :=
    (by fun_prop : Continuous fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).stronglyMeasurable.smul hGm
  have hpoint : ∀ a : H, coefficientFormulaVec ρ G (a, t - ⟪a, x⟫) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω : ℝ,
        (filterFourier ρ ω * Complex.exp ((ω * t : ℝ) * Complex.I)) •
          (Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) • G (-(ω • a))) := by
    intro a
    rw [coefficientFormulaVec]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hphase : Complex.exp ((ω * (t - ⟪a, x⟫) : ℝ) * Complex.I) =
        Complex.exp ((ω * t : ℝ) * Complex.I) *
          Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_neg_right, inner_smul_right, real_inner_comm]
      push_cast
      ring
    beta_reduce
    rw [hphase, ← mul_assoc, ← smul_smul]
  calc ∫ a : H, coefficientFormulaVec ρ G (a, t - ⟪a, x⟫) ∂ν
      = ∫ a : H, (((2 * Real.pi)⁻¹ : ℝ) • ∫ ω : ℝ,
          (filterFourier ρ ω * Complex.exp ((ω * t : ℝ) * Complex.I)) •
            (Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I) • G (-(ω • a)))) ∂ν :=
        integral_congr_ae (Eventually.of_forall hpoint)
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ p : H × ℝ,
          (filterFourier ρ p.2 * Complex.exp ((p.2 * t : ℝ) * Complex.I)) •
            (Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I) • G (-(p.2 • p.1)))
            ∂ν.prod volume := by
        rw [integral_smul, integral_prod _ hint]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ((∫ ω : ℝ, filterFourier ρ ω * Complex.exp ((ω * t : ℝ) * Complex.I) *
              ((|ω| ^ (-α) : ℝ) : ℂ)) •
            ∫ ξ : H, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ ∂ν) := by
        rw [hν.integral_prod_neg_smul_vec
          (K := fun ω => filterFourier ρ ω * Complex.exp ((ω * t : ℝ) * Complex.I))
          (F := fun ξ => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) hFmeas hint]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ((∫ ω : ℝ, filterFourier ρ ω * ((|ω| ^ (-α) : ℝ) : ℂ) *
              Complex.exp ((ω * t : ℝ) * Complex.I)) • spectralTarget ν G x) := by
        congr 2
        exact integral_congr_ae (Eventually.of_forall fun ω => by ring)

end Separation

/-! ### The tempered spectral synthesis identity -/

section Identity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- After the translation `t = ⟪a,x⟫ + c` the integrand of the tempered synthesis identity is
integrable on `ν ⊗ dt`, which is what Fubini needs. -/
theorem integrable_prod_smul_coefficientFormulaVec_shift {ν : Measure H} [SFinite ν] {I : Set ℝ}
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I) {G : H → Y}
    (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    Integrable (fun p : H × ℝ =>
      (b p.2 : ℂ) • coefficientFormulaVec ρ G (p.1, p.2 - ⟪p.1, x⟫)) (ν.prod volume) := by
  obtain ⟨K, n, hKtop, hK⟩ :=
    exists_bound_enorm_smul_coefficientFormulaVec hρ hI hG.contDiffOn hbp x
  have hshift : Measurable fun p : H × ℝ => (p.1, p.2 - ⟪p.1, x⟫) :=
    measurable_fst.prodMk (measurable_snd.sub (by fun_prop))
  have hmeas : AEStronglyMeasurable (fun p : H × ℝ =>
      (b p.2 : ℂ) • coefficientFormulaVec ρ G (p.1, p.2 - ⟪p.1, x⟫)) (ν.prod volume) :=
    StronglyMeasurable.aestronglyMeasurable
      (((Complex.continuous_ofReal.comp (hbc.comp continuous_snd)).stronglyMeasurable).smul
        ((stronglyMeasurable_coefficientFormulaVec ρ
          hG.stronglyMeasurable).comp_measurable hshift))
  have htrans : ∀ u : ℝ, (∫⁻ t : ℝ, ENNReal.ofReal ((1 + (t - u) ^ 2)⁻¹)) =
      ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by
    intro u
    have h : (∫⁻ a : ℝ, ENNReal.ofReal ((1 + a ^ 2)⁻¹)
          ∂(Measure.map (· + (-u)) (volume : Measure ℝ))) =
        ∫⁻ a : ℝ, ENNReal.ofReal ((1 + (a + -u) ^ 2)⁻¹) :=
      lintegral_map measurable_ofReal_inv_one_add_sq (measurable_id.add_const (-u))
    rw [map_add_right_eq_self] at h
    simp_rw [sub_eq_add_neg]
    exact h.symm
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm]
  have hCfin : (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) < ⊤ :=
    lintegral_ofReal_inv_one_add_sq_lt_top
  have hbound : ∀ a : H,
      (∫⁻ t : ℝ, ‖(b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫)‖ₑ) ≤
        K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
          (ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) * rayDerivBound I G (n + 2) a) := by
    intro a
    have hmono : ENNReal.ofReal ((1 + ‖a‖) ^ n) ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) :=
      ENNReal.ofReal_le_ofReal
        (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg a)) (by omega))
    have hpt : ∀ t : ℝ, ‖(b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫)‖ₑ ≤
        K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
          ENNReal.ofReal ((1 + (t - ⟪a, x⟫) ^ 2)⁻¹) := by
      intro t
      have h := hK a (t - ⟪a, x⟫)
      rwa [show (⟪a, x⟫ : ℝ) + (t - ⟪a, x⟫) = t from by ring] at h
    calc ∫⁻ t : ℝ, ‖(b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫)‖ₑ
        ≤ ∫⁻ t : ℝ, K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
            ENNReal.ofReal ((1 + (t - ⟪a, x⟫) ^ 2)⁻¹) := lintegral_mono hpt
      _ = K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
            ∫⁻ t : ℝ, ENNReal.ofReal ((1 + (t - ⟪a, x⟫) ^ 2)⁻¹) :=
          lintegral_const_mul _ (by fun_prop)
      _ = K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
            ∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹) := by rw [htrans]
      _ ≤ K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
            (ENNReal.ofReal ((1 + ‖a‖) ^ (n + 2 + 2)) * rayDerivBound I G (n + 2) a) := by
          rw [show K * (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) *
              (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) =
              K * (∫⁻ c : ℝ, ENNReal.ofReal ((1 + c ^ 2)⁻¹)) *
                (ENNReal.ofReal ((1 + ‖a‖) ^ n) * rayDerivBound I G (n + 2) a) from by ring]
          exact mul_le_mul' le_rfl (mul_le_mul' hmono le_rfl)
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_lt_top hKtop hCfin).ne]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hKtop hCfin) (hG.rayMoment_lt_top (n + 2))

/-- **Theorem `thm:A`(iii), the identity.**  For a density regular along rays and a tempered
activation acting by integration against `b`,
`∫ [∫ γ_G(a,c) b(⟪a,x⟫+c) dc] ν(da) = C^{(α)}_{β,ρ} g_G(x)`. -/
theorem integral_integral_smul_coefficientFormulaVec_activation {ν : Measure H} [SFinite ν]
    {α : ℝ} (hν : IsHomogeneous α ν) {I : Set ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (hI : IsFrequencyWindow ρ I) {G : H → Y} (hG : IsRegularAlongRays ν I G)
    {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ} (hβ : IsTemperedFunction β b) (x : H) :
    ∫ a, (∫ c : ℝ, (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
      temperedAdmissibilityConst α β ρ • spectralTarget ν G x := by
  obtain ⟨ω₀, hω₀⟩ := hI.nonempty hρ
  have hω₀' : ω₀ ≠ 0 := fun h => hI.zero_notMem (h ▸ hω₀)
  have hGm : StronglyMeasurable G := hG.stronglyMeasurable
  have hG₁ : Integrable G ν := hG.integrable hν hω₀ hω₀'
  have hprod := integrable_prod_smul_coefficientFormulaVec_shift hρ hI hG hβ.continuous
    hβ.polynomialGrowth x
  have hrefl : ∀ g : ℝ → ℂ, (∫ w : ℝ, g (-w)) = ∫ w : ℝ, g w := by
    intro g
    have h := Measure.integral_comp_mul_left g (-1)
    simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
    exact h
  have hPsi : ∀ t : ℝ, (∫ ω : ℝ, filterFourier ρ ω * ((|ω| ^ (-α) : ℝ) : ℂ) *
      Complex.exp ((ω * t : ℝ) * Complex.I)) =
      angularFourierSchwartz (temperedTestFilter α ρ) t := by
    intro t
    rw [angularFourierSchwartz_apply,
      ← hrefl fun w : ℝ => Complex.exp (-Complex.I * ((w : ℂ) * (t : ℂ))) *
        temperedTestFilter α ρ w]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [hρ.temperedTestFilter_apply, neg_neg, abs_neg,
      show Complex.exp (-Complex.I * (((-ω : ℝ) : ℂ) * (t : ℂ))) =
        Complex.exp ((ω * t : ℝ) * Complex.I) from by
          congr 1
          push_cast
          ring]
    ring
  have htrans : ∀ a : H,
      (∫ c : ℝ, (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) =
      ∫ t : ℝ, (b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫) := by
    intro a
    rw [← integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => (b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫)) ⟪a, x⟫]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [add_sub_cancel_left]
  have hinner : ∀ t : ℝ,
      (∫ a : H, (b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫) ∂ν) =
        ((b t : ℂ) * angularFourierSchwartz (temperedTestFilter α ρ) t) •
          (((2 * Real.pi)⁻¹ : ℝ) • spectralTarget ν G x) := by
    intro t
    rw [integral_smul, integral_coefficientFormulaVec_shift hν hρ hGm hG₁ x t, hPsi t,
      smul_comm ((2 * Real.pi)⁻¹ : ℝ), smul_smul]
  rw [integral_congr_ae (Eventually.of_forall htrans),
    integral_integral_swap (f := fun (a : H) (t : ℝ) =>
      (b t : ℂ) • coefficientFormulaVec ρ G (a, t - ⟪a, x⟫)) hprod,
    integral_congr_ae (Eventually.of_forall hinner), integral_smul_const, ← hβ.apply_eq,
    temperedAdmissibilityConst, angularFourierDistribution_apply, ← Complex.coe_smul,
    smul_smul, mul_comm]

end Identity

/-! ### The scalar statements -/

section Scalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- For a scalar density the `Y`-valued and the scalar explicit coefficients agree. -/
theorem coefficientFormulaVec_eq_coefficientFormula (ρ : SchwartzMap ℝ ℝ) (G : H → ℂ)
    (p : H × ℝ) : coefficientFormulaVec ρ G p = coefficientFormula ρ G p := by
  unfold coefficientFormulaVec coefficientFormula
  rw [Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show (filterFourier ρ ω * Complex.exp ((ω * p.2 : ℝ) * Complex.I)) • G (-(ω • p.1)) =
    filterFourier ρ ω * G (-(ω • p.1)) * Complex.exp ((ω * p.2 : ℝ) * Complex.I)
  rw [smul_eq_mul]
  ring

omit [MeasurableSpace H] [BorelSpace H] in
/-- The scalar integrand of the tempered bias integral, as a `Y`-valued one. -/
theorem coefficientFormula_mul_eq_smul (ρ : SchwartzMap ℝ ℝ) (G : H → ℂ) (b : ℝ → ℝ) (a : H)
    (u c : ℝ) : coefficientFormula ρ G (a, c) * (b (u + c) : ℂ) =
      (b (u + c) : ℂ) • coefficientFormulaVec ρ G (a, c) := by
  rw [coefficientFormulaVec_eq_coefficientFormula, smul_eq_mul, mul_comm]

/-- **Theorem `thm:A`(iii), first part.**  For a density regular along rays the bias integral
`∫ γ_G(a,c) b(⟪a,x⟫+c) dc` converges absolutely for `ν`-almost every direction. -/
theorem ae_integrable_coefficientFormula_mul_activation {ν : Measure H} [SFinite ν] {I : Set ℝ}
    {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I) {G : H → ℂ}
    (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    ∀ᵐ a ∂ν, Integrable fun c : ℝ => coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ) := by
  filter_upwards [ae_integrable_smul_coefficientFormulaVec_activation hρ hI hG hbc hbp x]
    with a ha
  exact ha.congr (Eventually.of_forall fun c =>
    (coefficientFormula_mul_eq_smul ρ G b a ⟪a, x⟫ c).symm)

/-- **Theorem `thm:A`(iii), second part.**  The direction integral of the bias integral converges
absolutely. -/
theorem integrable_integral_coefficientFormula_mul_activation {ν : Measure H} [SFinite ν]
    {I : Set ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) (hI : IsFrequencyWindow ρ I)
    {G : H → ℂ} (hG : IsRegularAlongRays ν I G) {b : ℝ → ℝ} (hbc : Continuous b)
    (hbp : HasPolynomialGrowth b) (x : H) :
    Integrable
      (fun a : H => ∫ c : ℝ, coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ)) ν := by
  have h := integrable_integral_smul_coefficientFormulaVec_activation hρ hI hG hbc hbp x
  refine h.congr (Eventually.of_forall fun a => ?_)
  exact integral_congr_ae (Eventually.of_forall fun c =>
    (coefficientFormula_mul_eq_smul ρ G b a ⟪a, x⟫ c).symm)

/-- **Theorem `thm:A`(iii), the identity.**  For a density regular along rays and a tempered
activation acting by integration against `b`,
`∫ [∫ γ_G(a,c) b(⟪a,x⟫+c) dc] ν(da) = C^{(α)}_{β,ρ} g_G(x)`. -/
theorem integral_integral_coefficientFormula_mul_activation {ν : Measure H} [SFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) {I : Set ℝ} {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ)
    (hI : IsFrequencyWindow ρ I) {G : H → ℂ} (hG : IsRegularAlongRays ν I G)
    {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ} (hβ : IsTemperedFunction β b) (x : H) :
    ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ)) ∂ν =
      temperedAdmissibilityConst α β ρ * spectralTarget ν G x := by
  have h := integral_integral_smul_coefficientFormulaVec_activation hν hρ hI hG hβ x
  rw [← smul_eq_mul, ← h]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact integral_congr_ae (Eventually.of_forall fun c =>
    coefficientFormula_mul_eq_smul ρ G b a ⟪a, x⟫ c)

end Scalar

/-! ### Scalar multiples of the filter and the ReLU activation -/

section Instances

/-- A frequency window for `ρ` is a frequency window for every scalar multiple of `ρ`: scaling
does not enlarge the support of `ρ̂`. -/
theorem IsFrequencyWindow.smul {ρ : SchwartzMap ℝ ℝ} {I : Set ℝ} (hI : IsFrequencyWindow ρ I)
    (c : ℝ) : IsFrequencyWindow (⇑(c • ρ)) I where
  isCompact := hI.isCompact
  zero_notMem := hI.zero_notMem
  neg_mem := hI.neg_mem
  tsupport_subset := by
    refine (closure_mono fun ω hω => ?_).trans hI.tsupport_subset
    simp only [Function.mem_support, ne_eq] at hω ⊢
    intro h
    exact hω (by rw [filterFourier_smul' c ρ ω, h, mul_zero])

/-- `ReLU` has polynomial growth: `|ReLU(t)| ≤ (1 + |t|)`. -/
theorem hasPolynomialGrowth_relu : HasPolynomialGrowth relu := by
  refine ⟨1, 1, fun t => ?_⟩
  rw [Real.rpow_one, one_mul, abs_of_nonneg (relu_nonneg t)]
  have := relu_le_norm t
  rw [Real.norm_eq_abs] at this
  linarith

/-- The vendored `reluDistribution` is the tempered activation given by the continuous function
`ReLU` of polynomial growth. -/
theorem isTemperedFunction_reluDistribution : IsTemperedFunction reluDistribution relu where
  continuous := lipschitzWith_relu.continuous
  polynomialGrowth := hasPolynomialGrowth_relu
  apply_eq φ := by
    rw [reluDistribution, reluTemperedDistribution_apply]
    exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)

end Instances

end OperatorRidgelet
