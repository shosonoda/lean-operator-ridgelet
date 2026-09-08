import OperatorRidgelet.ToMathlib.GaussianHilbert
import OperatorRidgelet.ToMathlib.TraceClassEigenbasis
import OperatorRidgelet.ToMathlib.PositiveOperator
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Small-ball estimates for quadratic forms of Gaussian series

For the Gaussian series `gaussianSeries b p` on a Hilbert space `H` and a positive, symmetric,
injective operator `Q`, the quadratic form `⟪Q a, a⟫` satisfies the small-ball estimate
`μ {a | ⟪Q a, a⟫ < ε} ≤ C ε^{k/2}` for every finite set `F` of `k` coordinates
(`gaussianSeries_inner_map_lt_le`).  Conditionally on the coordinates outside `F`, the sublevel
set `{z | ⟪Q (A z + w), A z + w⟫ < ε}` of the convex quadratic `z ↦ ⟪Q (A z + w), A z + w⟫` on
`ℝ^F` has diameter at most `4 √(ε/λ)` by the parallelogram identity, where `λ` is the smallest
value of `⟪Q (A z), A z⟫` on the unit sphere, and a box of side `4 √(ε/λ)` has Gaussian measure
at most `(4 √(ε/λ) / √(2π))^k` (`stdGaussianPi_inner_map_lt_le`).  Consequently the negative
moments `∫ ⟪Q a, a⟫^{-β} dμ`, `2β < k`, are finite (`lintegral_ofReal_rpow_neg_lt_top`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The parallelogram identity for the quadratic form of a symmetric operator. -/
theorem inner_map_add_inner_map {Q : H →L[ℝ] H} (hQ : (Q : H →ₗ[ℝ] H).IsSymmetric) (u v : H) :
    ⟪Q u, u⟫ + ⟪Q v, v⟫ =
      2 * ⟪Q ((1 / 2 : ℝ) • (u + v)), (1 / 2 : ℝ) • (u + v)⟫ +
        2 * ⟪Q ((1 / 2 : ℝ) • (u - v)), (1 / 2 : ℝ) • (u - v)⟫ := by
  have h := ContinuousLinearMap.inner_map_comm hQ u v
  simp only [map_smul, map_add, map_sub, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [h]
  ring

/-- A continuous, positive definite, `2`-homogeneous function on `ℝ^κ` is bounded below by a
positive multiple of `∑ z k ^ 2`. -/
theorem exists_pos_mul_sum_sq_le {κ : Type*} [Fintype κ] (g : (κ → ℝ) → ℝ) (hg : Continuous g)
    (hpos : ∀ z, z ≠ 0 → 0 < g z) (hhom : ∀ (c : ℝ) z, g (c • z) = c ^ 2 * g z) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z, lam * ∑ k, z k ^ 2 ≤ g z := by
  classical
  have hg0 : g 0 = 0 := by
    have := hhom 0 0
    simpa using this
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine ⟨1, one_pos, fun z => ?_⟩
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz, hg0]
  obtain ⟨k₀⟩ := hκ
  set Sph : Set (κ → ℝ) := {z | ∑ k, z k ^ 2 = 1} with hSph
  have hclosed : IsClosed Sph := isClosed_eq (by fun_prop) continuous_const
  have hbdd : Bornology.IsBounded Sph := by
    refine (Metric.isBounded_closedBall (x := (0 : κ → ℝ)) (r := 1)).subset fun z hz => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_one.mpr ?_
    calc z k ^ 2 ≤ ∑ j, z j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ k)
      _ = 1 := hz
  have hK : IsCompact Sph := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : Sph.Nonempty := by
    refine ⟨Pi.single k₀ 1, ?_⟩
    simp [hSph, Pi.single_apply]
  obtain ⟨z₁, hz₁, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  have hz₁0 : z₁ ≠ 0 := by
    intro h
    have : ∑ k, z₁ k ^ 2 = 1 := hz₁
    simp [h] at this
  refine ⟨g z₁, hpos z₁ hz₁0, fun z => ?_⟩
  by_cases hz : z = 0
  · simp [hz, hg0]
  have hn : 0 < ∑ k, z k ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hk) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ k))
  set n : ℝ := √(∑ k, z k ^ 2) with hn_def
  have hnpos : 0 < n := Real.sqrt_pos.mpr hn
  have hmem : n⁻¹ • z ∈ Sph := by
    show ∑ k, (n⁻¹ • z) k ^ 2 = 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [inv_pow, hn_def, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
  have h1 : g z = n ^ 2 * g (n⁻¹ • z) := by
    rw [hhom n⁻¹ z, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hnpos.ne', one_pow, one_mul]
  rw [h1, hn_def, Real.sq_sqrt hn.le, mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin hmem) hn.le

/-- The sublevel set of the convex quadratic `z ↦ ⟪Q (A z + w), A z + w⟫` on `ℝ^κ` lies in a box
of side `4 √(ε/λ)`, hence has Gaussian measure at most `(4 √(ε/λ) / √(2π))^{|κ|}`. -/
theorem stdGaussianPi_inner_map_lt_le {κ : Type*} [Fintype κ] {Q : H →L[ℝ] H}
    (hQ : (Q : H →ₗ[ℝ] H).IsSymmetric) (hQpos : ∀ x, 0 ≤ ⟪Q x, x⟫) (A : (κ → ℝ) →ₗ[ℝ] H)
    {lam : ℝ} (hlam : 0 < lam) (hA : ∀ z, lam * ∑ k, z k ^ 2 ≤ ⟪Q (A z), A z⟫) (w : H) {ε : ℝ}
    (hε : 0 < ε) :
    stdGaussianPi κ {z | ⟪Q (A z + w), A z + w⟫ < ε} ≤
      ENNReal.ofReal ((4 * √(ε / lam) / √(2 * Real.pi)) ^ Fintype.card κ) := by
  classical
  set S := {z : κ → ℝ | ⟪Q (A z + w), A z + w⟫ < ε} with hS
  rcases S.eq_empty_or_nonempty with hS0 | ⟨z₀, hz₀⟩
  · rw [hS0, measure_empty]
    exact zero_le
  set r : ℝ := 2 * √(ε / lam) with hr
  have hsub : S ⊆ Set.pi (Finset.univ : Finset κ) fun k => Set.Ioo (z₀ k - r) (z₀ k + r) := by
    intro z hz
    have hpar := inner_map_add_inner_map hQ (A z + w) (A z₀ + w)
    have h1 : (1 / 2 : ℝ) • (A z + w - (A z₀ + w)) = A ((1 / 2 : ℝ) • (z - z₀)) := by
      rw [map_smul, map_sub]
      congr 1
      abel
    have h2 : ⟪Q (A ((1 / 2 : ℝ) • (z - z₀))), A ((1 / 2 : ℝ) • (z - z₀))⟫ < ε := by
      rw [← h1]
      have := hQpos ((1 / 2 : ℝ) • (A z + w + (A z₀ + w)))
      have hz' : ⟪Q (A z + w), A z + w⟫ < ε := hz
      have hz₀' : ⟪Q (A z₀ + w), A z₀ + w⟫ < ε := hz₀
      linarith
    have h3 := hA ((1 / 2 : ℝ) • (z - z₀))
    have h4 : ∑ k, (z k - z₀ k) ^ 2 < 4 * (ε / lam) := by
      have : ∑ k, ((1 / 2 : ℝ) • (z - z₀)) k ^ 2 = 1 / 4 * ∑ k, (z k - z₀ k) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [this] at h3
      rw [← mul_div_assoc, lt_div_iff₀ hlam]
      linarith
    rw [Set.mem_pi]
    intro k _
    have h5 : (z k - z₀ k) ^ 2 < 4 * (ε / lam) :=
      lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (z j - z₀ j))
        (Finset.mem_univ k)) h4
    have h6 : |z k - z₀ k| < r := by
      rw [hr, ← Real.sqrt_sq_eq_abs]
      calc √((z k - z₀ k) ^ 2) < √(4 * (ε / lam)) := Real.sqrt_lt_sqrt (sq_nonneg _) h5
        _ = 2 * √(ε / lam) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    obtain ⟨h6a, h6b⟩ := abs_lt.mp h6
    exact ⟨by linarith, by linarith⟩
  refine (measure_mono hsub).trans ?_
  rw [stdGaussianPi_pi _ _ fun k _ => measurableSet_Ioo]
  calc ∏ k ∈ Finset.univ, gaussianReal 0 1 (Set.Ioo (z₀ k - r) (z₀ k + r))
      ≤ ∏ _k ∈ (Finset.univ : Finset κ),
          ENNReal.ofReal (4 * √(ε / lam) / √(2 * Real.pi)) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun k _ => ?_
        refine (gaussianReal_apply_le_volume 0 one_ne_zero _).trans ?_
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        simp only [NNReal.coe_one, mul_one]
        rw [hr]
        field_simp
        ring
    _ = ENNReal.ofReal ((4 * √(ε / lam) / √(2 * Real.pi)) ^ Fintype.card κ) := by
        rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]

section GaussianSeries

variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ H) (p : ι → ℝ)

/-- The finite section `z ↦ ∑_{k ∈ F} √(p k) z k • b k` of the Gaussian series as a linear map
on `ℝ^F`. -/
noncomputable def gaussianSeriesSection (F : Finset ι) : ({i // i ∈ F} → ℝ) →ₗ[ℝ] H :=
  ∑ k : {i // i ∈ F}, (LinearMap.proj k : ({i // i ∈ F} → ℝ) →ₗ[ℝ] ℝ).smulRight (√(p k) • b k)

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [Countable ι] in
theorem gaussianSeriesSection_apply (F : Finset ι) (z : {i // i ∈ F} → ℝ) :
    gaussianSeriesSection b p F z = ∑ k : {i // i ∈ F}, (√(p k) * z k) • b k := by
  simp only [gaussianSeriesSection, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [Countable ι] in
/-- The quadratic form `⟪Q (A z), A z⟫` of a finite section is bounded below by a positive
multiple of `∑ z k ^ 2`. -/
theorem exists_pos_mul_sum_sq_le_inner_map_section (hp : ∀ i, 0 < p i) {Q : H →L[ℝ] H}
    (hQ : (Q : H →ₗ[ℝ] H).IsSymmetric) (hQpos : ∀ x, 0 ≤ ⟪Q x, x⟫)
    (hQinj : Function.Injective Q) (F : Finset ι) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z : {i // i ∈ F} → ℝ, lam * ∑ k, z k ^ 2 ≤
      ⟪Q (gaussianSeriesSection b p F z), gaussianSeriesSection b p F z⟫ := by
  classical
  set A := gaussianSeriesSection b p F with hA
  refine exists_pos_mul_sum_sq_le (fun z => ⟪Q (A z), A z⟫)
    (by fun_prop) (fun z hz => ?_) (fun c z => ?_)
  · refine hQ.inner_map_self_pos_of_injective hQpos hQinj ?_
    intro hAz
    apply hz
    funext k
    have h := b.inner_eq_of_hasSum_smul (c := fun i => if h : i ∈ F then √(p i) * z ⟨i, h⟩ else 0)
      (y := A z) ?_ k
    · rw [hAz, inner_zero_right, dif_pos k.2] at h
      have hsq : 0 < √(p k) := Real.sqrt_pos.mpr (hp k)
      simpa [hsq.ne'] using h.symm
    · rw [hA, gaussianSeriesSection_apply]
      have hf : ∀ i ∉ F, (if h : i ∈ F then √(p i) * z ⟨i, h⟩ else 0) • b i = 0 := fun i hi => by
        rw [dif_neg hi, zero_smul]
      have h : HasSum (fun i => (if h : i ∈ F then √(p i) * z ⟨i, h⟩ else 0) • b i)
          (∑ i ∈ F, (if h : i ∈ F then √(p i) * z ⟨i, h⟩ else 0) • b i) :=
        hasSum_sum_of_ne_finset_zero hf
      convert h using 1
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dif_pos k.2]
  · simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring

open Classical in
/-- The small-ball estimate for the quadratic form of a positive injective operator under the
Gaussian series: `μ {a | ⟪Q a, a⟫ < ε} ≤ C ε^{k/2}` for a set `F` of `k` coordinates. -/
theorem gaussianSeries_inner_map_lt_le (hp : ∀ i, 0 < p i) (hs : Summable p) {Q : H →L[ℝ] H}
    (hQ : (Q : H →ₗ[ℝ] H).IsSymmetric) (hQpos : ∀ x, 0 ≤ ⟪Q x, x⟫)
    (hQinj : Function.Injective Q) (F : Finset ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      gaussianSeries b p {a | ⟪Q a, a⟫ < ε} ≤ ENNReal.ofReal (C * ε ^ ((F.card : ℝ) / 2)) := by
  obtain ⟨lam, hlam, hA⟩ := exists_pos_mul_sum_sq_le_inner_map_section b p hp hQ hQpos hQinj F
  set A := gaussianSeriesSection b p F with hA_def
  set Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun i => i ∈ F with hΦ
  set W : ({i // ¬ i ∈ F} → ℝ) → H := fun y => ∑' i : {i // ¬ i ∈ F}, (√(p i) * y i) • b i
    with hW
  have hsqrt2π : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtlam : (0 : ℝ) < √lam := Real.sqrt_pos.mpr hlam
  refine ⟨(4 / (√lam * √(2 * Real.pi))) ^ F.card, by positivity, fun ε hε => ?_⟩
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  set T := gaussianSeriesMap b p with hT
  have hmeas : MeasurableSet {a : H | ⟪Q a, a⟫ < ε} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [gaussianSeries, Measure.map_apply (measurable_gaussianSeriesMap b p) hmeas]
  -- the almost sure decomposition of the series into the coordinates in `F` and outside `F`
  have hdec : ∀ᵐ x ∂stdGaussianPi ι, T x = A (Φ x).1 + W (Φ x).2 := by
    filter_upwards [ae_hasSum_gaussianSeriesMap b p hp0 hs] with x hx
    have hc : HasSum (fun i : {i // i ∉ F} => (√(p i) * x i) • b i)
        (T x - ∑ i ∈ F, (√(p i) * x i) • b i) := by
      refine (Finset.hasSum_compl_iff (f := fun i => (√(p i) * x i) • b i) F).mpr ?_
      rw [sub_add_cancel]
      exact hx
    have h1 : W (Φ x).2 = T x - ∑ i ∈ F, (√(p i) * x i) • b i := hc.tsum_eq
    have h2 : A (Φ x).1 = ∑ i ∈ F, (√(p i) * x i) • b i := by
      rw [hA_def, gaussianSeriesSection_apply, ← Finset.sum_coe_sort F]
      rfl
    rw [h1, h2, add_sub_cancel]
  have hdec' : ∀ᵐ y ∂stdGaussianPi {i // ¬ i ∈ F}, ∀ᵐ z ∂stdGaussianPi {i // i ∈ F},
      T (Φ.symm (z, y)) = A z + W y := by
    have h := Φ.ae_map_of_ae (stdGaussianPi ι)
      (q := fun zy => T (Φ.symm zy) = A zy.1 + W zy.2)
      (by filter_upwards [hdec] with x hx; rwa [Φ.symm_apply_apply])
    rw [hΦ, stdGaussianPi_map_piEquivPiSubtypeProd] at h
    exact Measure.ae_ae_of_ae_prod' h
  refine stdGaussianPi_le_of_ae_fiber_le F (hmeas.preimage (measurable_gaussianSeriesMap b p)) ?_
  filter_upwards [hdec'] with y hy
  have hset : {z | Φ.symm (z, y) ∈ T ⁻¹' {a | ⟪Q a, a⟫ < ε}} =ᵐ[stdGaussianPi {i // i ∈ F}]
      {z | ⟪Q (A z + W y), A z + W y⟫ < ε} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hy] with z hz
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hz]
  rw [measure_congr hset]
  refine (stdGaussianPi_inner_map_lt_le hQ hQpos A hlam hA (W y) hε).trans (le_of_eq ?_)
  congr 1
  have hsq : (√ε) ^ F.card = ε ^ ((F.card : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    ring
  rw [Fintype.card_coe, ← hsq, ← mul_pow]
  congr 1
  rw [Real.sqrt_div' _ hlam.le]
  field_simp

end GaussianSeries

/-! ### Negative moments -/

/-- Finiteness of negative moments from a small-ball estimate: if `μ {q < ε} ≤ C ε^{k/2}` for
all `ε > 0`, then `∫ q^{-β} dμ < ∞` for `0 < 2β < k`. -/
theorem lintegral_ofReal_rpow_neg_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {q : α → ℝ} (hq : Measurable q) (hq0 : ∀ a, 0 ≤ q a) {C k : ℝ}
    (hC : 0 ≤ C) (hsb : ∀ ε : ℝ, 0 < ε → μ {a | q a < ε} ≤ ENNReal.ofReal (C * ε ^ (k / 2)))
    {β : ℝ} (hβ : 0 < β) (hk : 2 * β < k) :
    ∫⁻ a, ENNReal.ofReal (q a ^ (-β)) ∂μ < ∞ := by
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun a => Real.rpow_nonneg (hq0 a) _)
    (hq.pow_const _).aemeasurable]
  have hsplit : ∫⁻ t in Set.Ioi 0, μ {a | t < q a ^ (-β)} ≤
      (∫⁻ t in Set.Ioc 0 1, μ {a | t < q a ^ (-β)}) +
        ∫⁻ t in Set.Ioi 1, μ {a | t < q a ^ (-β)} := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact lintegral_union_le _ _ _
  refine lt_of_le_of_lt hsplit (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
  · calc ∫⁻ t in Set.Ioc 0 1, μ {a | t < q a ^ (-β)} ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1, 1 :=
          lintegral_mono fun t => prob_le_one
      _ < ∞ := by
          rw [setLIntegral_const, Real.volume_Ioc]
          simp
  · set γ : ℝ := -(k / (2 * β)) with hγ
    have hγlt : γ < -1 := by
      rw [hγ, neg_lt_neg_iff, lt_div_iff₀ (by positivity)]
      linarith
    have hbound : ∀ t ∈ Set.Ioi (1 : ℝ), μ {a | t < q a ^ (-β)} ≤ ENNReal.ofReal (C * t ^ γ) := by
      intro t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hε : 0 < t ^ (-(1 / β)) := Real.rpow_pos_of_pos ht0 _
      refine (measure_mono ?_).trans ((hsb _ hε).trans (le_of_eq ?_))
      · intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have hqa : 0 < q a := by
          rcases (hq0 a).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, Real.zero_rpow (neg_ne_zero.mpr hβ.ne')] at ha
            linarith
        rw [Real.rpow_neg hqa.le] at ha
        have h1 : q a ^ β < t⁻¹ := (lt_inv_comm₀ ht0 (Real.rpow_pos_of_pos hqa β)).mp ha
        have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg hqa.le β) h1 (by positivity : 0 < 1 / β)
        rwa [← Real.rpow_mul hqa.le, mul_one_div_cancel hβ.ne', Real.rpow_one,
          Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at h2
      · congr 1
        rw [← Real.rpow_mul ht0.le, hγ]
        congr 1
        field_simp
    calc ∫⁻ t in Set.Ioi 1, μ {a | t < q a ^ (-β)}
        ≤ ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (C * t ^ γ) :=
          setLIntegral_mono' measurableSet_Ioi hbound
      _ < ∞ := by
          have hint : IntegrableOn (fun t : ℝ => C * t ^ γ) (Set.Ioi 1) :=
            ((integrableOn_Ioi_rpow_iff one_pos).mpr hγlt).const_mul C
          have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun t : ℝ => C * t ^ γ :=
            ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
              mul_nonneg hC (Real.rpow_nonneg (lt_trans one_pos ht).le _)
          exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral

end ProbabilityTheory
