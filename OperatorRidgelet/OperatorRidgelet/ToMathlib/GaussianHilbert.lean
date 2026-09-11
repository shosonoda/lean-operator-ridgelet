import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Centred Gaussian measures on a separable Hilbert space with a diagonal covariance

Let `b : HilbertBasis ι ℝ H` be a Hilbert basis of a real Hilbert space `H` indexed by a countable
type, and `p : ι → ℝ` a nonnegative summable family.  Under the product `stdGaussianPi ι` of
standard Gaussians on `ι → ℝ`, the Gaussian series `∑ √(p i) x i • b i` converges almost surely
(`ae_hasSum_gaussianSeriesMap`), because `∫ ∑ p i x i² = ∑ p i < ∞`.  Its law
`gaussianSeries b p` on `H` is the centred Gaussian measure with the covariance diagonal in `b`
with eigenvalues `p`:

* `charFun_gaussianSeries`: `charFun (gaussianSeries b p) ξ = exp (-∑ p i ⟪b i, ξ⟫² / 2)`,
  by dominated convergence from the finite-dimensional Gaussians;
* `gaussianSeries_setOf_inner_mem`: the coordinates `⟪b i, ·⟫` are independent Gaussians
  `𝓝(0, p i)`, in the form of the cylinder-set formula;
* `isGaussian_of_charFun_eq_exp`: a measure whose characteristic function is
  `exp (-⟪P t, t⟫ / 2)` for a positive self-adjoint `P` is Gaussian in the sense of Mathlib
  (`ProbabilityTheory.IsGaussian`), so Fernique's theorem applies to it.

The elementary bound `gaussianReal_apply_le_volume` (the Gaussian density is at most
`(2πv)^{-1/2}`) is used for small-ball estimates.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory

/-! ### The one-dimensional Gaussian -/

/-- The density of `gaussianReal μ v` is at most `(2πv)^{-1/2}`, so
`gaussianReal μ v s ≤ (2πv)^{-1/2} vol(s)`. -/
theorem gaussianReal_apply_le_volume (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s ≤ ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ * volume s := by
  rw [gaussianReal_apply μ hv]
  calc ∫⁻ x in s, gaussianPDF μ v x
      ≤ ∫⁻ _ in s, ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := by
        refine lintegral_mono fun x => ?_
        unfold gaussianPDF gaussianPDFReal
        refine ENNReal.ofReal_le_ofReal ?_
        refine mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_
        rw [Real.exp_le_one_iff]
        refine div_nonpos_iff.mpr (Or.inr ⟨neg_nonpos.mpr (sq_nonneg _), by positivity⟩)
    _ = ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ * volume s := setLIntegral_const _ _

/-- A nondegenerate one-dimensional Gaussian charges every nonempty open set. -/
theorem isOpenPosMeasure_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal μ v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' μ hv).isOpenPosMeasure

/-! ### Independent standard Gaussians -/

/-- The law of a family of independent standard Gaussians indexed by `ι`. -/
noncomputable def stdGaussianPi (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi fun _ : ι => gaussianReal 0 1

/-- The product of standard Gaussian laws is a probability measure. -/
instance instIsProbabilityMeasureStdGaussianPi (ι : Type*) :
    IsProbabilityMeasure (stdGaussianPi ι) := by
  unfold stdGaussianPi
  infer_instance

/-- The second moment of a standard Gaussian, as a Lebesgue integral: `∫ t² = 1`. -/
theorem lintegral_ofReal_sq_gaussianReal_zero_one :
    ∫⁻ t, ENNReal.ofReal (t ^ 2) ∂gaussianReal 0 1 = 1 := by
  have hmem : MemLp (fun t : ℝ => t) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hint : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hmem.1).mp hmem
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => sq_nonneg t)]
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub hmem, integral_id_gaussianReal] at hvar
  simp only [Pi.pow_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    NNReal.coe_one] at hvar
  rw [hvar, ENNReal.ofReal_one]

variable {ι : Type*} [Countable ι]

omit [Countable ι] in
/-- The `i`-th coordinate of `stdGaussianPi ι` is a standard Gaussian. -/
theorem stdGaussianPi_map_eval (i : ι) :
    (stdGaussianPi ι).map (fun x => x i) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ i

omit [Countable ι] in
/-- The cylinder-set formula for `stdGaussianPi`. -/
theorem stdGaussianPi_pi (F : Finset ι) (A : ι → Set ℝ) (hA : ∀ i ∈ F, MeasurableSet (A i)) :
    stdGaussianPi ι (Set.pi F A) = ∏ i ∈ F, gaussianReal 0 1 (A i) :=
  Measure.infinitePi_pi _ hA

/-! ### The Gaussian series -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (b : HilbertBasis ι ℝ H) (p : ι → ℝ)

/-- The partial sums `∑_{i ∈ F} √(p i) x i • b i` of the Gaussian series. -/
noncomputable def gaussianSeriesPartial (F : Finset ι) (x : ι → ℝ) : H :=
  ∑ i ∈ F, (√(p i) * x i) • b i

omit [Countable ι] in
/-- Measurability of `gaussianSeriesPartial`. -/
theorem measurable_gaussianSeriesPartial (F : Finset ι) :
    Measurable (gaussianSeriesPartial b p F) :=
  Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).const_mul _).smul_const _

omit [Countable ι] in
/-- `∫ ∑ q k x (g k)² = ∑ q k` for a countable family of coordinates `g k`. -/
theorem lintegral_tsum_ofReal_mul_sq_comp {κ : Type*} [Countable κ] (g : κ → ι) (q : κ → ℝ)
    (hq : ∀ k, 0 ≤ q k) (hs : Summable q) :
    ∫⁻ x, ∑' k, ENNReal.ofReal (q k * x (g k) ^ 2) ∂stdGaussianPi ι =
      ENNReal.ofReal (∑' k, q k) := by
  have hmeas : ∀ k, Measurable fun x : ι → ℝ => ENNReal.ofReal (q k * x (g k) ^ 2) := fun k => by
    fun_prop
  rw [lintegral_tsum fun k => (hmeas k).aemeasurable, ENNReal.ofReal_tsum_of_nonneg hq hs]
  refine tsum_congr fun k => ?_
  have h1 : ∀ x : ι → ℝ, ENNReal.ofReal (q k * x (g k) ^ 2) =
      ENNReal.ofReal (q k) * ENNReal.ofReal ((x (g k)) ^ 2) := fun x => ENNReal.ofReal_mul (hq k)
  simp_rw [h1]
  rw [lintegral_const_mul _ (by fun_prop),
    ← lintegral_map (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ 2))
      (measurable_pi_apply (g k)),
    stdGaussianPi_map_eval, lintegral_ofReal_sq_gaussianReal_zero_one, mul_one]

/-- `∫ ∑ p i x i² = ∑ p i < ∞`. -/
theorem lintegral_tsum_ofReal_mul_sq (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∫⁻ x, ∑' i, ENNReal.ofReal (p i * x i ^ 2) ∂stdGaussianPi ι = ENNReal.ofReal (∑' i, p i) :=
  lintegral_tsum_ofReal_mul_sq_comp id p hp hs

/-- The coefficients `√(p i) x i` are almost surely square summable. -/
theorem ae_summable_mul_sq (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∀ᵐ x ∂stdGaussianPi ι, Summable fun i => p i * x i ^ 2 := by
  have hmeas : Measurable fun x : ι → ℝ => ∑' i, ENNReal.ofReal (p i * x i ^ 2) :=
    Measurable.tsum fun i => by fun_prop
  have hfin : ∫⁻ x, ∑' i, ENNReal.ofReal (p i * x i ^ 2) ∂stdGaussianPi ι ≠ ∞ := by
    rw [lintegral_tsum_ofReal_mul_sq p hp hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top hmeas hfin] with x hx
  have h := ENNReal.summable_toReal hx.ne
  refine h.congr fun i => ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (hp i) (sq_nonneg _))

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The Gaussian series converges almost surely. -/
theorem ae_exists_hasSum (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∀ᵐ x ∂stdGaussianPi ι, ∃ y : H, HasSum (fun i => (√(p i) * x i) • b i) y := by
  filter_upwards [ae_summable_mul_sq p hp hs] with x hx
  have hmem : Memℓp (fun i => √(p i) * x i) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine hx.congr fun i => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (hp i)]
  exact ⟨b.repr.symm ⟨_, hmem⟩, b.hasSum_repr_symm ⟨_, hmem⟩⟩

/-- There is a measurable map which is almost surely the sum of the Gaussian series. -/
theorem exists_measurable_ae_hasSum (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∃ T : (ι → ℝ) → H, Measurable T ∧
      ∀ᵐ x ∂stdGaussianPi ι, HasSum (fun i => (√(p i) * x i) • b i) (T x) := by
  classical
  let g : (ι → ℝ) → H := fun x =>
    if h : ∃ y : H, HasSum (fun i => (√(p i) * x i) • b i) y then h.choose else 0
  have hg : ∀ᵐ x ∂stdGaussianPi ι, HasSum (fun i => (√(p i) * x i) • b i) (g x) := by
    filter_upwards [ae_exists_hasSum b p hp hs] with x hx
    simp only [g, dif_pos hx]
    exact hx.choose_spec
  have hae : AEMeasurable g (stdGaussianPi ι) := by
    refine aemeasurable_of_tendsto_metrizable_ae (atTop : Filter (Finset ι))
      (fun F => (measurable_gaussianSeriesPartial b p F).aemeasurable) ?_
    filter_upwards [hg] with x hx
    exact hx
  refine ⟨hae.mk g, hae.measurable_mk, ?_⟩
  filter_upwards [hg, hae.ae_eq_mk] with x hx hx'
  rwa [← hx']

open Classical in
/-- The Gaussian series `∑ √(p i) x i • b i` as a measurable map on the product space (`0` if
`p` is not a nonnegative summable family); it is defined by choice and characterized almost
surely by `ae_hasSum_gaussianSeriesMap`. -/
noncomputable def gaussianSeriesMap : (ι → ℝ) → H :=
  if h : (∀ i, 0 ≤ p i) ∧ Summable p then (exists_measurable_ae_hasSum b p h.1 h.2).choose
  else 0

/-- Measurability of `gaussianSeriesMap`. -/
theorem measurable_gaussianSeriesMap : Measurable (gaussianSeriesMap b p) := by
  unfold gaussianSeriesMap
  split_ifs with h
  · exact (exists_measurable_ae_hasSum b p h.1 h.2).choose_spec.1
  · exact measurable_const

/-- The weighted Gaussian series converges almost surely to its measurable sum. -/
theorem ae_hasSum_gaussianSeriesMap (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∀ᵐ x ∂stdGaussianPi ι,
      HasSum (fun i => (√(p i) * x i) • b i) (gaussianSeriesMap b p x) := by
  unfold gaussianSeriesMap
  rw [dif_pos ⟨hp, hs⟩]
  exact (exists_measurable_ae_hasSum b p hp hs).choose_spec.2

/-- The centred Gaussian measure on `H` whose covariance is diagonal in the Hilbert basis `b`
with eigenvalues `p`: the law of the Gaussian series `∑ √(p i) Z_i b_i` with independent
standard Gaussians `Z_i`. -/
noncomputable def gaussianSeries : Measure H :=
  (stdGaussianPi ι).map (gaussianSeriesMap b p)

/-- The pushforward law of the Gaussian series is a probability measure. -/
instance instIsProbabilityMeasureGaussianSeries : IsProbabilityMeasure (gaussianSeries b p) :=
  Measure.isProbabilityMeasure_map (measurable_gaussianSeriesMap b p).aemeasurable

/-! ### The characteristic functional -/

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The characteristic functional of a finite section of the Gaussian series. -/
theorem integral_exp_inner_gaussianSeriesPartial (hp : ∀ i, 0 ≤ p i) (F : Finset ι) (ξ : H) :
    ∫ x, Complex.exp ((⟪gaussianSeriesPartial b p F x, ξ⟫ : ℝ) * Complex.I) ∂stdGaussianPi ι =
      Complex.exp (((-(∑ i ∈ F, p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ)) := by
  set β : ι → ℝ := fun i => √(p i) * ⟪b i, ξ⟫ with hβ
  -- the integrand is a product over the coordinates in `F`
  have h1 : ∀ x : ι → ℝ, Complex.exp ((⟪gaussianSeriesPartial b p F x, ξ⟫ : ℝ) * Complex.I) =
      ∏ i : F, Complex.exp ((β i : ℝ) * (F.restrict x i : ℝ) * Complex.I) := by
    intro x
    have : ⟪gaussianSeriesPartial b p F x, ξ⟫ = ∑ i ∈ F, β i * x i := by
      simp only [gaussianSeriesPartial, sum_inner, real_inner_smul_left, hβ]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum, ← Finset.prod_coe_sort]
    rfl
  simp_rw [h1]
  unfold stdGaussianPi
  rw [integral_restrict_infinitePi (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun y : F → ℝ => ∏ i : F, Complex.exp ((β i : ℝ) * (y i : ℝ) * Complex.I))
    (Continuous.aestronglyMeasurable (by fun_prop)),
    integral_fintype_prod_eq_prod
      (f := fun (i : F) (t : ℝ) => Complex.exp ((β i : ℝ) * (t : ℝ) * Complex.I))]
  have h2 : ∀ i : F, ∫ t : ℝ, Complex.exp ((β i : ℝ) * (t : ℝ) * Complex.I) ∂gaussianReal 0 1 =
      Complex.exp (((-(p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ)) := by
    intro i
    have hβsq : β i ^ 2 = p i * ⟪b i, ξ⟫ ^ 2 := by
      simp only [hβ, mul_pow, Real.sq_sqrt (hp i)]
    rw [← charFun_apply_real, charFun_gaussianReal, ← Complex.ofReal_pow, hβsq]
    congr 1
    push_cast
    ring
  simp_rw [h2]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_coe_sort F fun i => ((-(p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ)]
  push_cast
  simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

/-- The characteristic functional of the Gaussian series: `exp (-∑ p i ⟪b i, ξ⟫² / 2)`. -/
theorem charFun_gaussianSeries (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (ξ : H) :
    charFun (gaussianSeries b p) ξ =
      Complex.exp (((-(∑' i, p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ)) := by
  have hcont : Continuous fun y : H => Complex.exp ((⟪y, ξ⟫ : ℝ) * Complex.I) := by fun_prop
  rw [gaussianSeries, charFun_apply,
    integral_map (measurable_gaussianSeriesMap b p).aemeasurable hcont.aestronglyMeasurable]
  -- dominated convergence along the finite sections
  have hlim : Tendsto (fun F : Finset ι =>
      ∫ x, Complex.exp ((⟪gaussianSeriesPartial b p F x, ξ⟫ : ℝ) * Complex.I) ∂stdGaussianPi ι)
      atTop (𝓝 (∫ x, Complex.exp ((⟪gaussianSeriesMap b p x, ξ⟫ : ℝ) * Complex.I)
        ∂stdGaussianPi ι)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun F =>
        (hcont.measurable.comp (measurable_gaussianSeriesPartial b p F)).aestronglyMeasurable)
      (Eventually.of_forall fun F => Eventually.of_forall fun x => ?_) (integrable_const _) ?_
    · exact (Complex.norm_exp_ofReal_mul_I _).le
    · filter_upwards [ae_hasSum_gaussianSeriesMap b p hp hs] with x hx
      exact (hcont.tendsto _).comp hx
  -- the finite sections have the explicit characteristic functional
  have hsum : HasSum (fun i => p i * ⟪b i, ξ⟫ ^ 2) (∑' i, p i * ⟪b i, ξ⟫ ^ 2) := by
    refine (Summable.of_nonneg_of_le (fun i => mul_nonneg (hp i) (sq_nonneg _))
      (fun i => ?_) (hs.mul_right (‖ξ‖ ^ 2))).hasSum
    refine mul_le_mul_of_nonneg_left ?_ (hp i)
    have h1 : |⟪b i, ξ⟫| ≤ ‖ξ‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [b.orthonormal.1 i, one_mul]
    calc ⟪b i, ξ⟫ ^ 2 = |⟪b i, ξ⟫| ^ 2 := (sq_abs _).symm
      _ ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hlim' : Tendsto (fun F : Finset ι =>
      Complex.exp (((-(∑ i ∈ F, p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp (((-(∑' i, p i * ⟪b i, ξ⟫ ^ 2) / 2 : ℝ) : ℂ)))) := by
    have hc : Continuous fun t : ℝ => Complex.exp (((-t / 2 : ℝ) : ℂ)) := by fun_prop
    exact (hc.tendsto _).comp hsum
  simp_rw [integral_exp_inner_gaussianSeriesPartial b p hp] at hlim
  exact tendsto_nhds_unique hlim hlim'

/-! ### Coordinates of the Gaussian series -/

omit [Countable ι] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The coordinates of a convergent series `∑ c i • b i` in a Hilbert basis are its
coefficients. -/
theorem _root_.HilbertBasis.inner_eq_of_hasSum_smul {c : ι → ℝ} {y : H}
    (hy : HasSum (fun i => c i • b i) y) (i : ι) : ⟪b i, y⟫ = c i := by
  classical
  have h1 := hy.mapL (innerSL ℝ (b i))
  simp only [innerSL_apply_apply, real_inner_smul_right] at h1
  have h2 : HasSum (fun j => c j * ⟪b i, b j⟫) (c i) := by
    have hfun : (fun j => c j * ⟪b i, b j⟫) = fun j => if j = i then c i else 0 := by
      funext j
      rw [orthonormal_iff_ite.mp b.orthonormal i j]
      by_cases h : j = i
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [hfun]
    exact hasSum_ite_eq i _
  exact h1.unique h2

/-- The coordinates of the Gaussian series: `⟪b i, T x⟫ = √(p i) x i` almost surely. -/
theorem ae_inner_gaussianSeriesMap (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (i : ι) :
    ∀ᵐ x ∂stdGaussianPi ι, ⟪b i, gaussianSeriesMap b p x⟫ = √(p i) * x i := by
  filter_upwards [ae_hasSum_gaussianSeriesMap b p hp hs] with x hx
  exact b.inner_eq_of_hasSum_smul hx i

/-- The cylinder-set formula: under `gaussianSeries b p` the coordinates `⟪b i, ·⟫`, `i ∈ F`, are
independent centred Gaussians with variances `p i`. -/
theorem gaussianSeries_setOf_inner_mem (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (F : Finset ι)
    (A : ι → Set ℝ) (hA : ∀ i ∈ F, MeasurableSet (A i)) :
    gaussianSeries b p {y | ∀ i ∈ F, ⟪b i, y⟫ ∈ A i} =
      ∏ i ∈ F, gaussianReal 0 (p i).toNNReal (A i) := by
  have hmeas : MeasurableSet {y : H | ∀ i ∈ F, ⟪b i, y⟫ ∈ A i} := by
    have : {y : H | ∀ i ∈ F, ⟪b i, y⟫ ∈ A i} = ⋂ i ∈ F, (fun y => ⟪b i, y⟫) ⁻¹' A i := by
      ext y
      simp
    rw [this]
    exact MeasurableSet.biInter F.countable_toSet fun i hi => (hA i hi).preimage (by fun_prop)
  rw [gaussianSeries, Measure.map_apply (measurable_gaussianSeriesMap b p) hmeas]
  have hae : ∀ᵐ x ∂stdGaussianPi ι, ∀ i ∈ F,
      ⟪b i, gaussianSeriesMap b p x⟫ = √(p i) * x i := by
    have := (ae_ball_iff F.countable_toSet).mpr
      fun i (_ : i ∈ (F : Set ι)) => ae_inner_gaussianSeriesMap b p hp hs i
    simpa using this
  have hset : gaussianSeriesMap b p ⁻¹' {y | ∀ i ∈ F, ⟪b i, y⟫ ∈ A i} =ᵐ[stdGaussianPi ι]
      Set.pi (F : Set ι) fun i => (fun t => √(p i) * t) ⁻¹' A i := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
    exact forall₂_congr fun i hi => by rw [hx i hi]
  rw [measure_congr hset, stdGaussianPi_pi F _ fun i hi => (hA i hi).preimage (by fun_prop)]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Measure.map_apply (by fun_prop) (hA i hi), gaussianReal_map_const_mul, mul_zero]
  congr 2
  refine NNReal.eq ?_
  simp [Real.sq_sqrt (hp i), Real.coe_toNNReal _ (hp i)]

/-- Small-ball estimate through finitely many coordinates: the ball of radius `r` is contained in
the cylinder `{|⟪b i, y⟫| ≤ r, i ∈ F}`. -/
theorem gaussianSeries_closedBall_le (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (F : Finset ι)
    (r : ℝ) :
    gaussianSeries b p (Metric.closedBall 0 r) ≤
      ∏ i ∈ F, gaussianReal 0 (p i).toNNReal (Set.Icc (-r) r) := by
  rw [← gaussianSeries_setOf_inner_mem b p hp hs F _ fun i _ => measurableSet_Icc]
  refine measure_mono fun y hy i hi => ?_
  rw [mem_closedBall_zero_iff] at hy
  refine abs_le.mp ((abs_real_inner_le_norm _ _).trans ?_)
  rw [b.orthonormal.1 i, one_mul]
  exact hy

/-- `gaussianReal μ v [-r, r] ≤ 2r / √(2πv)`. -/
theorem gaussianReal_Icc_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (r : ℝ) :
    gaussianReal μ v (Set.Icc (-r) r) ≤ ENNReal.ofReal (2 * r / √(2 * Real.pi * v)) := by
  refine (gaussianReal_apply_le_volume μ hv _).trans ?_
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [sub_neg_eq_add]
  ring

/-! ### Full support -/

omit [Countable ι] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- Parseval's identity in the form `‖y‖² = ∑ ⟪b i, y⟫²`. -/
theorem _root_.HilbertBasis.hasSum_inner_sq (y : H) :
    HasSum (fun i => ⟪b i, y⟫ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  rw [real_inner_self_eq_norm_sq] at h
  refine h.congr_fun ?_
  intro i
  rw [sq, real_inner_comm]

/-- The σ-algebra on `ι → ℝ` generated by the coordinate `x ↦ x i`. -/
@[reducible] def coordinateSigma (ι : Type*) (i : ι) : MeasurableSpace (ι → ℝ) :=
  MeasurableSpace.comap (fun x => x i) inferInstance

omit [Countable ι] in
/-- The sigma-algebra of one coordinate is contained in the product sigma-algebra. -/
theorem coordinateSigma_le (i : ι) :
    coordinateSigma ι i ≤ (inferInstance : MeasurableSpace (ι → ℝ)) :=
  (measurable_pi_apply i).comap_le

omit [Countable ι] in
/-- The coordinates in `F` and those outside `F` generate independent σ-algebras under
`stdGaussianPi`. -/
theorem indep_coordinateSigma (F : Finset ι) :
    ProbabilityTheory.Indep (⨆ i ∈ (F : Set ι), coordinateSigma ι i)
      (⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i) (stdGaussianPi ι) := by
  have h := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ι => gaussianReal 0 1) (X := fun _ (t : ℝ) => t) fun _ => measurable_id
  rw [ProbabilityTheory.iIndepFun_iff_iIndep] at h
  exact ProbabilityTheory.indep_iSup_of_disjoint coordinateSigma_le h disjoint_compl_right

omit [Countable ι] in
/-- The restriction to the coordinates in `S` is measurable for the σ-algebra generated by
those coordinates. -/
theorem measurable_restrict_iSup_coordinateSigma (S : Set ι) :
    Measurable[⨆ i ∈ S, coordinateSigma ι i] (S.restrict : (ι → ℝ) → S → ℝ) := by
  letI : MeasurableSpace (ι → ℝ) := ⨆ i ∈ S, coordinateSigma ι i
  refine measurable_pi_iff.mpr fun k => ?_
  exact measurable_iff_comap_le.mpr
    (le_iSup₂ (f := fun i (_ : i ∈ S) => coordinateSigma ι i) (k : ι) k.2)

omit [Countable ι] in
/-- Transport of an almost sure statement through a measurable equivalence. -/
theorem _root_.MeasurableEquiv.ae_map_of_ae {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α) {q : β → Prop}
    (h : ∀ᵐ x ∂μ, q (e x)) : ∀ᵐ y ∂μ.map e, q y := by
  rw [ae_iff, MeasurableEquiv.map_apply]
  rw [ae_iff] at h
  exact h

omit [Countable ι] in
/-- Fubini for almost sure statements on a product, integrating first over the second factor. -/
theorem _root_.MeasureTheory.Measure.ae_ae_of_ae_prod' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {q : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, q z) : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, q (x, y) := by
  have h' : ∀ᵐ z ∂ν.prod μ, q z.swap := by
    rw [← Measure.prod_swap]
    exact (MeasurableEquiv.prodComm (α := α) (β := β)).ae_map_of_ae (μ.prod ν) h
  exact Measure.ae_ae_of_ae_prod h'

open Classical in
omit [Countable ι] in
/-- The product structure of `stdGaussianPi` along the coordinates in `F` and outside `F`. -/
theorem stdGaussianPi_map_piEquivPiSubtypeProd (F : Finset ι) :
    (stdGaussianPi ι).map (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun i => i ∈ F) =
      (stdGaussianPi {i // i ∈ F}).prod (stdGaussianPi {i // ¬ i ∈ F}) := by
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun i => i ∈ F) ⁻¹' (s ×ˢ t) =
      ((fun x : ι → ℝ => fun i : {i // i ∈ F} => x i) ⁻¹' s) ∩
        ((fun x : ι → ℝ => fun i : {i // ¬ i ∈ F} => x i) ⁻¹' t) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    rfl
  rw [hpre]
  have hX : Measurable[⨆ i ∈ (F : Set ι), coordinateSigma ι i]
      fun x : ι → ℝ => fun i : {i // i ∈ F} => x i :=
    measurable_restrict_iSup_coordinateSigma (F : Set ι)
  have hY : Measurable[⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i]
      fun x : ι → ℝ => fun i : {i // ¬ i ∈ F} => x i :=
    measurable_restrict_iSup_coordinateSigma ((F : Set ι)ᶜ)
  have hle₁ : (⨆ i ∈ (F : Set ι), coordinateSigma ι i) ≤ MeasurableSpace.pi :=
    iSup₂_le fun i _ => coordinateSigma_le i
  have hle₂ : (⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i) ≤ MeasurableSpace.pi :=
    iSup₂_le fun i _ => coordinateSigma_le i
  have h1 := (ProbabilityTheory.indep_iff_forall_indepSet _).mp (indep_coordinateSigma F) _ _
    (hX hs) (hY ht)
  rw [(ProbabilityTheory.indepSet_iff_measure_inter_eq_mul (hle₁ _ (hX hs)) (hle₂ _ (hY ht))
    (μ := stdGaussianPi ι)).mp h1]
  have hmX : Measurable fun x : ι → ℝ => fun i : {i // i ∈ F} => x i := by fun_prop
  have hmY : Measurable fun x : ι → ℝ => fun i : {i // ¬ i ∈ F} => x i := by fun_prop
  have hmapX : (stdGaussianPi ι).map (fun x : ι → ℝ => fun i : {i // i ∈ F} => x i) =
      stdGaussianPi {i // i ∈ F} :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ι => gaussianReal 0 1)
      (f := (Subtype.val : {i // i ∈ F} → ι)) Subtype.val_injective
  have hmapY : (stdGaussianPi ι).map (fun x : ι → ℝ => fun i : {i // ¬ i ∈ F} => x i) =
      stdGaussianPi {i // ¬ i ∈ F} :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ι => gaussianReal 0 1)
      (f := (Subtype.val : {i // ¬ i ∈ F} → ι)) Subtype.val_injective
  rw [← Measure.map_apply hmX hs, ← Measure.map_apply hmY ht, hmapX, hmapY]

open Classical in
omit [Countable ι] in
/-- Conditioning on the coordinates outside `F`: if for almost every configuration `y` of the
coordinates outside `F` the fibre `{z | (z, y) ∈ E}` has measure at most `C`, then
`stdGaussianPi ι E ≤ C`. -/
theorem stdGaussianPi_le_of_ae_fiber_le (F : Finset ι) {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    {C : ℝ≥0∞} (h : ∀ᵐ y ∂stdGaussianPi {i // ¬ i ∈ F}, stdGaussianPi {i // i ∈ F}
      {z | (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun i => i ∈ F).symm (z, y) ∈ E}
        ≤ C) :
    stdGaussianPi ι E ≤ C := by
  set Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun i => i ∈ F with hΦ
  have hE' : MeasurableSet (Φ '' E) := Φ.measurableSet_image.mpr hE
  calc stdGaussianPi ι E = ((stdGaussianPi ι).map Φ) (Φ '' E) := by
        rw [MeasurableEquiv.map_apply, Set.preimage_image_eq E Φ.injective]
    _ = ∫⁻ y, stdGaussianPi {i // i ∈ F} ((fun z => (z, y)) ⁻¹' (Φ '' E))
          ∂stdGaussianPi {i // ¬ i ∈ F} := by
        rw [hΦ, stdGaussianPi_map_piEquivPiSubtypeProd, Measure.prod_apply_symm hE']
    _ ≤ ∫⁻ _, C ∂stdGaussianPi {i // ¬ i ∈ F} := by
        refine lintegral_mono_ae ?_
        filter_upwards [h] with y hy
        convert hy using 2
        ext z
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, hx, hxz⟩
          rw [← hxz, Φ.symm_apply_apply]
          exact hx
        · intro hz
          exact ⟨Φ.symm (z, y), hz, Φ.apply_symm_apply _⟩
    _ = C := by rw [lintegral_const, measure_univ, mul_one]

/-- The Gaussian series with positive eigenvalues charges every nonempty open set: a ball
`B(y₀, ε)` contains the event that finitely many coordinates are close to those of `y₀` and the
remaining coordinates have small energy; the two events are independent and each has positive
probability (the second by Markov's inequality). -/
theorem isOpenPosMeasure_gaussianSeries (hp : ∀ i, 0 < p i) (hs : Summable p) :
    (gaussianSeries b p).IsOpenPosMeasure := by
  classical
  refine ⟨fun U hU ⟨y₀, hy₀⟩ => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hball))
  rw [gaussianSeries, Measure.map_apply (measurable_gaussianSeriesMap b p) measurableSet_ball]
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  set γ := stdGaussianPi ι with hγ
  set T := gaussianSeriesMap b p with hT
  set a : ι → ℝ := fun i => ⟪b i, y₀⟫ with ha_def
  have ha : Summable fun i => a i ^ 2 := (b.hasSum_inner_sq y₀).summable
  -- the tails of `a` and `p` are small outside a finite set `F`
  obtain ⟨F, hFa, hFp⟩ : ∃ F : Finset ι, ∑' i : {i // i ∉ F}, a i ^ 2 < ε ^ 2 / 8 ∧
      ∑' i : {i // i ∉ F}, p i < ε ^ 2 / 16 :=
    (((tendsto_tsum_compl_atTop_zero fun i => a i ^ 2).eventually
      (gt_mem_nhds (by positivity))).and
      ((tendsto_tsum_compl_atTop_zero p).eventually (gt_mem_nhds (by positivity)))).exists
  set n : ℝ := (F.card : ℝ) with hn
  set δ : ℝ := ε / (2 * (n + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set A : Set (ι → ℝ) := {x | ∀ i ∈ F, |√(p i) * x i - a i| < δ} with hA_def
  set S : (ι → ℝ) → ℝ≥0∞ := fun x => ∑' i : {i // i ∉ F}, ENNReal.ofReal (p i * x i ^ 2)
    with hS_def
  set B : Set (ι → ℝ) := {x | S x < ENNReal.ofReal (ε ^ 2 / 8)} with hB_def
  -- Step 1: `A ∩ B` is almost surely contained in the preimage of the ball
  have hsub : ∀ᵐ x ∂γ, x ∈ A ∩ B → x ∈ T ⁻¹' Metric.ball y₀ ε := by
    filter_upwards [ae_hasSum_gaussianSeriesMap b p hp0 hs, ae_summable_mul_sq p hp0 hs]
      with x hx hsum hxAB
    obtain ⟨hxA, hxB⟩ := hxAB
    set c : ι → ℝ := fun i => √(p i) * x i with hc_def
    have hc2 : ∀ i, c i ^ 2 = p i * x i ^ 2 := fun i => by
      rw [hc_def]
      simp only
      rw [mul_pow, Real.sq_sqrt (hp0 i)]
    have hcs : Summable fun i => c i ^ 2 := by
      simp_rw [hc2]
      exact hsum
    -- the coordinates of `T x - y₀`
    have hdiff : HasSum (fun i => (c i - a i) • b i) (T x - y₀) := by
      have h := hx.sub (b.hasSum_repr y₀)
      refine h.congr_fun fun i => ?_
      rw [b.repr_apply_apply, sub_smul]
    have hnorm : ‖T x - y₀‖ ^ 2 = ∑' i, (c i - a i) ^ 2 := by
      rw [← (b.hasSum_inner_sq (T x - y₀)).tsum_eq]
      exact tsum_congr fun i => by rw [b.inner_eq_of_hasSum_smul hdiff i]
    have hbound : ∀ i, (c i - a i) ^ 2 ≤ 2 * c i ^ 2 + 2 * a i ^ 2 := fun i => by
      nlinarith [sq_nonneg (c i + a i)]
    have hds : Summable fun i => (c i - a i) ^ 2 :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _) hbound ((hcs.mul_left 2).add (ha.mul_left 2))
    -- the finite part
    have hfin : ∑ i ∈ F, (c i - a i) ^ 2 ≤ ε ^ 2 / 4 := by
      have h1 : ∑ i ∈ F, (c i - a i) ^ 2 ≤ F.card • δ ^ 2 :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi => by
          have := hxA i hi
          rw [← sq_abs]
          exact (pow_le_pow_left₀ (abs_nonneg _) this.le 2)
      rw [nsmul_eq_mul, ← hn] at h1
      refine h1.trans ?_
      have hn0 : 0 ≤ n := Nat.cast_nonneg _
      have : n * δ ^ 2 = ε ^ 2 / 4 * (n / (n + 1) ^ 2) := by
        rw [hδ]
        field_simp
        ring
      rw [this]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one (by positivity)]
      nlinarith
    -- the tail
    have htail : ∑' i : {i // i ∉ F}, (c i - a i) ^ 2 < ε ^ 2 / 2 := by
      have hcB : ∑' i : {i // i ∉ F}, c i ^ 2 < ε ^ 2 / 8 := by
        have h := hxB
        simp only [hB_def, hS_def, Set.mem_setOf_eq] at h
        have hsub' : Summable fun i : {i // i ∉ F} => p i * x i ^ 2 := hsum.subtype _
        rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun i : {i // i ∉ F} => p i * x i ^ 2)
          (fun i => mul_nonneg (hp0 i) (sq_nonneg _)) hsub',
          ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h
        simpa only [hc2] using h
      calc ∑' i : {i // i ∉ F}, (c i - a i) ^ 2
          ≤ ∑' i : {i // i ∉ F}, (2 * c i ^ 2 + 2 * a i ^ 2) :=
            Summable.tsum_le_tsum (fun i => hbound i) (hds.subtype _)
              (((hcs.mul_left 2).add (ha.mul_left 2)).subtype _)
        _ = 2 * ∑' i : {i // i ∉ F}, c i ^ 2 + 2 * ∑' i : {i // i ∉ F}, a i ^ 2 := by
            have h1 : Summable fun i : {i // i ∉ F} => 2 * c i ^ 2 := (hcs.mul_left 2).subtype _
            have h2 : Summable fun i : {i // i ∉ F} => 2 * a i ^ 2 := (ha.mul_left 2).subtype _
            rw [Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left]
        _ < ε ^ 2 / 2 := by linarith
    have hlt : ‖T x - y₀‖ ^ 2 < ε ^ 2 := by
      rw [hnorm, ← hds.sum_add_tsum_compl (s := F)]
      calc ∑ i ∈ F, (c i - a i) ^ 2 + ∑' i : ↥((F : Set ι)ᶜ), (c i - a i) ^ 2
          < ε ^ 2 / 4 + ε ^ 2 / 2 := add_lt_add_of_le_of_lt hfin htail
        _ < ε ^ 2 := by linarith [pow_pos hε 2]
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  refine lt_of_lt_of_le ?_
    (measure_mono_ae (s := A ∩ B) (t := T ⁻¹' Metric.ball y₀ ε) hsub)
  -- Step 2: independence of the two events
  have hmF_le : (⨆ i ∈ (F : Set ι), coordinateSigma ι i) ≤ MeasurableSpace.pi :=
    iSup₂_le fun i _ => coordinateSigma_le i
  have hmFc_le : (⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i) ≤ MeasurableSpace.pi :=
    iSup₂_le fun i _ => coordinateSigma_le i
  have hindep : ProbabilityTheory.Indep (⨆ i ∈ (F : Set ι), coordinateSigma ι i)
      (⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i) γ := indep_coordinateSigma F
  have hA : MeasurableSet[⨆ i ∈ (F : Set ι), coordinateSigma ι i] A := by
    letI : MeasurableSpace (ι → ℝ) := ⨆ i ∈ (F : Set ι), coordinateSigma ι i
    have : A = ⋂ i ∈ F, (fun x : ι → ℝ => x i) ⁻¹' {t | |√(p i) * t - a i| < δ} := by
      ext x
      simp [hA_def]
    rw [this]
    refine MeasurableSet.biInter F.countable_toSet fun i hi => ?_
    refine le_iSup₂ (f := fun i (_ : i ∈ (F : Set ι)) => coordinateSigma ι i) i hi _ ?_
    exact MeasurableSpace.measurableSet_comap.mpr
      ⟨_, measurableSet_lt (by fun_prop) measurable_const, rfl⟩
  have hSmeas : Measurable[⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i] S := by
    letI : MeasurableSpace (ι → ℝ) := ⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i
    refine Measurable.tsum fun k => ?_
    have hk : Measurable fun x : ι → ℝ => x k :=
      measurable_iff_comap_le.mpr
        (le_iSup₂ (f := fun i (_ : i ∈ ((F : Set ι))ᶜ) => coordinateSigma ι i) (k : ι) k.2)
    exact (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (p k * t ^ 2)).comp hk
  have hB : MeasurableSet[⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i] B := by
    letI : MeasurableSpace (ι → ℝ) := ⨆ i ∈ ((F : Set ι))ᶜ, coordinateSigma ι i
    exact measurableSet_lt hSmeas measurable_const
  have hA' : MeasurableSet A := hmF_le _ hA
  have hB' : MeasurableSet B := hmFc_le _ hB
  have hAB : γ (A ∩ B) = γ A * γ B :=
    (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hA' hB' (μ := γ)).mp
      ((ProbabilityTheory.indep_iff_forall_indepSet γ).mp hindep A B hA hB)
  rw [hAB]
  refine ENNReal.mul_pos ?_ ?_
  · -- Step 3: the cylinder event has positive probability
    have hApi : A = Set.pi (F : Set ι) fun i =>
        (fun t : ℝ => √(p i) * t) ⁻¹' Set.Ioo (a i - δ) (a i + δ) := by
      ext x
      simp only [hA_def, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_preimage,
        Set.mem_Ioo, abs_sub_lt_iff]
      refine forall₂_congr fun i _ => ?_
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hApi, hγ, stdGaussianPi_pi F _ fun i _ => measurableSet_Ioo.preimage (by fun_prop)]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    haveI := isOpenPosMeasure_gaussianReal 0 one_ne_zero
    refine (IsOpen.measure_pos _ (isOpen_Ioo.preimage (by fun_prop)) ⟨a i / √(p i), ?_⟩).ne'
    have hsq : 0 < √(p i) := Real.sqrt_pos.mpr (hp i)
    simp only [Set.mem_preimage, Set.mem_Ioo, mul_div_cancel₀ _ hsq.ne']
    constructor <;> linarith
  · -- Step 4: Markov's inequality for the tail energy
    have hSint : ∫⁻ x, S x ∂γ = ENNReal.ofReal (∑' i : {i // i ∉ F}, p i) :=
      lintegral_tsum_ofReal_mul_sq_comp (fun i : {i // i ∉ F} => (i : ι)) (fun i => p i)
        (fun i => hp0 i) (hs.subtype _)
    have hc0 : ENNReal.ofReal (ε ^ 2 / 8) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hcompl : γ Bᶜ ≤ ENNReal.ofReal (1 / 2) := by
      have hBc : Bᶜ = {x | ENNReal.ofReal (ε ^ 2 / 8) ≤ S x} := by
        ext x
        simp [hB_def]
      rw [hBc]
      refine (meas_ge_le_lintegral_div (hSmeas.mono hmFc_le le_rfl).aemeasurable hc0
        ENNReal.ofReal_ne_top).trans ?_
      rw [hSint, ← ENNReal.ofReal_div_of_pos (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (by positivity)]
      linarith
    have htot := measure_add_measure_compl (μ := γ) hB'
    rw [measure_univ] at htot
    intro h0
    rw [h0, zero_add] at htot
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) := htot ▸ hcompl
    have h2 : ENNReal.ofReal (1 / 2) < 1 := ENNReal.ofReal_lt_one.mpr (by norm_num)
    exact absurd (lt_of_lt_of_le h2 this) (lt_irrefl _)

/-! ### Gaussian measures in the sense of Mathlib -/

/-- A finite measure on a Hilbert space whose characteristic function is `exp (-⟪P t, t⟫ / 2)`
for a positive self-adjoint `P` is a Gaussian measure (`ProbabilityTheory.IsGaussian`). -/
theorem isGaussian_of_charFun_eq_exp [CompleteSpace H] {μ : Measure H} [IsFiniteMeasure μ]
    {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) (hpos : ∀ x, 0 ≤ ⟪P x, x⟫)
    (h : ∀ t, charFun μ t = Complex.exp (-((⟪P t, t⟫ / 2 : ℝ) : ℂ))) : IsGaussian μ := by
  rw [isGaussian_iff_gaussian_charFun]
  refine ⟨0, (innerSL ℝ).comp P, ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, fun t => ?_⟩
  · change ⟪P x, y⟫ = ⟪P y, x⟫
    rw [show ⟪P x, y⟫ = ⟪(P : H →ₗ[ℝ] H) x, y⟫ from rfl, hP.isSymmetric x y]
    exact real_inner_comm _ _
  · exact hpos x
  · rw [h t, inner_zero_right]
    congr 1
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofReal_zero, zero_mul,
      zero_sub]
    push_cast
    ring

end ProbabilityTheory
