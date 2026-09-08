import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Transform.Mixture
import OperatorRidgelet.ToMathlib.TraceClassEigenbasis
import OperatorRidgelet.ToMathlib.GaussianHilbert
import OperatorRidgelet.ToMathlib.GaussianQuadraticForm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Gaussian layers `𝒩(0,2sP)` and their small-ball estimates

The Gaussian series construction of Appendix A.  A trace-class covariance `P` has a countable
Hilbert basis `e_k` of eigenvectors with positive summable eigenvalues `p_k`
(`IsTraceClassCovariance.exists_eigenbasis`, from
`OperatorRidgelet.ToMathlib.TraceClassEigenbasis`), and the Gaussian series `∑ √p_k Z_k e_k`
(`ProbabilityTheory.gaussianSeries`, from `OperatorRidgelet.ToMathlib.GaussianHilbert`) is
`𝒩(0,P)`; the layers are its dilates
`𝒩(0,2sP) = (√(2s) ·)_# 𝒩(0,P)`.  By Fourier uniqueness every family of layers is of this form
(`IsCenteredGaussianLayers.eq_map_smul`), which gives the coordinate description of an arbitrary
family of layers used in the proofs of Lemma `lem:homogeneous-mixture`: the small-ball estimate
`𝒩(0,2sP)(B_r) ≤ C_k s^{-k/2}` through `k` coordinates, and the finiteness of the mixture `ν_α`
on balls for `k > α`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Spectral data of a trace-class covariance -/

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- A trace-class covariance has a countable Hilbert basis of eigenvectors with positive,
summable eigenvalues. -/
theorem IsTraceClassCovariance.exists_eigenbasis {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) :
    ∃ (κ : Type) (_ : Countable κ) (e : HilbertBasis κ ℝ H) (p : κ → ℝ),
      (∀ k, 0 < p k) ∧ Summable p ∧ ∀ k, P (e k) = p k • e k := by
  obtain ⟨ι, b, hb⟩ := hP.hasSummableTrace
  exact ContinuousLinearMap.exists_hilbertBasis_eigenvector hP.isSelfAdjoint hP.inner_nonneg
    hP.injective b hb

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The eigen-expansion of the quadratic form: `⟪P ξ, ξ⟫ = ∑ p_k ⟪e_k, ξ⟫²`. -/
theorem inner_map_self_eq_tsum_of_eigen {P : H →L[ℝ] H} {κ : Type*} (e : HilbertBasis κ ℝ H)
    (p : κ → ℝ) (hPe : ∀ k, P (e k) = p k • e k) (ξ : H) :
    ⟪P ξ, ξ⟫ = ∑' k, p k * ⟪e k, ξ⟫ ^ 2 :=
  (ContinuousLinearMap.hasSum_inner_map_self_of_eigen e p hPe ξ).tsum_eq.symm

/-! ### `𝒩(0,P)` and the layers -/

section Layers

variable {P : H →L[ℝ] H}

omit [CompleteSpace H] in
/-- The Gaussian series with the spectral data of `P` is `𝒩(0,P)`. -/
theorem isCenteredGaussian_gaussianSeries {κ : Type*} [Countable κ] (e : HilbertBasis κ ℝ H)
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (hPe : ∀ k, P (e k) = p k • e k) :
    IsCenteredGaussian P (gaussianSeries e p) where
  isProbabilityMeasure := inferInstance
  charFun_eq ξ := by
    rw [charFun_gaussianSeries e p hp hs, inner_map_self_eq_tsum_of_eigen e p hPe]
    congr 1
    push_cast
    ring

/-- A trace-class covariance is the covariance of a centred Gaussian measure. -/
theorem IsTraceClassCovariance.exists_isCenteredGaussian (hP : IsTraceClassCovariance P) :
    ∃ μ : Measure H, IsCenteredGaussian P μ := by
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hP.exists_eigenbasis
  exact ⟨gaussianSeries e p, isCenteredGaussian_gaussianSeries e p (fun k => (hp k).le) hs hPe⟩

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- The dilate `(√(2s) ·)_# 𝒩(0,P)` is `𝒩(0,2sP)`. -/
theorem IsCenteredGaussian.map_smul_sqrt {μ : Measure H} (hμ : IsCenteredGaussian P μ) {s : ℝ}
    (hs : 0 < s) :
    IsCenteredGaussian ((2 * s) • P) (μ.map fun x => √(2 * s) • x) where
  isProbabilityMeasure := by
    haveI := hμ.isProbabilityMeasure
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  charFun_eq ξ := by
    rw [charFun_map_smul, hμ.charFun_eq]
    have : ⟪P (√(2 * s) • ξ), √(2 * s) • ξ⟫ = ⟪((2 * s) • P) ξ, ξ⟫ := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, smul_apply,
        real_inner_smul_left, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
    rw [this]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- The dilates `(√(2s) ·)_# 𝒩(0,P)` form a family of Gaussian layers. -/
theorem IsCenteredGaussian.isCenteredGaussianLayers_map_smul {μ : Measure H}
    (hμ : IsCenteredGaussian P μ) :
    IsCenteredGaussianLayers P fun s => μ.map fun x => √(2 * s) • x :=
  fun _ hs => hμ.map_smul_sqrt hs

/-- Uniqueness of the centred Gaussian with a given covariance (Fourier uniqueness). -/
theorem IsCenteredGaussian.unique {Q : H →L[ℝ] H} {μ μ' : Measure H}
    (hμ : IsCenteredGaussian Q μ) (hμ' : IsCenteredGaussian Q μ') : μ = μ' := by
  haveI := hμ.isProbabilityMeasure
  haveI := hμ'.isProbabilityMeasure
  exact Measure.ext_of_charFun (funext fun ξ => by rw [hμ.charFun_eq, hμ'.charFun_eq])

/-- Every family of layers consists of the dilates of `𝒩(0,P)`. -/
theorem IsCenteredGaussianLayers.eq_map_smul {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {μ : Measure H} (hμ : IsCenteredGaussian P μ) {s : ℝ}
    (hs : 0 < s) : N s = μ.map fun x => √(2 * s) • x :=
  (hN s hs).unique (hμ.map_smul_sqrt hs)

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The preimage of a ball under a positive dilation. -/
theorem preimage_smul_closedBall {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (fun x : H => c • x) ⁻¹' Metric.closedBall 0 r = Metric.closedBall 0 (r / c) := by
  ext x
  simp only [Set.mem_preimage, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, le_div_iff₀ hc]
  rw [mul_comm]

/-- The layer at scale `s` of a ball is `𝒩(0,P)` of the ball shrunk by `√(2s)`. -/
theorem IsCenteredGaussianLayers.apply_closedBall {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {μ : Measure H} (hμ : IsCenteredGaussian P μ) {s : ℝ}
    (hs : 0 < s) (r : ℝ) :
    N s (Metric.closedBall 0 r) = μ (Metric.closedBall 0 (r / √(2 * s))) := by
  rw [hN.eq_map_smul hμ hs, Measure.map_apply (by fun_prop) measurableSet_closedBall,
    preimage_smul_closedBall (by positivity)]

end Layers

/-! ### Small-ball estimates -/

section SmallBall

variable {P : H →L[ℝ] H} {κ : Type*} [Countable κ] (e : HilbertBasis κ ℝ H) (p : κ → ℝ)

omit [CompleteSpace H] in
/-- The small-ball estimate through the coordinates in `F`:
`𝒩(0,P)(B_r) ≤ (∏_{k ∈ F} 2 (2π p_k)^{-1/2}) r^{|F|}`. -/
theorem gaussianSeries_closedBall_le_pow (hp : ∀ k, 0 < p k) (hs : Summable p) (F : Finset κ)
    {r : ℝ} (hr : 0 ≤ r) :
    gaussianSeries e p (Metric.closedBall 0 r) ≤
      ENNReal.ofReal ((∏ k ∈ F, 2 / √(2 * Real.pi * p k)) * r ^ F.card) := by
  refine (gaussianSeries_closedBall_le e p (fun k => (hp k).le) hs F r).trans ?_
  have hfac : ∀ k ∈ F, gaussianReal 0 (p k).toNNReal (Set.Icc (-r) r) ≤
      ENNReal.ofReal (2 / √(2 * Real.pi * p k) * r) := by
    intro k _
    have hne : (p k).toNNReal ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact hp k
    refine (gaussianReal_Icc_le 0 hne r).trans (le_of_eq ?_)
    rw [Real.coe_toNNReal _ (hp k).le]
    ring_nf
  calc ∏ k ∈ F, gaussianReal 0 (p k).toNNReal (Set.Icc (-r) r)
      ≤ ∏ k ∈ F, ENNReal.ofReal (2 / √(2 * Real.pi * p k) * r) :=
        Finset.prod_le_prod (fun _ _ => zero_le) hfac
    _ = ENNReal.ofReal (∏ k ∈ F, 2 / √(2 * Real.pi * p k) * r) := by
        rw [ENNReal.ofReal_prod_of_nonneg]
        intro k _
        positivity
    _ = ENNReal.ofReal ((∏ k ∈ F, 2 / √(2 * Real.pi * p k)) * r ^ F.card) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The scaling of the small-ball bound: `(r / √(2s))^k = (r^k / 2^{k/2}) s^{-k/2}`. -/
theorem div_sqrt_pow_eq (r : ℝ) {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (r / √(2 * s)) ^ k = r ^ k / 2 ^ ((k : ℝ) / 2) * s ^ (-((k : ℝ) / 2)) := by
  have h2s : 0 ≤ 2 * s := by positivity
  have h1 : (√(2 * s)) ^ k = 2 ^ ((k : ℝ) / 2) * s ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2s,
      show 1 / 2 * (k : ℝ) = (k : ℝ) / 2 by ring, Real.mul_rpow (by norm_num) hs.le]
  rw [div_pow, h1, Real.rpow_neg hs.le]
  ring

/-- The small-ball estimate for the layers: for `s > 0` and a set of `k` coordinates,
`𝒩(0,2sP)(B_r) ≤ C s^{-k/2}`. -/
theorem IsCenteredGaussianLayers.closedBall_le_rpow {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) (hp : ∀ k, 0 < p k) (hs : Summable p)
    (hPe : ∀ k, P (e k) = p k • e k) (F : Finset κ) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs' : 0 < s) :
    N s (Metric.closedBall 0 r) ≤
      ENNReal.ofReal (((∏ k ∈ F, 2 / √(2 * Real.pi * p k)) * (r ^ F.card / 2 ^ ((F.card : ℝ) / 2)))
        * s ^ (-((F.card : ℝ) / 2))) := by
  have hμ := isCenteredGaussian_gaussianSeries e p (fun k => (hp k).le) hs hPe
  rw [hN.apply_closedBall hμ hs']
  refine (gaussianSeries_closedBall_le_pow e p hp hs F (by positivity)).trans (le_of_eq ?_)
  rw [div_sqrt_pow_eq r hs', mul_assoc]

/-- The mixture `ν_α` is finite on balls: `∫₀^∞ 𝒩(0,2sP)(B_r) s^{α/2-1} ds < ∞` as soon as `H`
has `k > α` eigen-directions. -/
theorem IsCenteredGaussianLayers.gaussianMixture_closedBall_lt_top {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) (hp : ∀ k, 0 < p k) (hs : Summable p)
    (hPe : ∀ k, P (e k) = p k • e k) {α : ℝ} (hα : 0 < α) (F : Finset κ) (hF : α < F.card)
    {r : ℝ} (hr : 0 ≤ r) :
    gaussianMixture N α (Metric.closedBall 0 r) < ⊤ := by
  set B := Metric.closedBall (0 : H) r
  set C : ℝ := (∏ k ∈ F, 2 / √(2 * Real.pi * p k)) * (r ^ F.card / 2 ^ ((F.card : ℝ) / 2))
  have hC : 0 ≤ C := by positivity
  set β : ℝ := -((F.card : ℝ) / 2) + (α / 2 - 1) with hβ
  have hβlt : β < -1 := by
    rw [hβ]
    linarith
  rw [gaussianMixture, hN.gaussianMixtureOn_apply α measurableSet_Ioi le_rfl
    measurableSet_closedBall]
  -- split the scale integral at `s = 1`
  have hsplit : ∫⁻ s in Set.Ioi 0, N s B * ENNReal.ofReal (s ^ (α / 2 - 1)) ≤
      (∫⁻ s in Set.Ioc 0 1, N s B * ENNReal.ofReal (s ^ (α / 2 - 1))) +
        ∫⁻ s in Set.Ioi 1, N s B * ENNReal.ofReal (s ^ (α / 2 - 1)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact lintegral_union_le _ _ _
  refine lt_of_le_of_lt hsplit (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
  · -- small scales: the layers are probability measures
    have h1 : ∫⁻ s in Set.Ioc 0 1, N s B * ENNReal.ofReal (s ^ (α / 2 - 1)) ≤
        ∫⁻ s in Set.Ioc 0 1, ENNReal.ofReal (s ^ (α / 2 - 1)) := by
      refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
      haveI := hN.isProbabilityMeasure hs.1
      calc N s B * ENNReal.ofReal (s ^ (α / 2 - 1))
          ≤ 1 * ENNReal.ofReal (s ^ (α / 2 - 1)) := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (s ^ (α / 2 - 1)) := one_mul _
    refine lt_of_le_of_lt h1 ?_
    have hint : IntegrableOn (fun s : ℝ => s ^ (α / 2 - 1)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun s : ℝ => s ^ (α / 2 - 1) :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => Real.rpow_nonneg hs.1.le _
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral
  · -- large scales: the small-ball estimate
    have h2 : ∫⁻ s in Set.Ioi 1, N s B * ENNReal.ofReal (s ^ (α / 2 - 1)) ≤
        ∫⁻ s in Set.Ioi 1, ENNReal.ofReal (C * s ^ β) := by
      refine setLIntegral_mono' measurableSet_Ioi fun s hs1 => ?_
      have hs0 : 0 < s := lt_trans one_pos hs1
      calc N s B * ENNReal.ofReal (s ^ (α / 2 - 1))
          ≤ ENNReal.ofReal (C * s ^ (-((F.card : ℝ) / 2))) *
              ENNReal.ofReal (s ^ (α / 2 - 1)) := by
            gcongr
            exact hN.closedBall_le_rpow e p hp hs hPe F hr hs0
        _ = ENNReal.ofReal (C * s ^ β) := by
            rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.rpow_add hs0]
    refine lt_of_le_of_lt h2 ?_
    have hint : IntegrableOn (fun s : ℝ => C * s ^ β) (Set.Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff one_pos).mpr hβlt).const_mul C
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun s : ℝ => C * s ^ β :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
        mul_nonneg hC (Real.rpow_nonneg (lt_trans one_pos hs).le _)
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral

end SmallBall

/-! ### Infinite dimension -/

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- A Hilbert basis of an infinite-dimensional space has an infinite index type. -/
theorem HilbertBasis.infinite_of_not_finiteDimensional (hH : ¬ FiniteDimensional ℝ H)
    {κ : Type*} (e : HilbertBasis κ ℝ H) : Infinite κ := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI := Fintype.ofFinite κ
  exact hH (Module.Finite.of_basis e.toOrthonormalBasis.toBasis)

/-- In infinite dimension the mixture `ν_α` is finite on bounded sets: choose `k > α`
eigen-directions in the small-ball estimate. -/
theorem IsTraceClassCovariance.gaussianMixture_lt_top_of_isBounded (hH : ¬ FiniteDimensional ℝ H)
    {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) {E : Set H}
    (hE : Bornology.IsBounded E) : gaussianMixture N α E < ⊤ := by
  obtain ⟨R, hR⟩ := hE.subset_closedBall 0
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hP.exists_eigenbasis
  haveI : Infinite κ := HilbertBasis.infinite_of_not_finiteDimensional hH e
  obtain ⟨k, hk⟩ := exists_nat_gt α
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq κ k
  refine lt_of_le_of_lt (measure_mono
    (hR.trans (Metric.closedBall_subset_closedBall (le_abs_self R)))) ?_
  refine hN.gaussianMixture_closedBall_lt_top e p hp hs hPe hα F ?_ (abs_nonneg R)
  rw [hF]
  exact hk

/-- The mixture `ν_α` has full support: every layer is a dilate of `𝒩(0,P)`, which charges every
nonempty open set. -/
theorem IsTraceClassCovariance.isOpenPosMeasure_gaussianMixture {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) : (gaussianMixture N α).IsOpenPosMeasure := by
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hP.exists_eigenbasis
  have hμ := isCenteredGaussian_gaussianSeries e p (fun k => (hp k).le) hs hPe
  haveI := isOpenPosMeasure_gaussianSeries e p hp hs
  refine ⟨fun U hU hne => ?_⟩
  have hlayer : ∀ s, 0 < s → N s U ≠ 0 := by
    intro s hs'
    rw [hN.eq_map_smul hμ hs', Measure.map_apply (by fun_prop) hU.measurableSet]
    refine (IsOpen.measure_pos _ (hU.preimage (by fun_prop)) ?_).ne'
    obtain ⟨y, hy⟩ := hne
    refine ⟨(√(2 * s))⁻¹ • y, ?_⟩
    simp only [Set.mem_preimage, smul_inv_smul₀ (by positivity : √(2 * s) ≠ 0)]
    exact hy
  rw [gaussianMixture, hN.gaussianMixtureOn_eq_bind α measurableSet_Ioi le_rfl,
    Measure.bind_apply hU.measurableSet hN.measurable_scaledLayer.aemeasurable]
  refine ne_of_gt ((lintegral_pos_iff_support
    ((Measure.measurable_coe hU.measurableSet).comp hN.measurable_scaledLayer)).mpr ?_)
  refine lt_of_lt_of_le ?_ (measure_mono (s := Set.Ioi 0)
    (t := Function.support fun s => scaledLayer N s U) fun s hs' => ?_)
  · rw [mixtureWeight, withDensity_apply _ measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Set.inter_self, lintegral_Ioi_rpow_eq_top]
    exact ENNReal.zero_lt_top
  · rw [Function.mem_support, ← hN.eq_scaledLayer hs']
    exact hlayer s hs'

/-- In infinite dimension the mixture `ν_α` is locally finite. -/
theorem IsTraceClassCovariance.isLocallyFiniteMeasure_gaussianMixture
    (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    IsLocallyFiniteMeasure (gaussianMixture N α) :=
  ⟨fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
    hP.gaussianMixture_lt_top_of_isBounded hH hN hα Metric.isBounded_ball⟩⟩

/-! ### Gaussian decay: Lemma `lem:gaussian-decay` -/

section Decay

variable {P Q : H →L[ℝ] H}

/-- `𝒩(0,P)` is a Gaussian measure in the sense of Mathlib. -/
theorem isGaussian_gaussianSeries (hP : IsTraceClassCovariance P) {κ : Type*} [Countable κ]
    (e : HilbertBasis κ ℝ H) (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hPe : ∀ k, P (e k) = p k • e k) : IsGaussian (gaussianSeries e p) :=
  isGaussian_of_charFun_eq_exp hP.isSelfAdjoint hP.inner_nonneg
    (isCenteredGaussian_gaussianSeries e p hp hs hPe).charFun_eq

/-- All moments of `𝒩(0,P)` are finite (Fernique). -/
theorem lintegral_norm_pow_gaussianSeries_lt_top (hP : IsTraceClassCovariance P) {κ : Type*}
    [Countable κ] (e : HilbertBasis κ ℝ H) (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hPe : ∀ k, P (e k) = p k • e k) (n : ℕ) :
    ∫⁻ a, ENNReal.ofReal (‖a‖ ^ n) ∂gaussianSeries e p < ⊤ := by
  haveI := isGaussian_gaussianSeries hP e p hp hs hPe
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hmem : MemLp id n (gaussianSeries e p) :=
    IsGaussian.memLp_id (gaussianSeries e p) n (ENNReal.natCast_ne_top n)
  have hint : Integrable (fun a : H => ‖a‖ ^ n) (gaussianSeries e p) := by
    simpa using hmem.integrable_norm_pow hn.ne'
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun a => by positivity)).mp
    hint.hasFiniteIntegral

omit [CompleteSpace H] in
/-- `𝒩(0,P)` has no atom at the origin. -/
theorem gaussianSeries_singleton_zero {κ : Type*} [Countable κ] [Nonempty κ]
    (e : HilbertBasis κ ℝ H) (p : κ → ℝ) (hp : ∀ k, 0 < p k) (hs : Summable p) :
    gaussianSeries e p {0} = 0 := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hsub : ({0} : Set H) ⊆ {y | ∀ i ∈ ({k} : Finset κ), ⟪e i, y⟫ ∈ ({0} : Set ℝ)} := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    intro i _
    simp [hy]
  refine le_antisymm ((measure_mono hsub).trans (le_of_eq ?_)) zero_le
  rw [gaussianSeries_setOf_inner_mem e p (fun k => (hp k).le) hs {k} _
    (fun _ _ => measurableSet_singleton 0), Finset.prod_singleton]
  have hne : (p k).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hp k
  exact gaussianReal_absolutelyContinuous 0 hne Real.volume_singleton

omit [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H] in
/-- A mixed moment bound: `‖a‖^{2m} q^{-β} ≤ ‖a‖^{4m} + q^{-2β}`. -/
theorem lintegral_ofReal_norm_pow_mul_rpow_neg_lt_top {μ : Measure H} {q : H → ℝ}
    (hq0 : ∀ a, 0 ≤ q a) (m : ℕ) {β : ℝ}
    (h1 : ∫⁻ a, ENNReal.ofReal (‖a‖ ^ (4 * m)) ∂μ < ⊤)
    (h2 : ∫⁻ a, ENNReal.ofReal (q a ^ (-(2 * β))) ∂μ < ⊤) :
    ∫⁻ a, ENNReal.ofReal (‖a‖ ^ (2 * m) * q a ^ (-β)) ∂μ < ⊤ := by
  calc ∫⁻ a, ENNReal.ofReal (‖a‖ ^ (2 * m) * q a ^ (-β)) ∂μ
      ≤ ∫⁻ a, (ENNReal.ofReal (‖a‖ ^ (4 * m)) + ENNReal.ofReal (q a ^ (-(2 * β)))) ∂μ := by
        refine lintegral_mono fun a => ?_
        rw [← ENNReal.ofReal_add (by positivity) (Real.rpow_nonneg (hq0 a) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hx : 0 ≤ ‖a‖ ^ (2 * m) := by positivity
        have hy : 0 ≤ q a ^ (-β) := Real.rpow_nonneg (hq0 a) _
        have hsq : (q a ^ (-β)) ^ 2 = q a ^ (-(2 * β)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hq0 a)]
          congr 1
          push_cast
          ring
        have hx2 : (‖a‖ ^ (2 * m)) ^ 2 = ‖a‖ ^ (4 * m) := by
          rw [← pow_mul]
          congr 1
          ring
        rw [← hsq, ← hx2]
        nlinarith [sq_nonneg (‖a‖ ^ (2 * m) - q a ^ (-β)), mul_nonneg hx hy]
    _ = (∫⁻ a, ENNReal.ofReal (‖a‖ ^ (4 * m)) ∂μ) +
          ∫⁻ a, ENNReal.ofReal (q a ^ (-(2 * β))) ∂μ :=
        lintegral_add_left ((measurable_norm.pow_const _).ennreal_ofReal) _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h1, h2⟩

/-- The scale integral of a Gaussian layer: `∫₀^∞ s^{β-1} e^{-rs} ds = r^{-β} Γ(β)`, as a
Lebesgue integral. -/
theorem lintegral_Ioi_rpow_mul_exp_neg_mul {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * Real.exp (-(r * s))) =
      ENNReal.ofReal ((1 / r) ^ β * Real.Gamma β) := by
  have hint : IntegrableOn (fun s : ℝ => s ^ (β - 1) * Real.exp (-(r * s))) (Set.Ioi 0) := by
    have h0 := Real.GammaIntegral_convergent hβ
    have h1 : IntegrableOn (fun s : ℝ => Real.exp (-(r * s)) * (r * s) ^ (β - 1))
        (Set.Ioi 0) := by
      have := (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x) * x ^ (β - 1)) 0 hr).mpr (by simpa using h0)
      exact this
    refine IntegrableOn.congr_fun (h1.const_mul ((r ^ (β - 1))⁻¹)) (fun s hs => ?_)
      measurableSet_Ioi
    have hs' : 0 < s := hs
    rw [Real.mul_rpow hr.le hs'.le]
    field_simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (Real.exp_pos _).le),
    Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hr]

/-- Lemma `lem:gaussian-decay` (i) in Lebesgue form: `∫ ‖ξ‖^{2m} e^{-t⟪Qξ,ξ⟫} dν_α < ∞`. -/
theorem IsTraceClassCovariance.lintegral_norm_pow_mul_exp_gaussianMixture_lt_top
    (hH : ¬ FiniteDimensional ℝ H) (hP : IsTraceClassCovariance P)
    (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ∂gaussianMixture N α < ⊤ := by
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hP.exists_eigenbasis
  have hp0 : ∀ k, 0 ≤ p k := fun k => (hp k).le
  have hμ := isCenteredGaussian_gaussianSeries e p hp0 hs hPe
  haveI : Infinite κ := HilbertBasis.infinite_of_not_finiteDimensional hH e
  set q : H → ℝ := fun a => ⟪Q a, a⟫ with hq_def
  have hq0 : ∀ a, 0 ≤ q a := fun a => hQ.inner_nonneg a
  have hqm : Measurable q := by fun_prop
  set β : ℝ := m + α / 2 with hβ_def
  have hβ : 0 < β := by positivity
  set K : ℝ := 2 ^ m * Real.Gamma β * (2 * t) ^ (-β) with hK_def
  have hK : 0 ≤ K := by positivity
  -- the integrand on the layers, transported to `𝒩(0,P)`
  set F : H → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * m) * Real.exp (-t * q ξ)) with hF_def
  have hFm : Measurable F := by fun_prop
  set G : ℝ → H → ℝ≥0∞ := fun s a =>
    ENNReal.ofReal (‖a‖ ^ (2 * m) * 2 ^ m * (s ^ (β - 1) * Real.exp (-(2 * t * q a * s))))
    with hG_def
  have hGm : Measurable (Function.uncurry G) := by
    simp only [hG_def, Function.uncurry_def]
    fun_prop
  have hlayer : ∀ s ∈ Set.Ioi (0 : ℝ), (∫⁻ ξ, F ξ ∂N s) * ENNReal.ofReal (s ^ (α / 2 - 1)) =
      ∫⁻ a, G s a ∂gaussianSeries e p := by
    intro s hs'
    have hs0 : 0 < s := hs'
    rw [hN.eq_map_smul hμ hs0, lintegral_map hFm (by fun_prop),
      ← lintegral_mul_const _ (by fun_prop)]
    refine lintegral_congr fun a => ?_
    simp only [hF_def, hG_def]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ‖√(2 * s) • a‖ ^ (2 * m) = (2 * s) ^ m * ‖a‖ ^ (2 * m) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, pow_mul,
        Real.sq_sqrt (by positivity)]
    have h2 : q (√(2 * s) • a) = 2 * s * q a := by
      simp only [hq_def]
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
        Real.mul_self_sqrt (by positivity)]
    have h3 : s ^ (β - 1) = s ^ m * s ^ (α / 2 - 1) := by
      rw [hβ_def, show (m : ℝ) + α / 2 - 1 = (m : ℝ) + (α / 2 - 1) by ring, Real.rpow_add hs0,
        Real.rpow_natCast]
    have h4 : Real.exp (-t * (2 * s * q a)) = Real.exp (-(2 * t * q a * s)) := by
      congr 1
      ring
    rw [h1, h2, h3, h4, mul_pow]
    ring
  rw [gaussianMixture, hN.lintegral_gaussianMixtureOn α measurableSet_Ioi le_rfl hFm,
    setLIntegral_congr_fun measurableSet_Ioi hlayer,
    lintegral_lintegral_swap hGm.aemeasurable]
  -- the scale integral for `a ≠ 0`
  have hinner : ∀ a : H, 0 < q a →
      ∫⁻ s in Set.Ioi 0, G s a = ENNReal.ofReal (K * (‖a‖ ^ (2 * m) * q a ^ (-β))) := by
    intro a hqa
    have hr : 0 < 2 * t * q a := by positivity
    have : ∀ s, G s a = ENNReal.ofReal (‖a‖ ^ (2 * m) * 2 ^ m) *
        ENNReal.ofReal (s ^ (β - 1) * Real.exp (-(2 * t * q a * s))) := fun s => by
      rw [hG_def]
      simp only
      rw [ENNReal.ofReal_mul (by positivity)]
    simp_rw [this]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioi_rpow_mul_exp_neg_mul hβ hr,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hK_def, one_div, mul_inv, Real.mul_rpow (inv_nonneg.mpr (by positivity))
      (inv_nonneg.mpr hqa.le), Real.inv_rpow (by positivity), Real.inv_rpow hqa.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_neg hqa.le]
    ring
  have hae : ∀ᵐ a ∂gaussianSeries e p, 0 < q a := by
    have h0 : ∀ᵐ a ∂gaussianSeries e p, a ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      exact gaussianSeries_singleton_zero e p hp hs
    filter_upwards [h0] with a ha
    exact hQ.isSelfAdjoint.isSymmetric.inner_map_self_pos_of_injective hQ.inner_nonneg
      hQ.injective ha
  rw [lintegral_congr_ae (hae.mono fun a ha => hinner a ha)]
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- the negative moment of `⟪Q a, a⟫` and the Fernique moments
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq κ (⌈4 * (m : ℝ) + 2 * α⌉₊ + 1)
  obtain ⟨C, hC, hsb⟩ := gaussianSeries_inner_map_lt_le e p hp hs hQ.isSelfAdjoint.isSymmetric
    hQ.inner_nonneg hQ.injective F
  have hk : 2 * (2 * β) < (F.card : ℝ) := by
    rw [hF, hβ_def]
    push_cast
    have := Nat.le_ceil (4 * (m : ℝ) + 2 * α)
    linarith
  refine lintegral_ofReal_norm_pow_mul_rpow_neg_lt_top hq0 m
    (lintegral_norm_pow_gaussianSeries_lt_top hP e p hp0 hs hPe _) ?_
  exact lintegral_ofReal_rpow_neg_lt_top hqm hq0 hC hsb (by positivity) hk

end Decay

/-! ### The weighted Fourier transform -/

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- The weighted Fourier transform of an integrable function is continuous. -/
theorem continuous_gaussFourier (μ : Measure H) {f : H → ℂ} (hf : Integrable f μ) :
    Continuous (gaussFourier μ f) := by
  unfold gaussFourier
  refine continuous_of_dominated (bound := fun x => ‖f x‖) (fun ξ => ?_)
    (fun ξ => Eventually.of_forall fun x => ?_) hf.norm ?_
  · exact hf.aestronglyMeasurable.mul (continuous_character ξ).aestronglyMeasurable
  · rw [norm_mul, norm_character, mul_one]
  · refine Eventually.of_forall fun x => continuous_const.mul ?_
    unfold character
    fun_prop

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- The weighted Fourier transform of the `L²` class of a constant. -/
theorem gaussFourier_toLp_const (μ : Measure H) [IsFiniteMeasure μ] (c : ℂ) :
    gaussFourier μ ((MemLp.toLp (fun _ : H => c) (memLp_const c) : Lp ℂ 2 μ) : H → ℂ) =
      gaussFourier μ fun _ => c := by
  funext ξ
  unfold gaussFourier
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (μ := μ) (p := 2) c)] with x hx
  rw [hx]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- `(1 + x)^n ≤ 2^n (1 + x^n)` for `x ≥ 0`. -/
theorem one_add_pow_le_two_pow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ 2 ^ n * (1 + x ^ n) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    have := le_max_left 1 x
    have := le_max_right 1 x
    linarith
  calc (1 + x) ^ n ≤ (2 * max 1 x) ^ n := pow_le_pow_left₀ (by positivity) h1 n
    _ = 2 ^ n * (max 1 x) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + x ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases max_choice 1 x with h | h <;> rw [h]
        · rw [one_pow]
          exact le_add_of_nonneg_right (by positivity)
        · exact le_add_of_nonneg_left zero_le_one

end OperatorRidgelet
