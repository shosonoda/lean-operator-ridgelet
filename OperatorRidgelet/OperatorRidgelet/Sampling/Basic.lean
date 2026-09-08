import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Architecture.Basic
import OperatorRidgelet.ToMathlib.MeasurePi
import OperatorRidgelet.ToMathlib.ComplexMeasurePolar
import OperatorRidgelet.ToMathlib.Symmetrization
import OperatorRidgelet.ToMathlib.IntegralSqrt
import OperatorRidgelet.ToMathlib.VectorMeasureWithDensity
import OperatorRidgelet.ToFoML.RademacherSigns
import OperatorRidgelet.ToFoML.ProbabilisticMethod
import OperatorRidgelet.ToFoML.BoundedDifference
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Auxiliary lemmas for Section 6 (finite-width approximation) and Appendix D

Facts used by the proofs of `OperatorRidgelet.Paper.Sampling`.

* The compact sup norm is a nonnegative supremum, and it is the norm of `C(K)` for the
  restriction of a function to `K` (`compactSupNorm_eq_norm_of_forall`); orthogonal projections
  are contractions; the product law `sampleLaw N p = p^{⊗N}` is a probability measure.
* The polar decomposition `Γ = h |Γ|` of a complex measure of finite variation exists
  (`OperatorRidgelet.ToMathlib.ComplexMeasurePolar`), so `polarDensity Γ` satisfies its
  specification (`polarDensity_spec`), `polarLaw Γ` is a probability measure when `Γ ≠ 0`, and
  the integral network is the Bochner integral of the atoms against `p = |Γ|/V`
  (`integralNetwork_eq_integral_polarLaw`).
* The ridge atoms `x ↦ β(⟪a, x⟫ + c)` restricted to a compact `K` form a continuous, hence
  strongly measurable, map `ridgeAtom hK hβ : H × ℝ → C(K)` (`C(K)` is separable), and the
  `C(K)`-valued atoms `h(ω) β(⟪a, ·⟫ + c)` of a sampled network are Bochner integrable under
  the second-moment condition (`integrable_smul_ridgeAtom`).
* The dimension-free Barron bound in `C(K)` for the empirical mean of these atoms
  (`integral_norm_sum_smul_ridgeAtom_sub_le`), from the symmetrization inequality, the
  contraction principle, and the Hilbert-space Rademacher average; it is stated on an abstract
  probability space with a measurable parameter map `π : Ω → H × ℝ`, which covers the scalar,
  operator, and truncated-direction sampled networks at once.
* The ingredients of the two corollaries of Appendix D: the envelope `|β(0)| + Lip(β) R_K B` of
  a ridge atom with `‖a‖² + c² ≤ B²` (`norm_ridgeAtom_le_of_sq_le`, for the bounded-difference
  constant of Corollary `cor:sampling-concentration`), the pointwise bound of the sampled-network
  error by its compact sup norm (`norm_polarSampledNetwork_sub_le_compactSupNorm`), and the
  Lipschitz estimate for projecting the directions inside the activation
  (`norm_finiteNetwork_sub_finiteNetwork_map_le`, `norm_sampledNetwork_sub_truncated_le`, for
  Corollary `cor:two-stage-error`).

The Hilbert-valued variance identity of Lemma D.3 is the general `integral_norm_sq_sampleMean`
of `OperatorRidgelet.ToMathlib.MeasurePi`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

/-! ### The compact sup norm -/

section SupNorm

variable {X : Type*} {Y : Type*} [NormedAddCommGroup Y]

theorem compactSupNorm_nonneg (K : Set X) (f : X → Y) : 0 ≤ compactSupNorm K f :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ norm_nonneg _

theorem compactSupNorm_le {K : Set X} {f : X → Y} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ K, ‖f x‖ ≤ a) : compactSupNorm K f ≤ a :=
  Real.sSup_le (fun _ ⟨x, hx, hfx⟩ => hfx ▸ h x hx) ha

theorem compactSupNorm_congr_norm {K : Set X} {f g : X → Y} (h : ∀ x ∈ K, ‖f x‖ = ‖g x‖) :
    compactSupNorm K f = compactSupNorm K g := by
  unfold compactSupNorm
  congr 1
  exact Set.image_congr h

theorem compactSupNorm_congr {K : Set X} {f g : X → Y} (h : ∀ x ∈ K, f x = g x) :
    compactSupNorm K f = compactSupNorm K g :=
  compactSupNorm_congr_norm fun x hx => by rw [h x hx]

theorem compactSupNorm_sub_comm {K : Set X} (f g : X → Y) :
    compactSupNorm K (fun x => f x - g x) = compactSupNorm K (fun x => g x - f x) :=
  compactSupNorm_congr_norm fun _ _ => norm_sub_rev _ _

end SupNorm

/-! ### Finite-rank orthogonal projections -/

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An orthogonal projection is a contraction. -/
theorem IsFiniteRankProjection.norm_apply_le {P : H →L[ℝ] H} (hP : IsFiniteRankProjection P)
    (x : H) : ‖P x‖ ≤ ‖x‖ :=
  (P.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x)
    (IsStarProjection.norm_le P hP.isStarProjection))

end Projection

/-! ### The product law is a probability measure -/

instance instIsProbabilityMeasureSampleLaw {Θ : Type*} [MeasurableSpace Θ] (N : ℕ)
    (p : Measure Θ) [IsProbabilityMeasure p] : IsProbabilityMeasure (sampleLaw N p) := by
  unfold sampleLaw
  infer_instance

/-- The product law of a positive number of samples of the zero measure is zero. -/
theorem sampleLaw_zero {Θ : Type*} [MeasurableSpace Θ] {N : ℕ} (hN : 0 < N) :
    sampleLaw N (0 : Measure Θ) = 0 := by
  rw [← Measure.measure_univ_eq_zero, sampleLaw, Measure.pi_univ]
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp [hN.ne']

/-- A property holding `p`-almost surely holds for every coordinate of `p^{⊗N}`-almost every
sample. -/
theorem ae_sampleLaw_forall {Θ : Type*} [MeasurableSpace Θ] {N : ℕ} {p : Measure Θ}
    [IsProbabilityMeasure p] {P : Θ → Prop} (h : ∀ᵐ θ ∂p, P θ) :
    ∀ᵐ θ ∂sampleLaw N p, ∀ j, P (θ j) :=
  Measure.ae_pi_le_pi (Filter.eventually_pi fun _ => h)

/-! ### The polar decomposition of a complex measure -/

section Polar

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The specification of `polarDensity`: for a complex measure of finite variation the polar
decomposition exists, so `‖h‖ = 1` `|Γ|`-almost everywhere and `Γ = |Γ|.withDensityᵥ h`. -/
theorem polarDensity_spec (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation] :
    (∀ᵐ θ ∂Γ.variation, ‖polarDensity Γ θ‖ = 1) ∧
      Γ = Γ.variation.withDensityᵥ (polarDensity Γ) := by
  have h := ComplexMeasure.exists_withDensityᵥ_variation_eq Γ
  unfold polarDensity
  rw [dif_pos h]
  exact h.choose_spec

theorem ae_norm_polarDensity_eq_one (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation] :
    ∀ᵐ θ ∂Γ.variation, ‖polarDensity Γ θ‖ = 1 :=
  (polarDensity_spec Γ).1

theorem withDensityᵥ_polarDensity (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation] :
    Γ.variation.withDensityᵥ (polarDensity Γ) = Γ :=
  (polarDensity_spec Γ).2.symm

/-- The phase of a nonzero complex measure is integrable against the variation. -/
theorem integrable_polarDensity (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation]
    (hΓ : Γ ≠ 0) : Integrable (polarDensity Γ) Γ.variation := by
  by_contra h
  apply hΓ
  rw [← withDensityᵥ_polarDensity Γ, Measure.withDensityᵥ, dif_neg h]

variable {Y : Type*} [NormedAddCommGroup Y]

theorem totalVariation_ne_top (Γ : VectorMeasure Θ Y) [IsFiniteMeasure Γ.variation] :
    totalVariation Γ ≠ ⊤ :=
  measure_ne_top _ _

theorem polarWeight_nonneg (Γ : VectorMeasure Θ Y) : 0 ≤ polarWeight Γ :=
  ENNReal.toReal_nonneg

theorem polarWeight_pos (Γ : VectorMeasure Θ Y) [IsFiniteMeasure Γ.variation]
    (h : totalVariation Γ ≠ 0) : 0 < polarWeight Γ :=
  ENNReal.toReal_pos h (totalVariation_ne_top Γ)

theorem variation_eq_zero_of_totalVariation_eq_zero {Γ : VectorMeasure Θ Y}
    (h : totalVariation Γ = 0) : Γ.variation = 0 :=
  Measure.measure_univ_eq_zero.mp h

theorem polarWeight_eq_zero_of_totalVariation_eq_zero {Γ : VectorMeasure Θ Y}
    (h : totalVariation Γ = 0) : polarWeight Γ = 0 := by
  rw [polarWeight, h, ENNReal.toReal_zero]

theorem polarLaw_eq_zero_of_totalVariation_eq_zero {Γ : VectorMeasure Θ Y}
    (h : totalVariation Γ = 0) : polarLaw Γ = 0 := by
  rw [polarLaw, variation_eq_zero_of_totalVariation_eq_zero h, smul_zero]

theorem totalVariation_eq_zero_of_eq_zero {Γ : VectorMeasure Θ Y} (h : Γ = 0) :
    totalVariation Γ = 0 := by
  rw [h, totalVariation, VectorMeasure.variation_zero]
  rfl

theorem ne_zero_of_totalVariation_ne_zero {Γ : VectorMeasure Θ Y} (h : totalVariation Γ ≠ 0) :
    Γ ≠ 0 :=
  fun h0 => h (totalVariation_eq_zero_of_eq_zero h0)

/-- A vector measure of zero total variation is zero. -/
theorem eq_zero_of_totalVariation_eq_zero {Γ : VectorMeasure Θ Y} (h : totalVariation Γ = 0) :
    Γ = 0 := by
  have hv := variation_eq_zero_of_totalVariation_eq_zero h
  ext s hs
  have h1 : Γ s = 0 := by
    refine VectorMeasure.absolutelyContinuous Γ ?_
    show Γ.variation.toENNRealVectorMeasure s = 0
    rw [Measure.toENNRealVectorMeasure_apply_measurable hs, hv]
    simp
  rw [h1]
  simp

/-- The parameter law `p = |Γ|/V` is a probability measure when `Γ ≠ 0`. -/
theorem isProbabilityMeasure_polarLaw (Γ : VectorMeasure Θ Y) [IsFiniteMeasure Γ.variation]
    (h : totalVariation Γ ≠ 0) : IsProbabilityMeasure (polarLaw Γ) :=
  ⟨by
    rw [polarLaw, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h (totalVariation_ne_top Γ)⟩

/-- `|Γ| = V p`. -/
theorem variation_eq_smul_polarLaw (Γ : VectorMeasure Θ Y) [IsFiniteMeasure Γ.variation]
    (h : totalVariation Γ ≠ 0) :
    Γ.variation = ENNReal.ofReal (polarWeight Γ) • polarLaw Γ := by
  rw [polarWeight, ENNReal.ofReal_toReal (totalVariation_ne_top Γ), polarLaw, smul_smul,
    ENNReal.mul_inv_cancel h (totalVariation_ne_top Γ), one_smul]

theorem polarLaw_absolutelyContinuous (Γ : VectorMeasure Θ Y) : polarLaw Γ ≪ Γ.variation :=
  Measure.smul_absolutelyContinuous

theorem ae_polarLaw_norm_polarDensity_eq_one (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation] :
    ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 :=
  Measure.ae_smul_measure (ae_norm_polarDensity_eq_one Γ) _

theorem aestronglyMeasurable_polarDensity (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation]
    (hΓ : Γ ≠ 0) : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
  (integrable_polarDensity Γ hΓ).aestronglyMeasurable.mono_ac (polarLaw_absolutelyContinuous Γ)

/-- The variation measure with the density `‖h‖ₑ = 1` is the variation itself. -/
theorem withDensity_enorm_polarDensity (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation] :
    (Γ.variation.withDensity fun θ => ‖polarDensity Γ θ‖ₑ) = Γ.variation := by
  rw [withDensity_congr_ae (g := 1) ?_, withDensity_one]
  filter_upwards [ae_norm_polarDensity_eq_one Γ] with θ hθ
  rw [Pi.one_apply, ← ofReal_norm, hθ, ENNReal.ofReal_one]

end Polar

/-! ### Vector-measure integrals as Bochner integrals against the parameter law -/

section IntegralNetwork

variable {Θ : Type*} [MeasurableSpace Θ]

/-- `∫ f dΓ = V ∫ f h dp` for a nonzero complex measure `Γ = h |Γ|` and `f` integrable
against `p = |Γ|/V`. -/
theorem vectorIntegral_eq_integral_polarLaw (Γ : ComplexMeasure Θ) [IsFiniteMeasure Γ.variation]
    (h0 : totalVariation Γ ≠ 0) {f : Θ → ℂ} (hint : Integrable f (polarLaw Γ)) :
    ∫ᵛ θ, f θ ∂[ContinuousLinearMap.lsmul ℝ ℂ; Γ] =
      polarWeight Γ • ∫ θ, f θ • polarDensity Γ θ ∂polarLaw Γ := by
  have hΓ : Γ ≠ 0 := ne_zero_of_totalVariation_ne_zero h0
  conv_lhs => rw [← withDensityᵥ_polarDensity Γ]
  rw [VectorMeasure.integral_withDensityᵥ (integrable_polarDensity Γ hΓ) ?_]
  · simp only [ContinuousLinearMap.lsmul_apply]
    rw [variation_eq_smul_polarLaw Γ h0, integral_smul_measure,
      ENNReal.toReal_ofReal (polarWeight_nonneg Γ)]
  · rw [withDensity_enorm_polarDensity, variation_eq_smul_polarLaw Γ h0]
    exact hint.smul_measure ENNReal.ofReal_ne_top

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- `S_β[Γ](x) = V ∫ β(⟪a, x⟫ + c) h(θ) p(dθ)` for a nonzero complex measure `Γ = h |Γ|`. -/
theorem integralNetwork_eq_integral_polarLaw (β : ℝ → ℂ) (Γ : ComplexMeasure (H × ℝ))
    [IsFiniteMeasure Γ.variation] (h0 : totalVariation Γ ≠ 0) {x : H}
    (hint : Integrable (fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2)) (polarLaw Γ)) :
    integralNetwork β Γ x =
      polarWeight Γ • ∫ θ, β (⟪θ.1, x⟫ + θ.2) • polarDensity Γ θ ∂polarLaw Γ :=
  vectorIntegral_eq_integral_polarLaw Γ h0 hint

/-- The integral network of the zero measure vanishes. -/
theorem integralNetwork_zero (β : ℝ → ℂ) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (x : H) : integralNetwork β (0 : VectorMeasure (H × ℝ) Y) x = 0 :=
  VectorMeasure.integral_zero_vectorMeasure

theorem integralNetwork_eq_zero_of_totalVariation_eq_zero (β : ℝ → ℂ) {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {Γ : VectorMeasure (H × ℝ) Y}
    (h0 : totalVariation Γ = 0) (x : H) : integralNetwork β Γ x = 0 := by
  rw [eq_zero_of_totalVariation_eq_zero h0]
  exact integralNetwork_zero β x

/-- The integral network of a finite atomic measure `∑_j w_j δ_{θ_j}` is the finite network
`x ↦ ∑_j β(⟪a_j, x⟫ + c_j) w_j`. -/
theorem integralNetwork_atomicMeasure [BorelSpace H] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [CompleteSpace Y] (β : ℝ → ℂ) {n : ℕ} (w : Fin n → Y) (θ : Fin n → H × ℝ)
    (x : H) :
    integralNetwork β (atomicMeasure w θ) x = ∑ j, β (⟪(θ j).1, x⟫ + (θ j).2) • w j := by
  rw [integralNetwork, atomicMeasure, VectorMeasure.integral_finsetSum_vectorMeasure]
  · exact Finset.sum_congr rfl fun j _ => VectorMeasure.integral_dirac
  · intro j _
    show Integrable _ (VectorMeasure.dirac (θ j) (w j)).variation
    rw [VectorMeasure.variation_dirac]
    exact ((integrable_const _).congr (ae_eq_dirac _).symm).smul_measure enorm_ne_top

/-- The sampled network of a measure of zero total variation is the zero network. -/
theorem polarSampledNetwork_eq_zero (β : ℝ → ℂ) {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {Γ : VectorMeasure (H × ℝ) Y} (h0 : totalVariation Γ = 0) {N : ℕ}
    (θ : Fin N → H × ℝ) (x : H) : polarSampledNetwork β Γ θ x = 0 := by
  simp [polarSampledNetwork, sampledNetwork, finiteNetwork,
    polarWeight_eq_zero_of_totalVariation_eq_zero h0]

omit [InnerProductSpace ℝ H] in
/-- `∫ ‖a‖ d|Γ| = V ∫ ‖a‖ dp`. -/
theorem integral_norm_fst_variation (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (h0 : totalVariation Γ ≠ 0) :
    ∫ θ, ‖θ.1‖ ∂Γ.variation = polarWeight Γ * ∫ θ, ‖θ.1‖ ∂polarLaw Γ := by
  rw [variation_eq_smul_polarLaw Γ h0, integral_smul_measure,
    ENNReal.toReal_ofReal (polarWeight_nonneg Γ), smul_eq_mul]

end IntegralNetwork

/-! ### The compact sup norm as the norm of `C(K)` -/

section SupNormBCF

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [NormedAddCommGroup Y]

/-- The compact sup norm of `g` on `K` is the norm of any bounded continuous function on `K`
that agrees with `g`. -/
theorem compactSupNorm_eq_norm_of_forall {K : Set X} {g : X → Y} (F : K →ᵇ Y)
    (hF : ∀ x : K, F x = g x) : compactSupNorm K g = ‖F‖ := by
  rw [compactSupNorm, BoundedContinuousFunction.norm_eq_iSup_norm, Set.image_eq_range]
  simp_rw [hF]
  rfl

/-- The values on `K` of a function represented by a bounded continuous function are bounded
by the compact sup norm. -/
theorem le_compactSupNorm_of_forall {K : Set X} {g : X → Y} (F : K →ᵇ Y)
    (hF : ∀ x : K, F x = g x) {x : X} (hx : x ∈ K) : ‖g x‖ ≤ compactSupNorm K g := by
  rw [compactSupNorm_eq_norm_of_forall F hF, ← hF ⟨x, hx⟩]
  exact BoundedContinuousFunction.norm_coe_le_norm F ⟨x, hx⟩

end SupNormBCF

/-! ### The ridge atoms as a measurable map into `C(K)` -/

section Atoms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {K : Set H}

/-- The complexified activation `t ↦ (β t : ℂ)` is `L`-Lipschitz when `β` is. -/
theorem lipschitzWith_ofReal_comp {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) :
    LipschitzWith L fun t => (β t : ℂ) := by
  have h := Complex.isometry_ofReal.lipschitz.comp hβ
  rwa [one_mul] at h

/-- The complexified activation `t ↦ (β t : ℂ)` is continuous when `β` is Lipschitz. -/
theorem continuous_ofReal_comp {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) :
    Continuous fun t => (β t : ℂ) :=
  (lipschitzWith_ofReal_comp hβ).continuous

/-- The ridge atom `x ↦ β(⟪a, x⟫ + c)` of a continuous complex activation, restricted to the
compact set `K`, as a bounded continuous function on `K`; a real activation `β` is used as
`fun t => (β t : ℂ)`. -/
def ridgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) (θ : H × ℝ) : K →ᵇ ℂ :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  BoundedContinuousFunction.mkOfCompact ⟨fun x : K => β (⟪θ.1, (x : H)⟫ + θ.2), by fun_prop⟩

theorem ridgeAtom_apply (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) (θ : H × ℝ)
    (x : K) : ridgeAtom hK hβ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) :=
  rfl

/-- The norm of a ridge atom is the compact sup norm of the ridge. -/
theorem norm_ridgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) (θ : H × ℝ) :
    ‖ridgeAtom hK hβ θ‖ = compactSupNorm K fun x => β (⟪θ.1, x⟫ + θ.2) :=
  (compactSupNorm_eq_norm_of_forall (ridgeAtom hK hβ θ) fun _ => rfl).symm

/-- The ridge atoms depend continuously on the parameter. -/
theorem continuous_ridgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) :
    Continuous (ridgeAtom hK hβ) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C((H × ℝ) × K, ℂ) := ⟨fun q => β (⟪q.1.1, (q.2 : H)⟫ + q.1.2), by fun_prop⟩
  have hF : ridgeAtom hK hβ = fun θ =>
      ContinuousMap.isometryEquivBoundedOfCompact K ℂ (ContinuousMap.curry F θ) := rfl
  rw [hF]
  exact (ContinuousMap.isometryEquivBoundedOfCompact K ℂ).continuous.comp
    (ContinuousMap.curry F).continuous

omit [InnerProductSpace ℝ H] in
/-- `C(K)` is second countable for compact `K ⊆ H`. -/
theorem secondCountableTopology_boundedContinuousFunction (hK : IsCompact K) :
    SecondCountableTopology (K →ᵇ ℂ) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : SecondCountableTopology K := EMetric.secondCountable_of_sigmaCompact K
  haveI : LocallyCompactSpace K := inferInstance
  haveI : SecondCountableTopology C(K, ℂ) := ContinuousMap.instSecondCountableTopology
  exact (ContinuousMap.isometryEquivBoundedOfCompact K ℂ).toHomeomorph.symm.secondCountableTopology

/-- The norm of a ridge atom on `K ⊆ closedBall 0 r`: the Lipschitz envelope. -/
theorem norm_ridgeAtom_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    {r : ℝ} (hr : ∀ x ∈ K, ‖x‖ ≤ r) (θ : H × ℝ) :
    ‖ridgeAtom hK (continuous_ofReal_comp hβ) θ‖ ≤ (|β 0| + L * max r 1) * (1 + ‖θ.1‖ + |θ.2|) := by
  have hC : 0 ≤ |β 0| + L * max r 1 :=
    add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg (zero_le_one.trans (le_max_right r 1)))
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (by positivity))).mpr fun x => ?_
  rw [ridgeAtom_apply]
  refine (norm_ridge_le (lipschitzWith_ofReal_comp hβ) (x : H) θ).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact hr x x.2

end Atoms

section AtomsMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] {K : Set H} {Ω : Type*} [MeasurableSpace Ω]

/-- `C(K)` is separable for compact `K`, so the continuous atom map is strongly measurable. -/
theorem stronglyMeasurable_ridgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) :
    StronglyMeasurable (ridgeAtom hK hβ) := by
  haveI := secondCountableTopology_boundedContinuousFunction hK
  exact (continuous_ridgeAtom hK hβ).stronglyMeasurable

/-- The `C(K)`-valued atoms `ω ↦ h(ω) β(⟪a(ω), ·⟫ + c(ω))` of a sampled network with
`|h| ≤ 1` are Bochner integrable under the second-moment condition. -/
theorem integrable_smul_ridgeAtom (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure Ω) [IsProbabilityMeasure p] {π : Ω → H × ℝ}
    (hπ : Measurable π) {h : Ω → ℂ} (hh : AEStronglyMeasurable h p) (hh1 : ∀ᵐ ω ∂p, ‖h ω‖ ≤ 1)
    (hM : Integrable (fun ω => ‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) p) :
    Integrable (fun ω => h ω • ridgeAtom hK (continuous_ofReal_comp hβ) (π ω)) p := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hmeas :
      AEStronglyMeasurable (fun ω => h ω • ridgeAtom hK (continuous_ofReal_comp hβ) (π ω)) p :=
    hh.smul ((stronglyMeasurable_ridgeAtom hK (continuous_ofReal_comp hβ)).comp_measurable
      hπ).aestronglyMeasurable
  set C : ℝ := |β 0| + L * max r 1 with hC
  have hC0 : 0 ≤ C :=
    add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg (zero_le_one.trans (le_max_right r 1)))
  have hbound : Integrable (fun ω => C * (3 + (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2))) p :=
    ((integrable_const 3).add hM).const_mul C
  refine hbound.mono' hmeas ?_
  filter_upwards [hh1] with ω hω
  rw [norm_smul]
  calc ‖h ω‖ * ‖ridgeAtom hK (continuous_ofReal_comp hβ) (π ω)‖
      ≤ 1 * (C * (1 + ‖(π ω).1‖ + |(π ω).2|)) :=
        mul_le_mul hω (norm_ridgeAtom_le hK hβ hr _) (norm_nonneg _) zero_le_one
    _ ≤ C * (3 + (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2)) := by
        rw [one_mul]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        nlinarith [sq_nonneg (‖(π ω).1‖ - 1), sq_nonneg (|(π ω).2| - 1)]

end AtomsMeasurable

/-! ### The dimension-free Barron bound in `C(K)` -/

section Barron

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {K : Set H}

/-- The uniform weights on the sign vectors sum to one. -/
theorem sum_signs_inv_pow_two (N : ℕ) : ∑ _σ : Signs N, (2 ^ N : ℝ)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Signs.card, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

/-- Splitting the complex phases: with `ψ = β − β(0)`,
`‖∑_j σ_j h_j β(t_j)‖ ≤ |β(0)| ‖∑_j σ_j h_j‖ + |∑_j σ_j Re(h_j) ψ(t_j)| +
|∑_j σ_j Im(h_j) ψ(t_j)|`. -/
theorem norm_sum_smul_mul_ofReal_le {N : ℕ} (β : ℝ → ℝ) (σ : Fin N → ℝ) (h : Fin N → ℂ)
    (t : Fin N → ℝ) :
    ‖∑ j, σ j • (h j * (β (t j) : ℂ))‖ ≤
      |β 0| * ‖∑ j, σ j • h j‖ + |∑ j, σ j * ((h j).re * (β (t j) - β 0))| +
        |∑ j, σ j * ((h j).im * (β (t j) - β 0))| := by
  have hsplit : ∑ j, σ j • (h j * (β (t j) : ℂ)) =
      β 0 • ∑ j, σ j • h j + ∑ j, σ j • (h j * ((β (t j) - β 0 : ℝ) : ℂ)) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.real_smul, Complex.ofReal_sub]
    ring
  set Z := ∑ j, σ j • (h j * ((β (t j) - β 0 : ℝ) : ℂ)) with hZ
  have hre : Z.re = ∑ j, σ j * ((h j).re * (β (t j) - β 0)) := by
    rw [hZ, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.real_smul, Complex.mul_re]
  have him : Z.im = ∑ j, σ j * ((h j).im * (β (t j) - β 0)) := by
    rw [hZ, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.real_smul, Complex.mul_im]
  calc ‖∑ j, σ j • (h j * (β (t j) : ℂ))‖ = ‖β 0 • ∑ j, σ j • h j + Z‖ := by rw [hsplit]
    _ ≤ ‖β 0 • ∑ j, σ j • h j‖ + ‖Z‖ := norm_add_le _ _
    _ ≤ |β 0| * ‖∑ j, σ j • h j‖ + (|Z.re| + |Z.im|) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add le_rfl (Complex.norm_le_abs_re_add_abs_im Z)
    _ = _ := by rw [hre, him, add_assoc]

/-- `|⟪A, x⟫ + C| ≤ √(‖A‖² + C²) √(‖x‖² + 1)` (Cauchy–Schwarz in `H ⊕ ℝ`). -/
theorem abs_inner_add_le_sqrt (A x : H) (C : ℝ) :
    |⟪A, x⟫ + C| ≤ Real.sqrt (‖A‖ ^ 2 + C ^ 2) * Real.sqrt (‖x‖ ^ 2 + 1) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt ?_
  have h1 : |⟪A, x⟫ + C| ≤ ‖A‖ * ‖x‖ + |C| :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm A x) le_rfl)
  have h2 : (⟪A, x⟫ + C) ^ 2 ≤ (‖A‖ * ‖x‖ + |C|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine h2.trans ?_
  nlinarith [sq_nonneg (‖A‖ - |C| * ‖x‖), sq_abs C, norm_nonneg A, norm_nonneg x, abs_nonneg C]

omit [InnerProductSpace ℝ H] in
theorem le_compactRadius (hK : IsCompact K) {x : H} (hx : x ∈ K) :
    Real.sqrt (‖x‖ ^ 2 + 1) ≤ compactRadius K :=
  le_csSup (hK.image (by fun_prop : Continuous fun x : H => Real.sqrt (‖x‖ ^ 2 + 1))).bddAbove
    ⟨x, hx, rfl⟩

omit [InnerProductSpace ℝ H] in
theorem compactRadius_nonneg (K : Set H) : 0 ≤ compactRadius K :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ Real.sqrt_nonneg _

/-- The envelope of a ridge atom with bounded parameters: for `‖a‖² + c² ≤ B²` and `B ≥ 0`,
`‖β(⟪a, ·⟫ + c)‖_{C(K)} ≤ |β(0)| + Lip(β) R_K B`. -/
theorem norm_ridgeAtom_le_of_sq_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {B : ℝ} (hB0 : 0 ≤ B) {θ : H × ℝ}
    (hθ : ‖θ.1‖ ^ 2 + |θ.2| ^ 2 ≤ B ^ 2) :
    ‖ridgeAtom hK (continuous_ofReal_comp hβ) θ‖ ≤ |β 0| + L * compactRadius K * B := by
  have hR : 0 ≤ compactRadius K := compactRadius_nonneg K
  have hC : 0 ≤ |β 0| + L * compactRadius K * B := by positivity
  refine (BoundedContinuousFunction.norm_le hC).mpr fun x => ?_
  rw [ridgeAtom_apply, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |β (⟪θ.1, (x : H)⟫ + θ.2)| ≤ |β 0| + L * |⟪θ.1, (x : H)⟫ + θ.2| := by
    have := hβ.dist_le_mul (⟪θ.1, (x : H)⟫ + θ.2) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (β (⟪θ.1, (x : H)⟫ + θ.2)) (β 0)]
  have hsq : Real.sqrt (‖θ.1‖ ^ 2 + θ.2 ^ 2) ≤ B := by
    rw [← sq_abs θ.2]
    exact (Real.sqrt_le_sqrt hθ).trans_eq (Real.sqrt_sq hB0)
  have h2 : |⟪θ.1, (x : H)⟫ + θ.2| ≤ B * compactRadius K :=
    (abs_inner_add_le_sqrt θ.1 x θ.2).trans
      (mul_le_mul hsq (le_compactRadius hK x.2) (Real.sqrt_nonneg _) hB0)
  calc |β (⟪θ.1, (x : H)⟫ + θ.2)| ≤ |β 0| + L * |⟪θ.1, (x : H)⟫ + θ.2| := h1
    _ ≤ |β 0| + L * (B * compactRadius K) := by gcongr
    _ = |β 0| + L * compactRadius K * B := by ring

/-- The linear Rademacher process on `K`:
`sup_{x ∈ K} |∑_j σ_j (⟪a_j, x⟫ + c_j)| ≤ √(‖∑_j σ_j a_j‖² + (∑_j σ_j c_j)²) R_K`. -/
theorem sSup_abs_sum_mul_ridge_le (hK : IsCompact K) {N : ℕ} (σ : Fin N → ℝ)
    (θ : Fin N → H × ℝ) :
    sSup ((fun x => |∑ j, σ j * (⟪(θ j).1, x⟫ + (θ j).2)|) '' K) ≤
      Real.sqrt (‖∑ j, σ j • (θ j).1‖ ^ 2 + (∑ j, σ j * (θ j).2) ^ 2) * compactRadius K := by
  refine Real.sSup_le ?_ (mul_nonneg (Real.sqrt_nonneg _) (compactRadius_nonneg K))
  rintro _ ⟨x, hx, rfl⟩
  show |∑ j, σ j * (⟪(θ j).1, x⟫ + (θ j).2)| ≤ _
  have hlin : ∑ j, σ j * (⟪(θ j).1, x⟫ + (θ j).2) =
      ⟪∑ j, σ j • (θ j).1, x⟫ + ∑ j, σ j * (θ j).2 := by
    rw [sum_inner, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, mul_add]
  rw [hlin]
  exact (abs_inner_add_le_sqrt _ x _).trans
    (mul_le_mul_of_nonneg_left (le_compactRadius hK hx) (Real.sqrt_nonneg _))

/-- Symmetrized atoms on `K`, before averaging over the signs: with `|h_j| ≤ 1`,
`∑_σ ‖∑_j σ_j h_j β(⟪a_j, ·⟫ + c_j)‖_{C(K)} ≤ |β(0)| ∑_σ ‖∑_j σ_j h_j‖ +
4 Lip(β) ∑_σ sup_{x ∈ K} |∑_j σ_j (⟪a_j, x⟫ + c_j)|` (the contraction principle applied to
the real and imaginary parts). -/
theorem sum_compactSupNorm_ridge_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {N : ℕ} (θ : Fin N → H × ℝ) (h : Fin N → ℂ)
    (hh : ∀ j, ‖h j‖ ≤ 1) :
    ∑ σ : Signs N, compactSupNorm K
        (fun x => ∑ j, signVector σ j • (h j * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ))) ≤
      |β 0| * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖ +
        4 * L * ∑ σ : Signs N,
          sSup ((fun x => |∑ j, signVector σ j * (⟪(θ j).1, x⟫ + (θ j).2)|) '' K) := by
  have hβc : Continuous β := hβ.continuous
  have hlip : ∀ x y, |β x - β y| ≤ L * |x - y| := fun x y => by
    have := hβ.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hφre : ∀ j x y, |(h j).re * (β x - β 0) - (h j).re * (β y - β 0)| ≤ L * |x - y| := by
    intro j x y
    rw [show (h j).re * (β x - β 0) - (h j).re * (β y - β 0) = (h j).re * (β x - β y) by ring,
      abs_mul]
    calc |(h j).re| * |β x - β y| ≤ 1 * (L * |x - y|) :=
          mul_le_mul ((Complex.abs_re_le_norm _).trans (hh j)) (hlip x y) (abs_nonneg _)
            zero_le_one
      _ = L * |x - y| := one_mul _
  have hφim : ∀ j x y, |(h j).im * (β x - β 0) - (h j).im * (β y - β 0)| ≤ L * |x - y| := by
    intro j x y
    rw [show (h j).im * (β x - β 0) - (h j).im * (β y - β 0) = (h j).im * (β x - β y) by ring,
      abs_mul]
    calc |(h j).im| * |β x - β y| ≤ 1 * (L * |x - y|) :=
          mul_le_mul ((Complex.abs_im_le_norm _).trans (hh j)) (hlip x y) (abs_nonneg _)
            zero_le_one
      _ = L * |x - y| := one_mul _
  have hbddu : ∀ j, BddAbove ((fun x => |⟪(θ j).1, x⟫ + (θ j).2|) '' K) := fun j =>
    (hK.image (by fun_prop)).bddAbove
  have hcre := sum_sSup_abs_contraction K (fun j x => ⟪(θ j).1, x⟫ + (θ j).2)
    (fun j t => (h j).re * (β t - β 0)) L.coe_nonneg (fun j => by simp) hφre hbddu
  have hcim := sum_sSup_abs_contraction K (fun j x => ⟪(θ j).1, x⟫ + (θ j).2)
    (fun j t => (h j).im * (β t - β 0)) L.coe_nonneg (fun j => by simp) hφim hbddu
  have hpt : ∀ σ : Signs N,
      compactSupNorm K (fun x => ∑ j, signVector σ j • (h j * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ))) ≤
        |β 0| * ‖∑ j, signVector σ j • h j‖ +
          sSup ((fun x => |∑ j, signVector σ j * ((h j).re * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|)
            '' K) +
          sSup ((fun x => |∑ j, signVector σ j * ((h j).im * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|)
            '' K) := by
    intro σ
    have hbre : BddAbove ((fun x =>
        |∑ j, signVector σ j * ((h j).re * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|) '' K) :=
      (hK.image (by fun_prop)).bddAbove
    have hbim : BddAbove ((fun x =>
        |∑ j, signVector σ j * ((h j).im * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|) '' K) :=
      (hK.image (by fun_prop)).bddAbove
    refine compactSupNorm_le (add_nonneg (add_nonneg (by positivity)
      (Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _))
      (Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _)) fun x hx => ?_
    refine (norm_sum_smul_mul_ofReal_le β (signVector σ) h
      fun j => ⟪(θ j).1, x⟫ + (θ j).2).trans ?_
    exact add_le_add (add_le_add le_rfl (le_csSup hbre ⟨x, hx, rfl⟩)) (le_csSup hbim ⟨x, hx, rfl⟩)
  calc ∑ σ : Signs N, compactSupNorm K
        (fun x => ∑ j, signVector σ j • (h j * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ)))
      ≤ ∑ σ : Signs N, (|β 0| * ‖∑ j, signVector σ j • h j‖ +
          sSup ((fun x => |∑ j, signVector σ j * ((h j).re * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|)
            '' K) +
          sSup ((fun x => |∑ j, signVector σ j * ((h j).im * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|)
            '' K)) := Finset.sum_le_sum fun σ _ => hpt σ
    _ = |β 0| * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖ +
          ∑ σ : Signs N, sSup ((fun x =>
            |∑ j, signVector σ j * ((h j).re * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|) '' K) +
          ∑ σ : Signs N, sSup ((fun x =>
            |∑ j, signVector σ j * ((h j).im * (β (⟪(θ j).1, x⟫ + (θ j).2) - β 0))|) '' K) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ |β 0| * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖ +
          2 * L * ∑ σ : Signs N,
            sSup ((fun x => |∑ j, signVector σ j * (⟪(θ j).1, x⟫ + (θ j).2)|) '' K) +
          2 * L * ∑ σ : Signs N,
            sSup ((fun x => |∑ j, signVector σ j * (⟪(θ j).1, x⟫ + (θ j).2)|) '' K) :=
        add_le_add (add_le_add le_rfl hcre) hcim
    _ = _ := by ring

/-- The Hilbert-space Rademacher average: `2⁻ᴺ ∑_σ ‖∑_j σ_j v_j‖ ≤ √(∑_j ‖v_j‖²)`. -/
theorem inv_pow_two_mul_sum_norm_sum_signVector_smul_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (v : Fin N → E) :
    (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, ‖∑ j, signVector σ j • v j‖ ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
  have h := Finset.sum_mul_sqrt_le_sqrt_sum (Finset.univ : Finset (Signs N))
    (w := fun _ => (2 ^ N : ℝ)⁻¹) (y := fun σ => ‖∑ j, signVector σ j • v j‖ ^ 2)
    (fun _ _ => by positivity) (sum_signs_inv_pow_two N) (fun _ _ => by positivity)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  rw [Finset.mul_sum]
  refine h.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, sum_norm_sq_sum_signVector_smul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- The Rademacher average of the linear process:
`2⁻ᴺ ∑_σ √(‖∑_j σ_j a_j‖² + (∑_j σ_j c_j)²) ≤ √(∑_j (‖a_j‖² + c_j²))`. -/
theorem inv_pow_two_mul_sum_sqrt_le {N : ℕ} (θ : Fin N → H × ℝ) :
    (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        Real.sqrt (‖∑ j, signVector σ j • (θ j).1‖ ^ 2 + (∑ j, signVector σ j * (θ j).2) ^ 2) ≤
      Real.sqrt (∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2)) := by
  have h := Finset.sum_mul_sqrt_le_sqrt_sum (Finset.univ : Finset (Signs N))
    (w := fun _ => (2 ^ N : ℝ)⁻¹)
    (y := fun σ => ‖∑ j, signVector σ j • (θ j).1‖ ^ 2 + (∑ j, signVector σ j * (θ j).2) ^ 2)
    (fun _ _ => by positivity) (sum_signs_inv_pow_two N) (fun _ _ => by positivity)
  rw [Finset.mul_sum]
  refine h.trans (Real.sqrt_le_sqrt (le_of_eq ?_))
  have h2 : ∑ σ : Signs N, (∑ j, signVector σ j * (θ j).2) ^ 2 = 2 ^ N * ∑ j, |(θ j).2| ^ 2 := by
    have := sum_norm_sq_sum_signVector_smul (E := ℝ) fun j => (θ j).2
    simpa [Real.norm_eq_abs, sq_abs, smul_eq_mul] using this
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_norm_sq_sum_signVector_smul, h2, ← mul_add,
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul, Finset.sum_add_distrib]

/-- The Rademacher average of the `C(K)`-valued atoms, for a fixed sample with `|h_j| ≤ 1`:
`2⁻ᴺ ∑_σ ‖∑_j σ_j h_j β(⟪a_j, ·⟫ + c_j)‖_{C(K)} ≤
|β(0)| √N + 4 Lip(β) R_K √(∑_j (‖a_j‖² + c_j²))`. -/
theorem inv_pow_two_mul_sum_norm_sum_signVector_smul_ridgeAtom_le (hK : IsCompact K)
    {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) {N : ℕ} (θ : Fin N → H × ℝ) (h : Fin N → ℂ)
    (hh : ∀ j, ‖h j‖ ≤ 1) :
    (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        ‖∑ j, signVector σ j • (h j • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j))‖ ≤
      |β 0| * Real.sqrt N +
        4 * L * compactRadius K * Real.sqrt (∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2)) := by
  have hnorm : ∀ σ : Signs N,
      ‖∑ j, signVector σ j • (h j • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j))‖ =
      compactSupNorm K
        (fun x => ∑ j, signVector σ j • (h j * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ))) := by
    intro σ
    refine (compactSupNorm_eq_norm_of_forall _ fun x => ?_).symm
    change (BoundedContinuousFunction.evalCLM ℂ x) (∑ j, _) = _
    rw [map_sum]
    rfl
  have hR : 0 ≤ compactRadius K := compactRadius_nonneg K
  have hsq : Real.sqrt (∑ j, ‖h j‖ ^ 2) ≤ Real.sqrt N := by
    refine Real.sqrt_le_sqrt
      ((Finset.sum_le_sum fun j _ => pow_le_one₀ (norm_nonneg _) (hh j)).trans (le_of_eq ?_))
    simp
  calc (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        ‖∑ j, signVector σ j • (h j • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j))‖
      = (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, compactSupNorm K
          (fun x => ∑ j, signVector σ j • (h j * (β (⟪(θ j).1, x⟫ + (θ j).2) : ℂ))) := by
        simp_rw [hnorm]
    _ ≤ (2 ^ N : ℝ)⁻¹ * (|β 0| * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖ +
          4 * L * ∑ σ : Signs N,
            sSup ((fun x => |∑ j, signVector σ j * (⟪(θ j).1, x⟫ + (θ j).2)|) '' K)) :=
        mul_le_mul_of_nonneg_left (sum_compactSupNorm_ridge_le hK hβ θ h hh) (by positivity)
    _ ≤ (2 ^ N : ℝ)⁻¹ * (|β 0| * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖ +
          4 * L * ∑ σ : Signs N, (Real.sqrt (‖∑ j, signVector σ j • (θ j).1‖ ^ 2 +
            (∑ j, signVector σ j * (θ j).2) ^ 2) * compactRadius K)) := by
        gcongr with σ _
        exact sSup_abs_sum_mul_ridge_le hK (signVector σ) θ
    _ = |β 0| * ((2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, ‖∑ j, signVector σ j • h j‖) +
          4 * L * compactRadius K * ((2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
            Real.sqrt (‖∑ j, signVector σ j • (θ j).1‖ ^ 2 +
              (∑ j, signVector σ j * (θ j).2) ^ 2)) := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ |β 0| * Real.sqrt (∑ j, ‖h j‖ ^ 2) +
          4 * L * compactRadius K * Real.sqrt (∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (inv_pow_two_mul_sum_norm_sum_signVector_smul_le h)
            (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (inv_pow_two_mul_sum_sqrt_le θ) (by positivity))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)) le_rfl


variable [MeasurableSpace H] [BorelSpace H] {Ω : Type*} [MeasurableSpace Ω]

/-- A Lipschitz ridge is integrable against a probability measure with finite second
moment. -/
theorem integrable_ridge_of_secondMoment (p : Measure Ω) [IsProbabilityMeasure p]
    {π : Ω → H × ℝ} (hπ : Measurable π) {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (hM : Integrable (fun ω => ‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) p) (x : H) :
    Integrable (fun ω => β (⟪(π ω).1, x⟫ + (π ω).2)) p := by
  have hC : 0 ≤ ‖β 0‖ + L * max ‖x‖ 1 :=
    add_nonneg (norm_nonneg _) (mul_nonneg L.coe_nonneg (zero_le_one.trans (le_max_right _ _)))
  have hc : Continuous fun θ : H × ℝ => β (⟪θ.1, x⟫ + θ.2) := hβ.continuous.comp (by fun_prop)
  refine (((integrable_const 3).add hM).const_mul (‖β 0‖ + L * max ‖x‖ 1)).mono'
    (hc.measurable.comp hπ).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  refine (norm_ridge_le hβ x (π ω)).trans (mul_le_mul_of_nonneg_left ?_ hC)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖(π ω).1‖ - 1), sq_nonneg (|(π ω).2| - 1)]

/-- **The dimension-free Barron bound in `C(K)`.**  For a probability measure `p` on `Ω`, a
measurable parameter map `π : Ω → H × ℝ` with finite second moment, phases `|h| ≤ 1`, and a
Lipschitz `β`, the empirical mean of `N` independent copies of the `C(K)`-valued atom
`h(ω) β(⟪π(ω)_1, ·⟫ + π(ω)_2)` satisfies
`𝔼 ‖∑_j Φ(ω_j) − N ∫ Φ dp‖_{C(K)} ≤ 8 √N (|β(0)| + Lip(β) R_K M₂)`. -/
theorem integral_norm_sum_smul_ridgeAtom_sub_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure Ω) [IsProbabilityMeasure p] {π : Ω → H × ℝ}
    (hπ : Measurable π) {h : Ω → ℂ} (hh : AEStronglyMeasurable h p) (hh1 : ∀ᵐ ω ∂p, ‖h ω‖ ≤ 1)
    (hM : Integrable (fun ω => ‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) p) (N : ℕ) :
    ∫ ω, ‖∑ j, h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)) -
          (N : ℝ) • ∫ ω', h ω' • ridgeAtom hK (continuous_ofReal_comp hβ) (π ω') ∂p‖
        ∂sampleLaw N p ≤
      8 * Real.sqrt N * (|β 0| + L * compactRadius K *
        Real.sqrt (∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p)) := by
  unfold sampleLaw
  have hΦ : Integrable (fun ω => h ω • ridgeAtom hK (continuous_ofReal_comp hβ) (π ω)) p :=
    integrable_smul_ridgeAtom hK hβ p hπ hh hh1 hM
  have hsym := integral_norm_sum_sub_le p hΦ (signVector (N := N)) (fun _ => (2 ^ N : ℝ)⁻¹)
    (fun _ => by positivity) (sum_signs_inv_pow_two N) fun σ j => signVector_eq_one_or_neg_one σ j
  have hΦj : ∀ j, Integrable
      (fun ω : Fin N → Ω => h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))
      (Measure.pi fun _ : Fin N => p) :=
    fun j => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hΦ
  have hint : ∀ σ : Signs N, Integrable (fun ω : Fin N → Ω =>
      ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖)
      (Measure.pi fun _ : Fin N => p) :=
    fun σ => (integrable_finsetSum Finset.univ
      (f := fun j (ω : Fin N → Ω) =>
        signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j))))
      fun j _ => (hΦj j).smul (signVector σ j)).norm
  have hqj : Integrable (fun ω : Fin N → Ω => ∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2))
      (Measure.pi fun _ : Fin N => p) :=
    integrable_finsetSum Finset.univ
      (f := fun j (ω : Fin N → Ω) => ‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2)
      fun j _ => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hM
  have hsqrt : Integrable (fun ω : Fin N → Ω =>
      Real.sqrt (∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2))) (Measure.pi fun _ : Fin N => p) :=
    hqj.sqrt
  have hae : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => p),
      (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
          ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖ ≤
        |β 0| * Real.sqrt N + 4 * L * compactRadius K *
          Real.sqrt (∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2)) := by
    filter_upwards [ae_sampleLaw_forall (N := N) hh1] with ω hω
    exact inv_pow_two_mul_sum_norm_sum_signVector_smul_ridgeAtom_le hK hβ (fun j => π (ω j))
      (fun j => h (ω j)) hω
  have hR : 0 ≤ compactRadius K := compactRadius_nonneg K
  have hint2 : ∫ ω, (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖
        ∂(Measure.pi fun _ : Fin N => p) ≤
      |β 0| * Real.sqrt N + 4 * L * compactRadius K *
        Real.sqrt (N * ∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p) := by
    calc ∫ ω, (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
          ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖
          ∂(Measure.pi fun _ : Fin N => p)
        ≤ ∫ ω, (|β 0| * Real.sqrt N + 4 * L * compactRadius K *
            Real.sqrt (∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2)))
            ∂(Measure.pi fun _ : Fin N => p) :=
          integral_mono_ae ((integrable_finsetSum Finset.univ fun σ _ => hint σ).const_mul _)
            ((integrable_const _).add (hsqrt.const_mul _)) hae
      _ = |β 0| * Real.sqrt N + 4 * L * compactRadius K *
            ∫ ω, Real.sqrt (∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2))
              ∂(Measure.pi fun _ : Fin N => p) := by
          rw [integral_add (integrable_const _) (hsqrt.const_mul _), integral_const, probReal_univ,
            one_smul, integral_const_mul]
      _ ≤ |β 0| * Real.sqrt N + 4 * L * compactRadius K *
            Real.sqrt (∫ ω, ∑ j, (‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2)
              ∂(Measure.pi fun _ : Fin N => p)) := by
          gcongr
          exact integral_sqrt_le_sqrt_integral hqj
            (Eventually.of_forall fun ω => Finset.sum_nonneg fun j _ => by positivity)
      _ = |β 0| * Real.sqrt N + 4 * L * compactRadius K *
            Real.sqrt (N * ∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p) := by
          rw [integral_finsetSum Finset.univ
            (f := fun j (ω : Fin N → Ω) => ‖(π (ω j)).1‖ ^ 2 + |(π (ω j)).2| ^ 2)
            fun j _ => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hM]
          simp_rw [integral_eval_pi p hM.aestronglyMeasurable]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ∫ ω, ‖∑ j, h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)) -
          (N : ℝ) • ∫ ω', h ω' • ridgeAtom hK (continuous_ofReal_comp hβ) (π ω') ∂p‖
          ∂(Measure.pi fun _ : Fin N => p)
      ≤ 2 * ∑ σ : Signs N, (2 ^ N : ℝ)⁻¹ *
          ∫ ω,
            ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖
            ∂(Measure.pi fun _ : Fin N => p) := hsym
    _ = 2 * ∫ ω, (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
          ‖∑ j, signVector σ j • (h (ω j) • ridgeAtom hK (continuous_ofReal_comp hβ) (π (ω j)))‖
          ∂(Measure.pi fun _ : Fin N => p) := by
        rw [integral_const_mul, integral_finsetSum Finset.univ fun σ _ => hint σ, ← Finset.mul_sum]
    _ ≤ 2 * (|β 0| * Real.sqrt N + 4 * L * compactRadius K *
          Real.sqrt (N * ∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p)) :=
        mul_le_mul_of_nonneg_left hint2 (by norm_num)
    _ = 2 * Real.sqrt N * |β 0| + 8 * Real.sqrt N *
          (L * compactRadius K * Real.sqrt (∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
        ring
    _ ≤ 8 * Real.sqrt N * (|β 0| + L * compactRadius K *
          Real.sqrt (∫ ω, (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) ∂p)) := by
        have h0 : 0 ≤ Real.sqrt N * |β 0| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
        nlinarith [h0]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Evaluation of the scaled, centred sum of the atoms `Φ(ω) = β(⟪π(ω)_1, ·⟫ + π(ω)_2) h(ω)`
at a point of `K`: it is the sampled-network error. -/
theorem smul_sum_sub_apply (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → ℂ) {Φ : Ω → (K →ᵇ ℂ)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) * h ω) (hint : Integrable Φ p)
    (V : ℝ) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) (x : K) :
    ((V / N : ℝ) • (∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p)) x =
      ∑ j, β (⟪(π (ω j)).1, (x : H)⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
        V • ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) • h ω' ∂p := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have heval : (∫ ω', Φ ω' ∂p) x = ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) * h ω' ∂p := by
    change (BoundedContinuousFunction.evalCLM ℂ x) (∫ ω', Φ ω' ∂p) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    exact integral_congr_ae (Eventually.of_forall fun ω' => hΦ ω' x)
  change (V / N : ℝ) • ((BoundedContinuousFunction.evalCLM ℂ x) (∑ j, Φ (ω j)) -
    (N : ℝ) • (∫ ω', Φ ω' ∂p) x) = _
  rw [map_sum, heval, smul_sub, smul_smul, div_mul_cancel₀ V hN', Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change (V / N : ℝ) • Φ (ω j) x = _
  rw [hΦ, Complex.real_smul]
  simp only [smul_eq_mul]
  ring

omit [MeasurableSpace H] [BorelSpace H] in
/-- The sampled-network error on `K` is `V/N` times the `C(K)`-norm of the centred sum of the
atoms `Φ(ω) = β(⟪π(ω)_1, ·⟫ + π(ω)_2) h(ω)`. -/
theorem compactSupNorm_sampled_sub_eq (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → ℂ) {Φ : Ω → (K →ᵇ ℂ)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) * h ω) (hint : Integrable Φ p)
    {V : ℝ} (hV : 0 ≤ V) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) :
    compactSupNorm K (fun x =>
        ∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
          V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p) =
      V / N * ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖ := by
  conv_rhs => rw [← abs_of_nonneg (div_nonneg hV (Nat.cast_nonneg N)), ← Real.norm_eq_abs,
    ← norm_smul]
  exact compactSupNorm_eq_norm_of_forall _ (smul_sum_sub_apply p β π h hΦ hint V hN ω)

omit [MeasurableSpace H] [BorelSpace H] in
/-- The sampled-network error at a point of `K` is bounded by its compact sup norm. -/
theorem norm_sampled_sub_le_compactSupNorm (p : Measure Ω) [IsProbabilityMeasure p]
    (β : ℝ → ℂ) (π : Ω → H × ℝ) (h : Ω → ℂ) {Φ : Ω → (K →ᵇ ℂ)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) * h ω) (hint : Integrable Φ p)
    (V : ℝ) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) {x : H} (hx : x ∈ K) :
    ‖∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
        V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p‖ ≤
      compactSupNorm K (fun x =>
        ∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
          V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p) :=
  le_compactSupNorm_of_forall (F := (V / N : ℝ) • (∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p))
    (g := fun x : H => ∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
      V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p)
    (smul_sum_sub_apply p β π h hΦ hint V hN ω) hx

omit [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The centred sum of the atoms is integrable (used for the deterministic realization). -/
theorem integrable_norm_sum_sub (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → (K →ᵇ ℂ)}
    (hint : Integrable Φ p) (N : ℕ) :
    Integrable (fun ω : Fin N → Ω => ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖)
      (sampleLaw N p) :=
  ((integrable_finsetSum Finset.univ (f := fun j (ω : Fin N → Ω) => Φ (ω j)) fun j _ =>
    (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hint).sub
    (integrable_const _)).norm

omit [MeasurableSpace H] [BorelSpace H] in
/-- The ridge `β(⟪a, ·⟫ + c)` is integrable when the atoms `β(⟪a, ·⟫ + c) h` are, for
phases of modulus one. -/
theorem integrable_ridge_of_integrable_atom (p : Measure Ω) (β : ℝ → ℂ) (π : Ω → H × ℝ)
    {h : Ω → ℂ} (hh : AEStronglyMeasurable h p) (hh1 : ∀ᵐ ω ∂p, ‖h ω‖ = 1)
    {Φ : Ω → (K →ᵇ ℂ)} (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) * h ω)
    (hint : Integrable Φ p) (x : K) :
    Integrable (fun ω => β (⟪(π ω).1, (x : H)⟫ + (π ω).2)) p := by
  have heq : (fun ω => β (⟪(π ω).1, (x : H)⟫ + (π ω).2)) =ᵐ[p]
      fun ω => Φ ω x * (starRingEnd ℂ) (h ω) := by
    filter_upwards [hh1] with ω hω
    rw [hΦ, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]
    simp
  refine (hint.norm.mono' ?_ ?_).congr heq.symm
  · exact ((BoundedContinuousFunction.evalCLM ℂ x).continuous.comp_aestronglyMeasurable
      hint.aestronglyMeasurable).mul (Complex.continuous_conj.comp_aestronglyMeasurable hh)
  · filter_upwards [hh1] with ω hω
    rw [norm_mul, Complex.norm_conj, hω, mul_one]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] in
/-- Evaluation of the atoms `h(ω) β(⟪π(ω)_1, ·⟫ + π(ω)_2)` built from `ridgeAtom`. -/
theorem smul_ridgeAtom_apply (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β)
    (π : Ω → H × ℝ) (h : Ω → ℂ) (ω : Ω) (x : K) :
    (h ω • ridgeAtom hK hβ (π ω)) x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) * h ω := by
  simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, ridgeAtom_apply]
  ring

/-- The `C(K)`-valued atoms of the polar decomposition of a nonzero complex measure with finite
second moment are integrable. -/
theorem integrable_polar_atom (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (h0 : totalVariation Γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) :
    Integrable (fun θ => polarDensity Γ θ • ridgeAtom hK (continuous_ofReal_comp hβ) θ)
      (polarLaw Γ) := by
  haveI := isProbabilityMeasure_polarLaw Γ h0
  exact integrable_smul_ridgeAtom hK hβ (polarLaw Γ) measurable_id
    (aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0))
    ((ae_polarLaw_norm_polarDensity_eq_one Γ).mono fun θ hθ => hθ.le) hM

/-- The error of the polar sampled network on `K`, as `V/N` times the `C(K)`-norm of the
centred sum of the atoms. -/
theorem compactSupNorm_polarSampledNetwork_sub_eq (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ)) [IsFiniteMeasure Γ.variation]
    (h0 : totalVariation Γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) :
    compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) =
      polarWeight Γ / N *
        ‖∑ j, polarDensity Γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
          (N : ℝ) • ∫ θ', polarDensity Γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
            ∂polarLaw Γ‖ := by
  haveI := isProbabilityMeasure_polarLaw Γ h0
  calc compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x)
      = compactSupNorm K (fun x =>
          ∑ j, (β (⟪(id (θ j)).1, x⟫ + (id (θ j)).2) : ℂ) •
              (((polarWeight Γ / N : ℝ) : ℂ) • polarDensity Γ (θ j)) -
            polarWeight Γ • ∫ θ', (β (⟪(id θ').1, x⟫ + (id θ').2) : ℂ) • polarDensity Γ θ'
              ∂polarLaw Γ) := by
        refine compactSupNorm_congr fun x _ => ?_
        rw [integralNetwork_eq_integral_polarLaw (fun t => (β t : ℂ)) Γ h0
          (integrable_ridge_of_secondMoment (π := id) (polarLaw Γ) measurable_id
            (lipschitzWith_ofReal_comp hβ) hM x)]
        simp only [polarSampledNetwork, sampledNetwork, finiteNetwork, id]
    _ = _ := compactSupNorm_sampled_sub_eq (polarLaw Γ) (fun t => (β t : ℂ)) id (polarDensity Γ)
        (smul_ridgeAtom_apply hK (continuous_ofReal_comp hβ) id (polarDensity Γ))
        (integrable_polar_atom hK hβ Γ h0 hM) (polarWeight_nonneg Γ) hN θ

/-- The error of the polar sampled network at a point of `K` is bounded by its compact sup
norm (the error is the restriction to `K` of a bounded continuous function). -/
theorem norm_polarSampledNetwork_sub_le_compactSupNorm (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) (Γ : ComplexMeasure (H × ℝ))
    [IsFiniteMeasure Γ.variation] (h0 : totalVariation Γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) {x : H} (hx : x ∈ K) :
    ‖polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x - integralNetwork (fun t => (β t : ℂ)) Γ x‖ ≤
      compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) := by
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hΦint := integrable_polar_atom hK hβ Γ h0 hM
  refine le_compactSupNorm_of_forall (g := fun x =>
      polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x - integralNetwork (fun t => (β t : ℂ)) Γ x)
    ((polarWeight Γ / N : ℝ) •
      (∑ j, polarDensity Γ (θ j) • ridgeAtom hK (continuous_ofReal_comp hβ) (θ j) -
        (N : ℝ) • ∫ θ', polarDensity Γ θ' • ridgeAtom hK (continuous_ofReal_comp hβ) θ'
          ∂polarLaw Γ))
    (fun y => ?_) hx
  refine (smul_sum_sub_apply (polarLaw Γ) (fun t => (β t : ℂ)) id (polarDensity Γ)
    (smul_ridgeAtom_apply hK (continuous_ofReal_comp hβ) id (polarDensity Γ)) hΦint
    (polarWeight Γ) hN θ y).trans ?_
  rw [integralNetwork_eq_integral_polarLaw (fun t => (β t : ℂ)) Γ h0
    (integrable_ridge_of_secondMoment (π := id) (polarLaw Γ) measurable_id
      (lipschitzWith_ofReal_comp hβ) hM y)]
  simp only [polarSampledNetwork, sampledNetwork, finiteNetwork, id]

end Barron

/-! ### Projecting the directions inside the activation -/

section Truncation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {K : Set H}

/-- Projecting the directions inside the activation by a self-adjoint `P`:
`‖∑_j β(⟪a_j, x⟫ + c_j) v_j − ∑_j β(⟪P a_j, x⟫ + c_j) v_j‖ ≤
Lip(β) ‖x − P x‖ ∑_j ‖v_j‖ ‖a_j‖`. -/
theorem norm_finiteNetwork_sub_finiteNetwork_map_le {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) {N : ℕ} (v : Fin N → ℂ)
    (a : Fin N → H) (c : Fin N → ℝ) (x : H) :
    ‖finiteNetwork β v a c x - finiteNetwork β v (fun j => P (a j)) c x‖ ≤
      L * ‖x - P x‖ * ∑ j, ‖v j‖ * ‖a j‖ := by
  have hsym : ∀ j, ⟪P (a j), x⟫ = ⟪a j, P x⟫ := fun j =>
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP) (a j) x
  unfold finiteNetwork
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← sub_smul, norm_smul]
  have h1 : ‖β (⟪a j, x⟫ + c j) - β (⟪P (a j), x⟫ + c j)‖ ≤ L * (‖a j‖ * ‖x - P x‖) := by
    have := hβ.dist_le_mul (⟪a j, x⟫ + c j) (⟪P (a j), x⟫ + c j)
    rw [dist_eq_norm, Real.dist_eq] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    rw [hsym, show ⟪a j, x⟫ + c j - (⟪a j, P x⟫ + c j) = ⟪a j, x - P x⟫ by
      rw [inner_sub_right]; ring]
    exact abs_real_inner_le_norm _ _
  calc ‖β (⟪a j, x⟫ + c j) - β (⟪P (a j), x⟫ + c j)‖ * ‖v j‖
      ≤ L * (‖a j‖ * ‖x - P x‖) * ‖v j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = L * ‖x - P x‖ * (‖v j‖ * ‖a j‖) := by ring

/-- The sampled network with the directions projected by a self-adjoint `P` differs from the
sampled network on `K` by at most `Lip(β) sup_K ‖x − P x‖ (V/N) ∑_j ‖a_j‖`, for phases
`‖h(θ_j)‖ ≤ 1`. -/
theorem norm_sampledNetwork_sub_truncated_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) {V : ℝ} (hV : 0 ≤ V)
    {N : ℕ} (h : H × ℝ → ℂ) (θ : Fin N → H × ℝ) (hh : ∀ j, ‖h (θ j)‖ ≤ 1) {x : H}
    (hx : x ∈ K) :
    ‖sampledNetwork (fun t => (β t : ℂ)) V h θ x -
        finiteNetwork (fun t => (β t : ℂ)) (fun j => ((V / N : ℝ) : ℂ) • h (θ j))
          (fun j => P (θ j).1) (fun j => (θ j).2) x‖ ≤
      L * compactSupNorm K (fun x => x - P x) * (V / N * ∑ j, ‖(θ j).1‖) := by
  have hD : ‖x - P x‖ ≤ compactSupNorm K (fun x => x - P x) :=
    le_csSup (hK.image (by fun_prop : Continuous fun x : H => ‖x - P x‖)).bddAbove ⟨x, hx, rfl⟩
  have hVN : 0 ≤ V / N := div_nonneg hV (Nat.cast_nonneg N)
  have hv : ∀ j, ‖((V / N : ℝ) : ℂ) • h (θ j)‖ ≤ V / N := fun j => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hVN]
    exact mul_le_of_le_one_right hVN (hh j)
  have hD0 : 0 ≤ compactSupNorm K (fun x => x - P x) := compactSupNorm_nonneg _ _
  refine (norm_finiteNetwork_sub_finiteNetwork_map_le (lipschitzWith_ofReal_comp hβ) hP
    (fun j => ((V / N : ℝ) : ℂ) • h (θ j)) (fun j => (θ j).1) (fun j => (θ j).2) x).trans ?_
  calc L * ‖x - P x‖ * ∑ j, ‖((V / N : ℝ) : ℂ) • h (θ j)‖ * ‖(θ j).1‖
      ≤ L * compactSupNorm K (fun x => x - P x) * ∑ j, V / N * ‖(θ j).1‖ := by
        gcongr with j _
        exact hv j
    _ = L * compactSupNorm K (fun x => x - P x) * (V / N * ∑ j, ‖(θ j).1‖) := by
        simp only [Finset.mul_sum]

end Truncation

/-! ### The Rademacher complexity as a finite average over the sign vectors -/

section RademacherComplexity

instance instIsProbabilityMeasureRademacherMeasure (N : ℕ) :
    IsProbabilityMeasure (rademacherMeasure N) :=
  show IsProbabilityMeasure (Measure.pi fun _ : Fin N => rademacherSign) from inferInstance

theorem rademacherMeasure_eq (N : ℕ) :
    rademacherMeasure N = Measure.pi fun _ : Fin N => rademacherSign :=
  rfl

theorem ae_rademacherSign : ∀ᵐ t ∂rademacherSign, t = 1 ∨ t = -1 := by
  rw [rademacherSign]
  refine Measure.ae_smul_measure ?_ _
  rw [ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq]
  exact ⟨Filter.eventually_pure.mpr (Or.inr rfl), Filter.eventually_pure.mpr (Or.inl rfl)⟩

theorem ae_rademacherMeasure_forall (N : ℕ) :
    ∀ᵐ ε ∂rademacherMeasure N, ∀ j, ε j = 1 ∨ ε j = -1 := by
  rw [rademacherMeasure_eq]
  exact Measure.ae_pi_le_pi (Filter.eventually_pi fun _ => ae_rademacherSign)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  {K : Set H}

/-- The Rademacher complexity `𝔑_N(K; p, β)` as the uniform average over the `2ᴺ` sign
vectors of `N⁻¹ 𝔼_θ ‖∑_j σ_j Φ(θ_j)‖_{C(K)}`, for atoms `Φ(θ) = β(⟪a, ·⟫ + c) h(θ)`. -/
theorem rademacherComplexity_eq_sum_signs (N : ℕ) (p : Measure (H × ℝ))
    [IsProbabilityMeasure p] (β : ℝ → ℂ) (h : H × ℝ → ℂ) {Φ : H × ℝ → (K →ᵇ ℂ)}
    (hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) * h θ) (hint : Integrable Φ p) :
    rademacherComplexity N K p β h =
      (N : ℝ)⁻¹ * ((2 ^ N : ℝ)⁻¹ *
        ∑ σ : Signs N, ∫ θ, ‖∑ j, signVector σ j • Φ (θ j)‖ ∂sampleLaw N p) := by
  have hpt : ∀ z : (Fin N → H × ℝ) × (Fin N → ℝ),
      compactSupNorm K (fun x => (N : ℂ)⁻¹ •
        ∑ j, ((z.2 j : ℝ) : ℂ) • (β (⟪(z.1 j).1, x⟫ + (z.1 j).2) • h (z.1 j))) =
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖ := by
    intro z
    have hNinv : |(N : ℝ)⁻¹| = (N : ℝ)⁻¹ := abs_of_nonneg (by positivity)
    rw [← hNinv, ← Real.norm_eq_abs, ← norm_smul]
    refine compactSupNorm_eq_norm_of_forall _ fun x => ?_
    change (N : ℝ)⁻¹ • (BoundedContinuousFunction.evalCLM ℂ x) (∑ j, z.2 j • Φ (z.1 j)) = _
    rw [map_sum]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    change (z.2 j : ℂ) * Φ (z.1 j) x = _
    rw [hΦ]
  have hfun : (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) => compactSupNorm K (fun x => (N : ℂ)⁻¹ •
        ∑ j, ((z.2 j : ℝ) : ℂ) • (β (⟪(z.1 j).1, x⟫ + (z.1 j).2) • h (z.1 j)))) =
      fun z => (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖ := funext hpt
  have hΦj : ∀ j, Integrable (fun θ : Fin N → H × ℝ => Φ (θ j)) (sampleLaw N p) := fun j =>
    (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hint
  have hfst : MeasurePreserving Prod.fst ((sampleLaw N p).prod (rademacherMeasure N))
      (sampleLaw N p) := ⟨measurable_fst, Measure.fst_prod⟩
  have hsnd : MeasurePreserving Prod.snd ((sampleLaw N p).prod (rademacherMeasure N))
      (rademacherMeasure N) := ⟨measurable_snd, Measure.snd_prod⟩
  have hae : ∀ᵐ z ∂((sampleLaw N p).prod (rademacherMeasure N)), ∀ j, z.2 j = 1 ∨ z.2 j = -1 :=
    ae_of_ae_map measurable_snd.aemeasurable
      (by rw [hsnd.map_eq]; exact ae_rademacherMeasure_forall N)
  have hmeas : AEStronglyMeasurable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) =>
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖) ((sampleLaw N p).prod (rademacherMeasure N)) := by
    refine AEStronglyMeasurable.const_mul ?_ _
    have hsum := Finset.aestronglyMeasurable_sum (μ := (sampleLaw N p).prod (rademacherMeasure N))
      Finset.univ (f := fun j (z : (Fin N → H × ℝ) × (Fin N → ℝ)) => z.2 j • Φ (z.1 j))
      fun j _ => ((measurable_pi_apply j).comp measurable_snd).aestronglyMeasurable.smul
        ((hΦj j).aestronglyMeasurable.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving)
    exact (hsum.congr (Eventually.of_forall fun z => Finset.sum_apply z Finset.univ _)).norm
  have hbound : Integrable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) => (N : ℝ)⁻¹ * ∑ j, ‖Φ (z.1 j)‖)
      ((sampleLaw N p).prod (rademacherMeasure N)) :=
    (hfst.integrable_comp_of_integrable (integrable_finsetSum Finset.univ
      (f := fun j (θ : Fin N → H × ℝ) => ‖Φ (θ j)‖) fun j _ => (hΦj j).norm)).const_mul _
  have hintprod : Integrable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) =>
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖) ((sampleLaw N p).prod (rademacherMeasure N)) := by
    refine hbound.mono' hmeas ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      (by positivity)
    rw [norm_smul, Real.norm_eq_abs]
    rcases hz j with h1 | h1 <;> simp [h1]
  unfold rademacherComplexity
  rw [hfun, rademacherMeasure_eq, integral_prod_pi_rademacherSign _ _ hintprod]
  simp_rw [integral_const_mul]
  rw [smul_eq_mul, ← Finset.mul_sum]
  ring

end RademacherComplexity

end OperatorRidgelet
