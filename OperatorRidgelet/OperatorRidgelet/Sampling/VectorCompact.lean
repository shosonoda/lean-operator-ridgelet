import OperatorRidgelet.Sampling.VectorRates
import OperatorRidgelet.ToMathlib.SampleMeanL1

/-! # Compact-open vector sampling and Rademacher averages -/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  {K : Set H}

/-- The vector Rademacher complexity as the average over the finite sign space. -/
theorem rademacherComplexity_eq_sum_signs_vec (N : ℕ) (p : Measure (H × ℝ))
    [IsProbabilityMeasure p] (β : ℝ → ℂ) (h : H × ℝ → Y) {Φ : H × ℝ → (K →ᵇ Y)}
    (hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) • h θ) (hint : Integrable Φ p) :
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
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.coe_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    change (z.2 j : ℝ) • Φ (z.1 j) x = _
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


variable {Ω : Type*} [MeasurableSpace Ω]

/-- Evaluation of a vector-valued centered sample sum. -/
theorem smul_sum_sub_apply_vec (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → Y) {Φ : Ω → (K →ᵇ Y)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) • h ω) (hint : Integrable Φ p)
    (V : ℝ) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) (x : K) :
    ((V / N : ℝ) • (∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p)) x =
      ∑ j, β (⟪(π (ω j)).1, (x : H)⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
        V • ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) • h ω' ∂p := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have heval : (∫ ω', Φ ω' ∂p) x = ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) • h ω' ∂p := by
    change (BoundedContinuousFunction.evalCLM ℂ x) (∫ ω', Φ ω' ∂p) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    exact integral_congr_ae (Eventually.of_forall fun ω' => hΦ ω' x)
  change (V / N : ℝ) • ((BoundedContinuousFunction.evalCLM ℂ x) (∑ j, Φ (ω j)) -
    (N : ℝ) • (∫ ω', Φ ω' ∂p) x) = _
  rw [map_sum, heval, smul_sub, smul_smul, div_mul_cancel₀ V hN', Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change (V / N : ℝ) • Φ (ω j) x = _
  rw [hΦ, Complex.coe_smul]
  exact smul_comm _ _ _

/-- The sampled-network error on `K` is `V/N` times the `C(K)`-norm of the centred sum of the
atoms `Φ(ω) = β(⟪π(ω)_1, ·⟫ + π(ω)_2) h(ω)`. -/
theorem compactSupNorm_sampled_sub_eq_vec (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → Y) {Φ : Ω → (K →ᵇ Y)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) • h ω) (hint : Integrable Φ p)
    {V : ℝ} (hV : 0 ≤ V) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) :
    compactSupNorm K (fun x =>
        ∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
          V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p) =
      V / N * ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖ := by
  conv_rhs => rw [← abs_of_nonneg (div_nonneg hV (Nat.cast_nonneg N)), ← Real.norm_eq_abs,
    ← norm_smul]
  exact compactSupNorm_eq_norm_of_forall _ (smul_sum_sub_apply_vec p β π h hΦ hint V hN ω)


/-- The ridge atom with a vector outer weight, restricted to a compact set. -/
def vectorRidgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β)
    (θ : H × ℝ) (y : Y) : K →ᵇ Y :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K => β (⟪θ.1, (x : H)⟫ + θ.2) • y, by fun_prop⟩

/-- The vector ridge atom depends continuously on the parameter and outer weight. -/
theorem continuous_vectorRidgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) :
    Continuous (fun z : (H × ℝ) × Y => vectorRidgeAtom hK hβ z.1 z.2) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(((H × ℝ) × Y) × K, Y) :=
    ⟨fun q => β (⟪q.1.1.1, (q.2 : H)⟫ + q.1.1.2) • q.1.2, by fun_prop⟩
  exact (ContinuousMap.isometryEquivBoundedOfCompact K Y).continuous.comp
    (ContinuousMap.curry F).continuous

/-- The norm of a vector ridge atom factors into the scalar norm and the weight norm. -/
theorem norm_vectorRidgeAtom (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β)
    (θ : H × ℝ) (y : Y) :
    ‖vectorRidgeAtom hK hβ θ y‖ ≤ ‖ridgeAtom hK hβ θ‖ * ‖y‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖β (⟪θ.1, (x : H)⟫ + θ.2) • y‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm
    (ridgeAtom hK hβ θ) x) (norm_nonneg _)

variable [BorelSpace H] [SecondCountableTopology H] [SecondCountableTopology Y]

/-- The vector atoms with a measurable unit phase and finite parameter moment are integrable. -/
theorem integrable_vectorRidgeAtom (hK : IsCompact K) {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure (H × ℝ)) [IsProbabilityMeasure p]
    (h : H × ℝ → Y) (hh : AEStronglyMeasurable h p) (hu : ∀ᵐ θ ∂p, ‖h θ‖ = 1)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) p) :
    Integrable (fun θ => vectorRidgeAtom hK hβ.continuous θ (h θ)) p := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : SecondCountableTopology K := EMetric.secondCountable_of_sigmaCompact K
  haveI : SecondCountableTopology C(K, Y) := ContinuousMap.instSecondCountableTopology
  haveI : SecondCountableTopology (K →ᵇ Y) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K Y).toHomeomorph.symm.secondCountableTopology
  have hm := (continuous_vectorRidgeAtom hK hβ.continuous).comp_aestronglyMeasurable
    (aestronglyMeasurable_id.prodMk hh)
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let C := ‖β 0‖ + (L : ℝ) * max r 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : Integrable (fun θ : H × ℝ => C * (3 + (‖θ.1‖ ^ 2 + |θ.2| ^ 2))) p :=
    ((integrable_const _).add hM).const_mul C
  apply hb.mono' hm
  filter_upwards [hu] with θ hθ
  refine (norm_vectorRidgeAtom hK hβ.continuous θ (h θ)).trans ?_
  rw [hθ, mul_one]
  have ha : ‖ridgeAtom hK hβ.continuous θ‖ ≤ C * (1 + ‖θ.1‖ + |θ.2|) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact (norm_ridge_le hβ (x : H) θ).trans (by dsimp [C]; gcongr; exact hr x x.2)
  apply ha.trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [sq_nonneg (‖θ.1‖ - 1), sq_nonneg (|θ.2| - 1)]

/-- The compact-open vector sampling bound from symmetrization of the integrable atom map. -/
theorem integral_polarSampledNetwork_compact_le {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ))
    (hK : IsCompact K) {N : ℕ} (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ) ≤
      2 * polarWeight Γ * rademacherComplexity N K (polarLaw Γ) β (polarDensity Γ) := by
  let Φ : H × ℝ → (K →ᵇ Y) := fun θ => vectorRidgeAtom hK hβ.continuous θ (polarDensity Γ θ)
  have hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) • polarDensity Γ θ := fun _ _ => rfl
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN, integral_zero_measure,
      polarWeight_eq_zero_of_totalVariation_eq_zero h0, mul_zero, zero_mul]
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  have hint : Integrable Φ (polarLaw Γ) := integrable_vectorRidgeAtom hK hβ (polarLaw Γ)
    (polarDensity Γ) hh hh1 hM
  have hΦ' : ∀ θ (x : K), Φ θ x = β (⟪(id θ).1, (x : H)⟫ + (id θ).2) • polarDensity Γ θ := hΦ
  have hpt : ∀ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x) =
        polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖ := by
    intro θ
    rw [← compactSupNorm_sampled_sub_eq_vec (polarLaw Γ) β id (polarDensity Γ) hΦ' hint
      (polarWeight_nonneg Γ) hN θ]
    refine compactSupNorm_congr fun x hx => ?_
    rw [integralNetwork_eq_integral_polarLaw β Γ h0
      ((memLp_ridge_complex hβ (polarLaw Γ) hM x).integrable (by norm_num))]
    rfl
  have hsym := integral_norm_sum_sub_le (polarLaw Γ) hint (signVector (N := N))
    (fun _ => (2 ^ N : ℝ)⁻¹) (fun _ => by positivity) (sum_signs_inv_pow_two N)
    fun σ j => signVector_eq_one_or_neg_one σ j
  rw [rademacherComplexity_eq_sum_signs_vec N (polarLaw Γ) β (polarDensity Γ) hΦ hint]
  calc ∫ θ, compactSupNorm K (fun x => polarSampledNetwork β Γ θ x - integralNetwork β Γ x)
        ∂sampleLaw N (polarLaw Γ)
      = ∫ θ, polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) := integral_congr_ae (Eventually.of_forall hpt)
    _ = polarWeight Γ / N * ∫ θ, ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖
          ∂sampleLaw N (polarLaw Γ) := integral_const_mul _ _
    _ ≤ polarWeight Γ / N * (2 * ∑ σ : Signs N, (2 ^ N : ℝ)⁻¹ *
          ∫ θ, ‖∑ j, signVector σ j • Φ (θ j)‖ ∂sampleLaw N (polarLaw Γ)) :=
        mul_le_mul_of_nonneg_left hsym (div_nonneg (polarWeight_nonneg Γ) (Nat.cast_nonneg N))
    _ = _ := by
        rw [← Finset.mul_sum]
        ring

end OperatorRidgelet
