import OperatorRidgelet.Architecture.Defs

/-!
# Basic lemmas on the operator-valued architecture

Supporting lemmas for the statements of Appendix F: the rank-one reduction identity
`n_{ℓ,A,b}(x) = ⟪ℓ, z⟫ β(⟪A^* ψ, x⟫ + ⟪ψ, b⟫)` for the activation `σ_β`, the norms of the
rank-one lift `A_a` and of the bias lift `b_c`, and the fact that the section `J_ψ` is a closed
embedding, which makes the transport of measures along `J_ψ` exact without any integrability
hypothesis.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Topology
open scoped ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The rank-one reduction identity -/

/-- Equation `eq:rank-one-reduction`: for the activation `σ_β`, the operator neuron is
`⟪ℓ, z⟫ β(⟪A^* ψ, x⟫ + ⟪ψ, b⟫)`. -/
theorem operatorNeuron_rankOneActivation [CompleteSpace H] (β : ℝ → ℝ) (ψ z ℓ : H)
    (A : H →L[ℝ] H) (b x : H) :
    operatorNeuron (rankOneActivation β ψ z) ℓ A b x =
      inner ℝ ℓ z * β (inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b) := by
  simp only [operatorNeuron, rankOneActivation, inner_smul_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- Along the section `J_ψ` and with the readout normalized by `⟪ℓ, z⟫ = 1`, the operator
neuron is the scalar ridge `β(⟪a, x⟫ + c)`. -/
theorem operatorNeuron_rankOneActivation_section [CompleteSpace H] (β : ℝ → ℝ) {ψ z ℓ : H}
    (hψ : ψ ≠ 0) (hℓz : inner ℝ ℓ z = 1) (a : H) (c : ℝ) (x : H) :
    operatorNeuron (rankOneActivation β ψ z) ℓ (rankOneLift ψ a) (biasLift ψ c) x =
      β (inner ℝ a x + c) := by
  rw [operatorNeuron_rankOneActivation, hℓz, one_mul, adjoint_rankOneLift_apply ψ a hψ,
    inner_biasLift ψ c hψ]

/-- With `Y = ℂ`, the integral network of a complex measure is the scalar complex ridge
synthesis of `OperatorRidgelet.OperatorValuedRidgelet`. -/
theorem integralNetwork_eq_scalarComplexRidgeSynthesis [MeasurableSpace H] (β : ℝ → ℂ)
    (μ : ComplexMeasure (ScalarRidgeParameter H)) (x : H) :
    integralNetwork β μ x = scalarComplexRidgeSynthesis β μ x :=
  rfl

/-! ## Norms of the lifts -/

theorem rankOneLift_sub (ψ a a' : H) :
    rankOneLift ψ (a - a') = rankOneLift ψ a - rankOneLift ψ a' := by
  simp only [rankOneLift, map_sub, smul_sub]

theorem biasLift_sub (ψ : H) (c c' : ℝ) :
    biasLift ψ (c - c') = biasLift ψ c - biasLift ψ c' := by
  simp only [biasLift, sub_mul, sub_smul]

theorem norm_biasLift {ψ : H} (hψ : ψ ≠ 0) (c : ℝ) : ‖biasLift ψ c‖ = |c| / ‖ψ‖ := by
  have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  rw [biasLift, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, abs_norm]
  field_simp

theorem norm_rankOneLift_apply (ψ a e : H) :
    ‖rankOneLift ψ a e‖ = |inner ℝ a e| / ‖ψ‖ := by
  rcases eq_or_ne ψ 0 with rfl | hψ
  · simp [rankOneLift]
  have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  simp only [rankOneLift, smul_apply, InnerProductSpace.rankOne_apply,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  field_simp

/-! ## The section is a closed embedding -/

/-- For `ψ ≠ 0`, the section `J_ψ` is a closed embedding, since `π_ψ` is a continuous left
inverse. -/
theorem isClosedEmbedding_operatorRidgeletSection [CompleteSpace H] {ψ : H} (hψ : ψ ≠ 0) :
    IsClosedEmbedding (operatorRidgeletSection ψ) :=
  (operatorParameterMap_section ψ hψ).isClosedEmbedding (continuous_operatorParameterMap ψ)
    (continuous_operatorRidgeletSection ψ)

/-- Exact transport along `J_ψ`: the operator synthesis of `(J_ψ)_# Γ` with activation `σ_β`
and normalized readout is the scalar integral network of `Γ`, with no integrability
hypothesis, because `J_ψ` is a closed embedding. -/
theorem operatorSynthesis_map_section [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0)
    (hℓz : inner ℝ ℓ z = 1) (Γ : ComplexMeasure (ScalarRidgeParameter H)) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ (Γ.map (operatorRidgeletSection ψ)) =
      integralNetwork (fun t => (β t : ℂ)) Γ := by
  funext x
  rw [operatorSynthesis, integralNetwork,
    (isClosedEmbedding_operatorRidgeletSection hψ).integral_map_vectorMeasure]
  congr 1
  funext p
  rw [show operatorRidgeletSection ψ p = (rankOneLift ψ p.1, biasLift ψ p.2) from rfl,
    operatorNeuron_rankOneActivation_section β hψ hℓz]

/-- The finite-width operator network along the section with normalized readout is the scalar
finite-width network. -/
theorem operatorFiniteNetwork_section [CompleteSpace H] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] (β : ℝ → ℝ) {ψ z ℓ : H} (hψ : ψ ≠ 0) (hℓz : inner ℝ ℓ z = 1) {N : ℕ}
    (v : Fin N → Y) (a : Fin N → H) (c : Fin N → ℝ) :
    operatorFiniteNetwork (rankOneActivation β ψ z) ℓ v (fun j => rankOneLift ψ (a j))
        (fun j => biasLift ψ (c j)) =
      finiteNetwork (fun t => (β t : ℂ)) v a c := by
  funext x
  simp only [operatorFiniteNetwork, finiteNetwork, operatorNeuron_rankOneActivation_section β hψ
    hℓz, Complex.coe_smul]

/-! ## The Hilbert–Schmidt norm -/

theorem sum_enorm_sq_le_hsNormSq (A : H →L[ℝ] H) (s : Finset H)
    (hs : Orthonormal ℝ ((↑) : s → H)) : ∑ e ∈ s, ‖A e‖ₑ ^ 2 ≤ hsNormSq A :=
  le_iSup₂ (f := fun (s : Finset H) (_ : Orthonormal ℝ ((↑) : s → H)) => ∑ e ∈ s, ‖A e‖ₑ ^ 2)
    s hs

theorem hsNormSq_le {A : H →L[ℝ] H} {C : ℝ≥0∞}
    (h : ∀ s : Finset H, Orthonormal ℝ ((↑) : s → H) → ∑ e ∈ s, ‖A e‖ₑ ^ 2 ≤ C) :
    hsNormSq A ≤ C :=
  iSup₂_le h

theorem sum_enorm_sq_eq_ofReal (A : H →L[ℝ] H) (s : Finset H) :
    ∑ e ∈ s, ‖A e‖ₑ ^ 2 = ENNReal.ofReal (∑ e ∈ s, ‖A e‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem orthonormal_finset_singleton {u : H} (hu : ‖u‖ = 1) :
    Orthonormal ℝ ((↑) : ({u} : Finset H) → H) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  obtain rfl := Finset.mem_singleton.mp hi
  obtain rfl := Finset.mem_singleton.mp hj
  simp [hu]

/-- Bessel's inequality for the rank-one lift: `∑_{e ∈ s} ‖A_a e‖² ≤ ‖a‖² / ‖ψ‖²` over every
finite orthonormal family `s`. -/
theorem sum_sq_norm_rankOneLift_le (ψ a : H) (s : Finset H)
    (hs : Orthonormal ℝ ((↑) : s → H)) :
    ∑ e ∈ s, ‖rankOneLift ψ a e‖ ^ 2 ≤ ‖a‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hB : ∑ e ∈ s, ‖inner ℝ a e‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have h := hs.sum_inner_products_le a (s := Finset.univ)
    rw [Finset.sum_coe_sort s (fun e => ‖inner ℝ e a‖ ^ 2)] at h
    simpa only [real_inner_comm] using h
  calc ∑ e ∈ s, ‖rankOneLift ψ a e‖ ^ 2
      = (∑ e ∈ s, ‖inner ℝ a e‖ ^ 2) / ‖ψ‖ ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [norm_rankOneLift_apply, div_pow, Real.norm_eq_abs]
    _ ≤ ‖a‖ ^ 2 / ‖ψ‖ ^ 2 := by gcongr

theorem hsNormSq_rankOneLift_le (ψ a : H) :
    hsNormSq (rankOneLift ψ a) ≤ ENNReal.ofReal (‖a‖ ^ 2 / ‖ψ‖ ^ 2) :=
  hsNormSq_le fun s hs => by
    rw [sum_enorm_sq_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (sum_sq_norm_rankOneLift_le ψ a s hs)

/-- The rank-one lift `A_a` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_rankOneLift (ψ a : H) : IsHilbertSchmidt (rankOneLift ψ a) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsNormSq_rankOneLift_le ψ a)

theorem le_hsNormSq_rankOneLift {ψ : H} (hψ : ψ ≠ 0) (a : H) :
    ENNReal.ofReal (‖a‖ ^ 2 / ‖ψ‖ ^ 2) ≤ hsNormSq (rankOneLift ψ a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnψ : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hu : ‖(‖a‖⁻¹ • a)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna]
  refine le_trans (le_of_eq ?_)
    (sum_enorm_sq_le_hsNormSq (rankOneLift ψ a) {‖a‖⁻¹ • a} (orthonormal_finset_singleton hu))
  rw [sum_enorm_sq_eq_ofReal, Finset.sum_singleton, norm_rankOneLift_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]
  congr 1
  rw [abs_of_nonneg (by positivity)]
  field_simp

/-- The squared Hilbert–Schmidt norm of the rank-one lift is `‖a‖² / ‖ψ‖²`. -/
theorem hsNormSq_rankOneLift {ψ : H} (hψ : ψ ≠ 0) (a : H) :
    hsNormSq (rankOneLift ψ a) = ENNReal.ofReal (‖a‖ ^ 2 / ‖ψ‖ ^ 2) :=
  le_antisymm (hsNormSq_rankOneLift_le ψ a) (le_hsNormSq_rankOneLift hψ a)

/-- The Hilbert–Schmidt norm of the rank-one lift is `‖a‖ / ‖ψ‖`. -/
theorem hsNorm_rankOneLift {ψ : H} (hψ : ψ ≠ 0) (a : H) :
    hsNorm (rankOneLift ψ a) = ‖a‖ / ‖ψ‖ := by
  rw [hsNorm, hsNormSq_rankOneLift hψ, ENNReal.toReal_ofReal (by positivity), ← div_pow,
    Real.sqrt_sq (by positivity)]

theorem norm_apply_le_hsNorm {A : H →L[ℝ] H} (hA : IsHilbertSchmidt A) {u : H}
    (hu : ‖u‖ = 1) : ‖A u‖ ≤ hsNorm A := by
  have h := sum_enorm_sq_le_hsNormSq A {u} (orthonormal_finset_singleton hu)
  rw [sum_enorm_sq_eq_ofReal, Finset.sum_singleton] at h
  rw [hsNorm, ← Real.sqrt_sq (norm_nonneg (A u))]
  exact Real.sqrt_le_sqrt ((ENNReal.ofReal_le_iff_le_toReal hA).mp h)

/-- The operator norm is dominated by the Hilbert–Schmidt norm. -/
theorem opNorm_le_hsNorm {A : H →L[ℝ] H} (hA : IsHilbertSchmidt A) : ‖A‖ ≤ hsNorm A := by
  refine ContinuousLinearMap.opNorm_le_bound A (Real.sqrt_nonneg _) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ • x)‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have h := norm_apply_le_hsNorm hA hu
  rw [map_smul, norm_smul, norm_inv, norm_norm] at h
  calc ‖A x‖ = ‖x‖ * (‖x‖⁻¹ * ‖A x‖) := by field_simp
    _ ≤ ‖x‖ * hsNorm A := by gcongr
    _ = hsNorm A * ‖x‖ := mul_comm _ _

theorem hsNorm_nonneg (A : H →L[ℝ] H) : 0 ≤ hsNorm A :=
  Real.sqrt_nonneg _

/-- Continuity of the section `J_ψ` for the Hilbert–Schmidt norm on the operator component. -/
theorem tendsto_hsNorm_rankOneLift_sub_add_norm_biasLift_sub {ψ : H} (hψ : ψ ≠ 0) (a : H)
    (c : ℝ) :
    Filter.Tendsto
      (fun p : H × ℝ =>
        hsNorm (rankOneLift ψ p.1 - rankOneLift ψ a) + ‖biasLift ψ p.2 - biasLift ψ c‖)
      (𝓝 (a, c)) (𝓝 0) := by
  have h : (fun p : H × ℝ =>
      hsNorm (rankOneLift ψ p.1 - rankOneLift ψ a) + ‖biasLift ψ p.2 - biasLift ψ c‖) =
      fun p : H × ℝ => ‖p.1 - a‖ / ‖ψ‖ + |p.2 - c| / ‖ψ‖ := by
    funext p
    rw [← rankOneLift_sub, hsNorm_rankOneLift hψ, ← biasLift_sub, norm_biasLift hψ]
  rw [h]
  have hc : Continuous fun p : H × ℝ => ‖p.1 - a‖ / ‖ψ‖ + |p.2 - c| / ‖ψ‖ := by fun_prop
  simpa using hc.tendsto (a, c)

/-! ## Measurability of the Hilbert–Schmidt norm -/

/-- `hsNormSq` is lower semicontinuous for the operator norm, as a supremum of continuous
functions. -/
theorem lowerSemicontinuous_hsNormSq :
    LowerSemicontinuous (hsNormSq : (H →L[ℝ] H) → ℝ≥0∞) := by
  unfold hsNormSq
  refine lowerSemicontinuous_iSup fun s => lowerSemicontinuous_iSup fun _ => ?_
  refine Continuous.lowerSemicontinuous ?_
  exact continuous_finsetSum _ fun e _ =>
    (ENNReal.continuous_pow 2).comp (ContinuousLinearMap.apply ℝ H e).continuous.enorm

theorem measurable_hsNormSq : Measurable (hsNormSq : (H →L[ℝ] H) → ℝ≥0∞) :=
  lowerSemicontinuous_hsNormSq.measurable

theorem measurable_hsNorm : Measurable (hsNorm : (H →L[ℝ] H) → ℝ) :=
  measurable_hsNormSq.ennreal_toReal.sqrt

/-! ## Lipschitz estimates -/

theorem norm_le_of_lipschitzWith {E : Type*} [NormedAddCommGroup E] {β : ℝ → E} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (t : ℝ) : ‖β t‖ ≤ ‖β 0‖ + L * |t| := by
  have h := hβ.dist_le_mul t 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero, Real.norm_eq_abs] at h
  calc ‖β t‖ = ‖β 0 + (β t - β 0)‖ := by congr 1; abel
    _ ≤ ‖β 0‖ + ‖β t - β 0‖ := norm_add_le _ _
    _ ≤ ‖β 0‖ + L * |t| := by linarith

/-- The Lipschitz envelope of a scalar ridge: `‖β(⟪a, x⟫ + c)‖` is dominated by a multiple of
`1 + ‖a‖ + |c|`. -/
theorem norm_ridge_le {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β) (x : H) (θ : H × ℝ) :
    ‖β (inner ℝ θ.1 x + θ.2)‖ ≤ (‖β 0‖ + L * max ‖x‖ 1) * (1 + ‖θ.1‖ + |θ.2|) := by
  have h1 := norm_le_of_lipschitzWith hβ (inner ℝ θ.1 x + θ.2)
  have h2 : |inner ℝ θ.1 x + θ.2| ≤ ‖θ.1‖ * ‖x‖ + |θ.2| :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) le_rfl)
  have hM : ‖x‖ ≤ max ‖x‖ 1 := le_max_left _ _
  have hM1 : (1 : ℝ) ≤ max ‖x‖ 1 := le_max_right _ _
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have h3 : ‖θ.1‖ * ‖x‖ + |θ.2| ≤ max ‖x‖ 1 * (‖θ.1‖ + |θ.2|) := by
    nlinarith [mul_le_mul_of_nonneg_left hM (norm_nonneg θ.1),
      mul_le_mul_of_nonneg_left hM1 (abs_nonneg θ.2)]
  have h4 : (L : ℝ) * |inner ℝ θ.1 x + θ.2| ≤ L * (max ‖x‖ 1 * (‖θ.1‖ + |θ.2|)) :=
    mul_le_mul_of_nonneg_left (h2.trans h3) hL
  nlinarith [norm_nonneg (β 0), norm_nonneg θ.1, abs_nonneg θ.2,
    mul_nonneg hL (zero_le_one.trans hM1),
    mul_nonneg (norm_nonneg (β 0)) (add_nonneg (norm_nonneg θ.1) (abs_nonneg θ.2))]

/-- Under the first-moment condition, a globally Lipschitz activation gives an integrable
ridge: the Bochner integral defining `S_β[Γ](x)` exists. -/
theorem integrable_ridge_of_lipschitz [MeasurableSpace H] [BorelSpace H] {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {β : ℝ → ℂ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (Γ : VectorMeasure (H × ℝ) Y)
    (hmom : Integrable (fun θ : H × ℝ => 1 + ‖θ.1‖ + |θ.2|) Γ.variation) (x : H) :
    Γ.Integrable fun θ : H × ℝ => β (inner ℝ θ.1 x + θ.2) := by
  refine Integrable.mono' (hmom.const_mul (‖β 0‖ + L * max ‖x‖ 1)) ?_
    (Filter.Eventually.of_forall fun θ => norm_ridge_le hβ x θ)
  exact (hβ.continuous.comp
    (by fun_prop : Continuous fun θ : H × ℝ => inner ℝ θ.1 x + θ.2)).aestronglyMeasurable

/-- The envelope of the reduced neuron: for Hilbert–Schmidt `A` and `‖x‖ ≤ r`,
`|β(⟪A^* ψ, x⟫ + ⟪ψ, b⟫)| ≤ |β(0)| + L ‖ψ‖ (r ‖A‖_{𝓛₂} + ‖b‖)`. -/
theorem abs_ridge_adjoint_le [CompleteSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β)
    (ψ : H) {A : H →L[ℝ] H} (hA : IsHilbertSchmidt A) (b : H) {x : H} {r : ℝ} (hx : ‖x‖ ≤ r) :
    |β (inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b)| ≤
      |β 0| + L * ‖ψ‖ * (r * hsNorm A + ‖b‖) := by
  have h1 := norm_le_of_lipschitzWith hβ
    (inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b)
  simp only [Real.norm_eq_abs] at h1
  have h2 : |inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b| ≤
      ‖ContinuousLinearMap.adjoint A ψ‖ * ‖x‖ + ‖ψ‖ * ‖b‖ :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
  have h3 : ‖ContinuousLinearMap.adjoint A ψ‖ ≤ hsNorm A * ‖ψ‖ := by
    calc ‖ContinuousLinearMap.adjoint A ψ‖ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖ψ‖ :=
          (ContinuousLinearMap.adjoint A).le_opNorm ψ
      _ = ‖A‖ * ‖ψ‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ hsNorm A * ‖ψ‖ := by gcongr; exact opNorm_le_hsNorm hA
  have h0x : 0 ≤ ‖x‖ := norm_nonneg x
  have hr : 0 ≤ r := h0x.trans hx
  have h4 : ‖ContinuousLinearMap.adjoint A ψ‖ * ‖x‖ ≤ hsNorm A * ‖ψ‖ * r :=
    mul_le_mul h3 hx h0x (mul_nonneg (hsNorm_nonneg A) (norm_nonneg ψ))
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have h5 : (L : ℝ) * |inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b| ≤
      L * (hsNorm A * ‖ψ‖ * r + ‖ψ‖ * ‖b‖) :=
    mul_le_mul_of_nonneg_left (h2.trans (add_le_add h4 le_rfl)) hL
  linarith

/-- The envelope of the reduced neuron in the form needed for the first-moment condition. -/
theorem norm_ridge_adjoint_le_moment [CompleteSpace H] {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (ψ : H) {A : H →L[ℝ] H} (hA : IsHilbertSchmidt A) (b x : H) :
    ‖((β (inner ℝ (ContinuousLinearMap.adjoint A ψ) x + inner ℝ ψ b) : ℝ) : ℂ)‖ ≤
      (|β 0| + L * ‖ψ‖ * max ‖x‖ 1) * (1 + hsNorm A + ‖b‖) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_ridge_adjoint_le hβ ψ hA b (le_max_left ‖x‖ 1)).trans ?_
  have hM1 : (1 : ℝ) ≤ max ‖x‖ 1 := le_max_right _ _
  have hLψ : 0 ≤ (L : ℝ) * ‖ψ‖ := mul_nonneg L.coe_nonneg (norm_nonneg ψ)
  nlinarith [mul_nonneg (abs_nonneg (β 0)) (add_nonneg (hsNorm_nonneg A) (norm_nonneg b)),
    mul_nonneg hLψ (zero_le_one.trans hM1),
    mul_nonneg hLψ (mul_nonneg (norm_nonneg b) (sub_nonneg.2 hM1))]

/-! ## Transport of measures along `π_ψ` -/

/-- Exact transport along `π_ψ`: under the first-moment condition on a complex measure carried
by `𝓛₂(H) × H`, the operator synthesis with activation `σ_β` and normalized readout is the
scalar integral network of the pushforward `(π_ψ)_# Γ_op`. -/
theorem operatorSynthesis_eq_integralNetwork_map [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H))
    (hHS : ∀ᵐ p ∂Γop.variation, IsHilbertSchmidt p.1)
    (hmom : Integrable (fun p : OperatorRidgeParameter H => 1 + hsNorm p.1 + ‖p.2‖)
      Γop.variation)
    {ℓ z : H} (hℓz : inner ℝ ℓ z = 1) :
    operatorSynthesis (rankOneActivation β ψ z) ℓ Γop =
      integralNetwork (fun t => (β t : ℂ)) (Γop.map (operatorParameterMap ψ)) := by
  funext x
  have hcont : Continuous fun θ : ScalarRidgeParameter H =>
      ((β (inner ℝ θ.1 x + θ.2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hβ.continuous.comp (by fun_prop))
  have hint : Γop.Integrable ((fun θ : ScalarRidgeParameter H =>
      ((β (inner ℝ θ.1 x + θ.2) : ℝ) : ℂ)) ∘ operatorParameterMap ψ) := by
    refine Integrable.mono' (hmom.const_mul (|β 0| + L * ‖ψ‖ * max ‖x‖ 1))
      (hcont.comp (continuous_operatorParameterMap ψ)).aestronglyMeasurable ?_
    filter_upwards [hHS] with p hp
    exact norm_ridge_adjoint_le_moment hβ ψ hp p.2 x
  rw [operatorSynthesis, integralNetwork,
    VectorMeasure.integral_map (measurable_operatorParameterMap ψ) hcont.aestronglyMeasurable
      hint]
  congr 1
  funext p
  rw [operatorNeuron_rankOneActivation, hℓz, one_mul]
  rfl

/-- Bounded synthesis: for `‖x‖ ≤ r`,
`‖S_op Γ_op(x)‖ ≤ ∫ [|β(0)| + L ‖ψ‖ (r ‖A‖_{𝓛₂} + ‖b‖)] d|Γ_op|`. -/
theorem norm_operatorSynthesis_le [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) (ψ : H)
    (Γop : ComplexMeasure (OperatorRidgeParameter H)) [IsFiniteMeasure Γop.variation]
    (hHS : ∀ᵐ p ∂Γop.variation, IsHilbertSchmidt p.1)
    (hmom : Integrable (fun p : OperatorRidgeParameter H => 1 + hsNorm p.1 + ‖p.2‖)
      Γop.variation)
    {ℓ z : H} (hℓz : inner ℝ ℓ z = 1) {x : H} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x‖ ≤
      ∫ p, (|β 0| + (L : ℝ) * ‖ψ‖ * (r * hsNorm p.1 + ‖p.2‖)) ∂Γop.variation := by
  have h1 : Integrable (fun p : OperatorRidgeParameter H => hsNorm p.1) Γop.variation := by
    refine hmom.mono' (measurable_hsNorm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _)]
    have := norm_nonneg p.2
    linarith
  have h2 : Integrable (fun p : OperatorRidgeParameter H => ‖p.2‖) Γop.variation := by
    refine hmom.mono' measurable_snd.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_norm]
    have := hsNorm_nonneg p.1
    linarith
  have hbound : Integrable (fun p : OperatorRidgeParameter H =>
      |β 0| + (L : ℝ) * ‖ψ‖ * (r * hsNorm p.1 + ‖p.2‖)) Γop.variation :=
    (integrable_const _).add (((h1.const_mul r).add h2).const_mul _)
  have hpt : ∀ᵐ p ∂Γop.variation,
      ‖((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)‖ ≤
        |β 0| + (L : ℝ) * ‖ψ‖ * (r * hsNorm p.1 + ‖p.2‖) := by
    filter_upwards [hHS] with p hp
    rw [operatorNeuron_rankOneActivation, hℓz, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_ridge_adjoint_le hβ ψ hp p.2 hx
  have hf : Integrable (fun p : OperatorRidgeParameter H =>
      ((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)) Γop.variation := by
    refine Integrable.mono' hbound ?_ hpt
    have hc : Continuous fun p : OperatorRidgeParameter H =>
        ((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ) := by
      simp only [operatorNeuron_rankOneActivation, hℓz, one_mul]
      exact Complex.continuous_ofReal.comp (hβ.continuous.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  have hI : 0 ≤ ∫ p, ‖((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)‖
      ∂Γop.variation := integral_nonneg fun p => norm_nonneg _
  calc ‖operatorSynthesis (rankOneActivation β ψ z) ℓ Γop x‖
      ≤ ‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ *
        ∫ p, ‖((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)‖
          ∂Γop.variation := VectorMeasure.norm_integral_le_integral_norm
    _ ≤ 1 * ∫ p, ‖((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)‖
          ∂Γop.variation :=
        mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le hI
    _ = ∫ p, ‖((operatorNeuron (rankOneActivation β ψ z) ℓ p.1 p.2 x : ℝ) : ℂ)‖
          ∂Γop.variation := one_mul _
    _ ≤ ∫ p, (|β 0| + (L : ℝ) * ‖ψ‖ * (r * hsNorm p.1 + ‖p.2‖)) ∂Γop.variation :=
        integral_mono_ae hf.norm hbound hpt

end OperatorRidgelet
