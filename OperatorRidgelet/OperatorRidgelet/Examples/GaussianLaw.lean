import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.Basic
import OperatorRidgelet.Transform.Gaussian
import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.ToMathlib.GaussianRealIntegral
import OperatorRidgelet.ToMathlib.GaussianCoordinateLaw

/-!
# Gaussian coordinates under `𝒩(0,Q)` and the Gaussian-parameter closed forms

Under a centred Gaussian measure `μ = 𝒩(0,Q)` (`IsCenteredGaussian Q μ`) the coordinate
`⟪·, v⟫` is `𝒩(0, ⟪Qv,v⟫)` (`IsCenteredGaussian.map_inner_eq_gaussianReal` of
`OperatorRidgelet.Transform.Basic`), which gives

* the closed forms `F_Q(x) = √(⟪Qx,x⟫/(2π))` and `Φ_Q(x) = (1 + ⟪Qx,x⟫)^{-1/2}` of Example
  `ex:gaussian-parameter` (`gaussianParameterReLU_eq`, `gaussianParameterGauss_eq`) and the
  hinge representation `Φ_Q(x) = ∫∫ ReLU(⟪a,x⟫ - b) φ''(b) 𝒩(0,Q)(da) db`
  (`gaussianParameterGauss_eq_integral_prod`);
* the mixed integral `∫ Φ(⟪v,x⟫) e^{-i⟪x,ξ⟫} μ(dx) = (1+σ²)^{-1/2} e^{-⟪S_v ξ,ξ⟫/2}` with
  `S_v = Q - (1+σ²)⁻¹ (Qv) ⊗ (Qv)` (`IsCenteredGaussian.integral_gaussianFun_mul_character`),
  the building block of the transform of the neural-operator layer;
* the second moment `∫ ‖a‖² 𝒩(0,Q)(da) = tr Q` (`IsCenteredGaussian.integral_norm_sq_eq_traceOf`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory LeanRidgelet Filter
open scoped RealInnerProductSpace NNReal ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-! ### The characteristic functional along lines and planes -/

section CharFun

variable {Q : H →L[ℝ] H} {μ : Measure H}

/-- The characteristic functional of `𝒩(0,Q)` along the line through `v`. -/
theorem IsCenteredGaussian.charFun_smul (hμ : IsCenteredGaussian Q μ) (v : H) (s : ℝ) :
    charFun μ (s • v) = Complex.exp (-((⟪Q v, v⟫ * s ^ 2 / 2 : ℝ) : ℂ)) := by
  have : ⟪Q (s • v), s • v⟫ = ⟪Q v, v⟫ * s ^ 2 := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hμ.charFun_eq, this]

/-- The characteristic functional of `𝒩(0,Q)` along the plane spanned by `v` and `w`. -/
theorem IsCenteredGaussian.charFun_smul_add_smul [CompleteSpace H] (hQ : IsSelfAdjoint Q)
    (hμ : IsCenteredGaussian Q μ) (v w : H) (s t : ℝ) :
    charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * ⟪Q v, v⟫ + 2 * s * t * ⟪Q v, w⟫ + t ^ 2 * ⟪Q w, w⟫) / 2 : ℝ) :
        ℂ)) := by
  have : ⟪Q (s • v + t • w), s • v + t • w⟫ =
      s ^ 2 * ⟪Q v, v⟫ + 2 * s * t * ⟪Q v, w⟫ + t ^ 2 * ⟪Q w, w⟫ := by
    rw [map_add, map_smul, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      ContinuousLinearMap.inner_map_comm hQ.isSymmetric w v]
    ring
  rw [hμ.charFun_eq, this]

end CharFun

/-! ### The quadratic form of a rank-one correction -/

omit [MeasurableSpace H] in
/-- `⟪(Q - (1+σ²)⁻¹ (Qv) ⊗ (Qv)) ξ, ξ⟫ = ⟪Qξ,ξ⟫ - ⟪Qv,ξ⟫²/(1+σ²)` with `σ² = ⟪Qv,v⟫`. -/
theorem inner_sub_rankOne_smul_apply (Q : H →L[ℝ] H) (v ξ : H) :
    ⟪(Q - (1 + ⟪Q v, v⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q v) (Q v)) ξ, ξ⟫ =
      ⟪Q ξ, ξ⟫ - ⟪Q v, ξ⟫ ^ 2 / (1 + ⟪Q v, v⟫) := by
  change ⟪Q ξ - (1 + ⟪Q v, v⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q v) (Q v) ξ, ξ⟫ = _
  rw [InnerProductSpace.rankOne_apply, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left]
  ring

/-! ### The law of a coordinate and the Gaussian-parameter closed forms -/

section Coordinate

variable [OpensMeasurableSpace H] {Q : H →L[ℝ] H} {μ : Measure H} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A Gaussian coordinate is integrable. -/
theorem IsCenteredGaussian.integrable_inner (hμ : IsCenteredGaussian Q μ) (v : H)
    (hv : 0 ≤ ⟪Q v, v⟫) : Integrable (fun x => ⟪x, v⟫) μ := by
  have hmeas : Measurable fun x : H => ⟪x, v⟫ := by fun_prop
  have h0 : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 ⟪Q v, v⟫.toNNReal) := by
    have := memLp_id_gaussianReal (μ := 0) (v := ⟪Q v, v⟫.toNNReal) 1
    simpa using this
  have h1 : Integrable (id : ℝ → ℝ) (gaussianReal 0 ⟪Q v, v⟫.toNNReal) :=
    memLp_one_iff_integrable.mp h0
  rw [← hμ.map_inner_eq_gaussianReal v hv] at h1
  exact (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).mp h1

omit [IsProbabilityMeasure μ] in
/-- **Example `ex:gaussian-parameter`**, first closed form: `F_Q(x) = √(⟪Qx,x⟫/(2π))`. -/
theorem gaussianParameterReLU_eq (hμ : IsCenteredGaussian Q μ) (x : H) (hx : 0 ≤ ⟪Q x, x⟫) :
    gaussianParameterReLU μ x = Real.sqrt (⟪Q x, x⟫ / (2 * Real.pi)) := by
  have hmeas : Measurable fun a : H => ⟪a, x⟫ := by fun_prop
  have hmax : AEStronglyMeasurable (fun t : ℝ => max t 0) (μ.map fun a => ⟪a, x⟫) :=
    (continuous_id.max continuous_const).aestronglyMeasurable
  have h := integral_max_zero_gaussianReal ⟪Q x, x⟫.toNNReal
  rw [← hμ.map_inner_eq_gaussianReal x hx, integral_map hmeas.aemeasurable hmax,
    Real.coe_toNNReal _ hx] at h
  unfold gaussianParameterReLU relu
  exact h

omit [IsProbabilityMeasure μ] in
/-- **Example `ex:gaussian-parameter`**, second closed form: `Φ_Q(x) = (1 + ⟪Qx,x⟫)^{-1/2}`. -/
theorem gaussianParameterGauss_eq (hμ : IsCenteredGaussian Q μ) (x : H) (hx : 0 ≤ ⟪Q x, x⟫) :
    gaussianParameterGauss μ x = (Real.sqrt (1 + ⟪Q x, x⟫))⁻¹ := by
  have hmeas : Measurable fun a : H => ⟪a, x⟫ := by fun_prop
  have hexp : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t ^ 2 / 2))
      (μ.map fun a => ⟪a, x⟫) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).aestronglyMeasurable
  have h := integral_exp_neg_sq_half_gaussianReal ⟪Q x, x⟫.toNNReal
  rw [← hμ.map_inner_eq_gaussianReal x hx, integral_map hmeas.aemeasurable hexp,
    Real.coe_toNNReal _ hx] at h
  unfold gaussianParameterGauss gaussianFun
  exact h

/-- **Example `ex:gaussian-parameter`**, hinge form:
`Φ_Q(x) = ∫∫ ReLU(⟪a,x⟫ - b) φ''(b) 𝒩(0,Q)(da) db`. -/
theorem gaussianParameterGauss_eq_integral_prod (hμ : IsCenteredGaussian Q μ) (x : H)
    (hx : 0 ≤ ⟪Q x, x⟫) :
    gaussianParameterGauss μ x =
      ∫ p : H × ℝ, relu (⟪p.1, x⟫ - p.2) * gaussianActDeriv2 p.2 ∂(μ.prod volume) := by
  rw [integral_prod _ (integrable_relu_sub_mul_gaussianActDeriv2_prod μ (hμ.integrable_inner x hx))]
  unfold gaussianParameterGauss
  congr 1
  funext a
  exact (integral_relu_sub_mul_gaussianActDeriv2 ⟪a, x⟫).symm

/-- The mixed Gaussian integral of the layer transform: for `σ² = ⟪Qv,v⟫` and
`S_v = Q - (1+σ²)⁻¹ (Qv) ⊗ (Qv)`,
`∫ Φ(⟪v,x⟫) e^{-i⟪x,ξ⟫} 𝒩(0,Q)(dx) = (1+σ²)^{-1/2} e^{-⟪S_v ξ,ξ⟫/2}`. -/
theorem IsCenteredGaussian.integral_gaussianFun_mul_character [CompleteSpace H]
    (hQ : IsSelfAdjoint Q)
    (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (hμ : IsCenteredGaussian Q μ) (v ξ : H) :
    ∫ x, ((gaussianFun ⟪v, x⟫ : ℝ) : ℂ) * character ξ x ∂μ =
      (((Real.sqrt (1 + ⟪Q v, v⟫))⁻¹ *
        Real.exp (-⟪(Q - (1 + ⟪Q v, v⟫)⁻¹ • InnerProductSpace.rankOne ℝ (Q v) (Q v)) ξ, ξ⟫ / 2) :
          ℝ) : ℂ) := by
  have key := MeasureTheory.integral_exp_neg_inner_sq_half_mul_exp_neg_inner_mul_I μ v ξ (hQ0 v)
    (fun s t => hμ.charFun_smul_add_smul hQ v ξ s t)
  have hL : (fun x => ((gaussianFun ⟪v, x⟫ : ℝ) : ℂ) * character ξ x) =
      fun x => Complex.exp (-((⟪x, v⟫ ^ 2 / 2 : ℝ) : ℂ)) *
        Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) := by
    funext x
    unfold gaussianFun character
    rw [real_inner_comm x v, Complex.ofReal_exp]
    congr 2
    · push_cast
      ring
    · ring
  have hS := inner_sub_rankOne_smul_apply Q v ξ
  have h1 : (1 + ((⟪Q v, v⟫ : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + ⟪Q v, v⟫ := by linarith [hQ0 v]
    exact_mod_cast this.ne'
  have h2 : (2 + ((⟪Q v, v⟫ : ℝ) : ℂ) * 2) ≠ 0 := by
    have : (0 : ℝ) < 2 + ⟪Q v, v⟫ * 2 := by linarith [hQ0 v]
    exact_mod_cast this.ne'
  rw [hL, key, hS]
  push_cast
  congr 2
  field_simp

end Coordinate

/-! ### The second moment of `𝒩(0,Q)` -/

section SecondMoment

variable [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H]

omit [MeasurableSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- The trace of a positive trace-class operator is the sum of the eigenvalues along any
orthonormal eigenbasis. -/
theorem traceOf_eq_tsum_of_eigen {Q : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q) {κ : Type*}
    (e : HilbertBasis κ ℝ H) (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hps : Summable p)
    (hQe : ∀ k, Q (e k) = p k • e k) : traceOf Q = ∑' k, p k := by
  unfold traceOf
  rw [dif_pos hQ.hasSummableTrace]
  have hb : Summable fun i => ⟪Q (hQ.hasSummableTrace.choose_spec.choose i),
      hQ.hasSummableTrace.choose_spec.choose i⟫ :=
    hQ.hasSummableTrace.choose_spec.choose_spec
  have h := ContinuousLinearMap.tsum_ofReal_inner_map_eq_of_eigen
    hQ.hasSummableTrace.choose_spec.choose e p hp hQe
  unfold traceAlong
  rw [← ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun i => hQ.inner_nonneg _) (tsum_nonneg hp),
    ENNReal.ofReal_tsum_of_nonneg (fun i => hQ.inner_nonneg _) hb,
    ENNReal.ofReal_tsum_of_nonneg hp hps, h]

/-- The second moment of `𝒩(0,Q)` as a Lebesgue integral: `∫⁻ ‖a‖² 𝒩(0,Q)(da) = ∑ q_k` along
an eigenbasis. -/
theorem IsCenteredGaussian.lintegral_norm_sq_eq {Q : H →L[ℝ] H} {μ : Measure H}
    (hμ : IsCenteredGaussian Q μ) {κ : Type} [Countable κ] (e : HilbertBasis κ ℝ H) (p : κ → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (hPe : ∀ k, Q (e k) = p k • e k) :
    ∫⁻ a, ENNReal.ofReal (‖a‖ ^ 2) ∂μ = ENNReal.ofReal (∑' k, p k) := by
  have hμ' : μ = gaussianSeries e p :=
    hμ.unique (isCenteredGaussian_gaussianSeries e p hp hs hPe)
  rw [hμ', gaussianSeries, lintegral_map (by fun_prop) (measurable_gaussianSeriesMap e p),
    ← lintegral_tsum_ofReal_mul_sq p hp hs]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_hasSum_gaussianSeriesMap e p hp hs] with x hx
  have h1 := e.hasSum_inner_sq (gaussianSeriesMap e p x)
  have h2 : ∀ i, ⟪e i, gaussianSeriesMap e p x⟫ = √(p i) * x i := fun i =>
    e.inner_eq_of_hasSum_smul hx i
  rw [← h1.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h1.summable]
  congr 1
  funext i
  rw [h2, mul_pow, Real.sq_sqrt (hp i)]

/-- `𝒩(0,Q)` has a finite second moment. -/
theorem IsCenteredGaussian.integrable_norm_sq {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    {μ : Measure H} (hμ : IsCenteredGaussian Q μ) : Integrable (fun a => ‖a‖ ^ 2) μ := by
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hQ.exists_eigenbasis
  refine ⟨(by fun_prop : Continuous fun a : H => ‖a‖ ^ 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun a => sq_nonneg _),
    hμ.lintegral_norm_sq_eq e p (fun k => (hp k).le) hs hPe]
  exact ENNReal.ofReal_lt_top

/-- The second moment of `𝒩(0,Q)` is the trace: `∫ ‖a‖² 𝒩(0,Q)(da) = tr Q`. -/
theorem IsCenteredGaussian.integral_norm_sq_eq_traceOf {Q : H →L[ℝ] H}
    (hQ : IsTraceClassCovariance Q) {μ : Measure H} (hμ : IsCenteredGaussian Q μ) :
    ∫ a, ‖a‖ ^ 2 ∂μ = traceOf Q := by
  obtain ⟨κ, _, e, p, hp, hs, hPe⟩ := hQ.exists_eigenbasis
  have hp' : ∀ k, 0 ≤ p k := fun k => (hp k).le
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun a => sq_nonneg _)
    (by fun_prop : Continuous fun a : H => ‖a‖ ^ 2).aestronglyMeasurable,
    hμ.lintegral_norm_sq_eq e p hp' hs hPe, ENNReal.toReal_ofReal (tsum_nonneg hp'),
    traceOf_eq_tsum_of_eigen hQ.toIsPositiveTraceClass e p hp' hs hPe]

end SecondMoment

end OperatorRidgelet
