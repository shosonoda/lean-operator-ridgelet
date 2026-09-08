import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.Basic
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical

/-!
# Statements of Section 7 (genuinely infinite-dimensional examples) and Appendix E

Each item is `theorem OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, identical to its twin in
`Challenge.Examples`, proved from the library or left as `sorry`.

The examples are stated in the Gaussian setting of the manuscript (`μ = 𝒩(0,Q)` through
`IsCenteredGaussian Q μ`, `ν_α = gaussianMixture N α` through Gaussian layers `N` for `P`, with
`dim H = ∞`), one theorem per claim.  The representations of traces, square roots, resolvents,
Fredholm determinants, cylindrical functions, the neural-operator layer, the local sampling
objects, the torus, and the Dirichlet operator are documented in
`OperatorRidgelet.Examples.Defs`.  Sampling claims are stated as bounds on the lower integral
`∫⁻` of the error over the product law of the sample, with the width `n ≥ 1` (the layers of
`ν_α` are `N`).  Example `ex:gaussian-parameter` is stated on a Hilbert space with a Hilbert basis
`e` diagonalizing `Q` (`Q e_j = q_j e_j`, `q_j > 0`, `∑ q_j < ∞`), which is the manuscript's
`ℓ²(ℕ)` up to the unitary identification.  The two claims of Example `ex:core-elements` on `f_W`
and on the operator layers are `ex_core_elements_iv` and `ex_core_elements_v` (the first claim is
`ex_core_elements_i`–`iii` in `OperatorRidgelet.Paper.Transform`).
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Complex Filter Topology LeanRidgelet
open scoped ENNReal NNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Lemma `lem:gaussian-quadratic` -/

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- **Lemma [lem:gaussian-quadratic]** Gaussian integral of a quadratic exponential.  For a
positive self-adjoint trace-class `Σ` and a bounded positive self-adjoint `S`, the operator
`M = Σ^{1/2} S Σ^{1/2}` is trace class. -/
theorem lem_gaussian_quadratic_i {Cov S R : H →L[ℝ] H} (hCov : IsPositiveTraceClass Cov)
    (hS : IsSelfAdjoint S) (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫) (hR : IsPositiveSqrt R Cov) :
    HasSummableTrace (R * S * R) := by
  sorry

/-- **Lemma [lem:gaussian-quadratic]** Gaussian integral of a quadratic exponential.  With
`M = Σ^{1/2} S Σ^{1/2}`,
`∫ e^{i⟨x,ξ⟩ - ⟨Sξ,ξ⟩/2} 𝒩(0,Σ)(dξ) = det(I+M)^{-1/2} exp(-½⟨Σ^{1/2}(I+M)⁻¹Σ^{1/2}x, x⟩)`. -/
theorem lem_gaussian_quadratic_ii {Cov S R : H →L[ℝ] H} (hCov : IsPositiveTraceClass Cov)
    (hS : IsSelfAdjoint S) (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫) (hR : IsPositiveSqrt R Cov)
    (μ : Measure H) [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Cov μ) (x : H) :
    ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I - ((⟪S ξ, ξ⟫ / 2 : ℝ) : ℂ)) ∂μ =
      (((Real.sqrt (fredholmDet (R * S * R)))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((resolventForm R (R * S * R) x / 2 : ℝ) : ℂ)) := by
  sorry

/-! ### Lemma `lem:gaussian-hinge` -/

/-- **Lemma [lem:gaussian-hinge]** Absolute hinge representation of the Gaussian.  For
`φ(u) = e^{-u²/2}` the integral `∫ (u-b)_+ φ''(b) db` converges absolutely for each `u`. -/
theorem lem_gaussian_hinge_i_a (u : ℝ) :
    Integrable fun b : ℝ => relu (u - b) * gaussianActDeriv2 b := by
  have h0 := integrable_abs_pow_mul_exp_neg_sq_half 0
  have h1 := integrable_abs_pow_mul_exp_neg_sq_half 1
  have h2 := integrable_abs_pow_mul_exp_neg_sq_half 2
  have h3 := integrable_abs_pow_mul_exp_neg_sq_half 3
  refine (((h2.add h0).const_mul |u|).add (h3.add h1)).mono' ?_ ?_
  · exact ((continuous_relu.comp (continuous_const.sub continuous_id)).mul
      continuous_gaussianActDeriv2).aestronglyMeasurable
  · filter_upwards with b
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (relu_nonneg _)]
    have hr : relu (u - b) ≤ |u| + |b| := by
      unfold relu
      exact max_le (by linarith [le_abs_self u, neg_abs_le b]) (by positivity)
    have hb2 : b ^ 2 + 1 = |b| ^ 2 + |b| ^ 0 := by rw [sq_abs, pow_zero]
    calc relu (u - b) * |gaussianActDeriv2 b|
        ≤ (|u| + |b|) * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) :=
          mul_le_mul hr (abs_gaussianActDeriv2_le b) (abs_nonneg _) (by positivity)
      _ = |u| * (|b| ^ 2 * Real.exp (-b ^ 2 / 2) + |b| ^ 0 * Real.exp (-b ^ 2 / 2)) +
          (|b| ^ 3 * Real.exp (-b ^ 2 / 2) + |b| ^ 1 * Real.exp (-b ^ 2 / 2)) := by
          rw [hb2]; ring

/-- **Lemma [lem:gaussian-hinge]** Absolute hinge representation of the Gaussian.  For
`φ(u) = e^{-u²/2}`, `φ(u) = ∫ (u-b)_+ φ''(b) db` for each `u`. -/
theorem lem_gaussian_hinge_i_b (u : ℝ) :
    ∫ b : ℝ, relu (u - b) * gaussianActDeriv2 b = gaussianAct u := by
  sorry

/-- **Lemma [lem:gaussian-hinge]** Absolute hinge representation of the Gaussian.
`∫ (1 + |b|^k) |φ''(b)| db < ∞` for every `k ≥ 0`. -/
theorem lem_gaussian_hinge_ii (k : ℕ) :
    Integrable fun b : ℝ => (1 + |b| ^ k) * |gaussianActDeriv2 b| := by
  have h0 := integrable_abs_pow_mul_exp_neg_sq_half 0
  have h2 := integrable_abs_pow_mul_exp_neg_sq_half 2
  have hk := integrable_abs_pow_mul_exp_neg_sq_half k
  have hk2 := integrable_abs_pow_mul_exp_neg_sq_half (k + 2)
  refine ((h2.add h0).add (hk2.add hk)).mono' ?_ ?_
  · exact ((continuous_const.add (continuous_abs.pow k)).mul
      continuous_gaussianActDeriv2.abs).aestronglyMeasurable
  · filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb2 : b ^ 2 + 1 = |b| ^ 2 + |b| ^ 0 := by rw [sq_abs, pow_zero]
    calc (1 + |b| ^ k) * |gaussianActDeriv2 b|
        ≤ (1 + |b| ^ k) * ((b ^ 2 + 1) * Real.exp (-b ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (abs_gaussianActDeriv2_le b) (by positivity)
      _ = |b| ^ 2 * Real.exp (-b ^ 2 / 2) + |b| ^ 0 * Real.exp (-b ^ 2 / 2) +
          (|b| ^ (k + 2) * Real.exp (-b ^ 2 / 2) + |b| ^ k * Real.exp (-b ^ 2 / 2)) := by
          rw [hb2]; ring

/-! ### Example `ex:closed-form` -/

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  For `W` bounded,
positive, injective, self-adjoint with `M = Q^{1/2} W Q^{1/2}` trace class,
`𝒢_Q f_W(ξ) = D^{-1/2} e^{-κ_W(ξ)/2}` with `D = det(I+M)`. -/
theorem ex_closed_form_i_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (W S : H →L[ℝ] H)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hWi : Function.Injective W)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    ∀ ξ : H, gaussFourier μ (gaussianTarget W) ξ =
      (((Real.sqrt (fredholmDet (S * W * S)))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((gaussianKappa S W ξ / 2 : ℝ) : ℂ)) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  For every
band-pass `ρ`, `R_ρ f_W(a,c) = D^{-1/2} (ρ * φ_{κ_W(a)})(c)`. -/
theorem ex_closed_form_i_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    ∀ p : H × ℝ, ridgelet μ ρ (gaussianTarget W) p =
      (((Real.sqrt (fredholmDet (S * W * S)))⁻¹ * gaussianSmooth ρ (gaussianKappa S W p.1) p.2 :
        ℝ) : ℂ) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  In particular
`f_W ∈ 𝒟_α` for every `α > 0`. -/
theorem ex_closed_form_i_c (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (W S : H →L[ℝ] H)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hWi : Function.Injective W)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    MemSpectralCore μ (gaussianMixture N α) (gaussianTarget W) := by
  sorry

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  `f_W` is not
cylindrical when `W` has infinite rank. -/
theorem ex_closed_form_i_d (W : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hrank : HasInfiniteRank (W : H →ₗ[ℝ] H)) :
    ¬ IsCylindrical (gaussianTarget W) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  For every
band-pass `ρ`, the density `G = 𝒢_Q f_W` is regular along rays. -/
theorem ex_closed_form_ii_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      IsRegularAlongRays (gaussianMixture N α) I (gaussFourier μ (gaussianTarget W)) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  The image
`T_α f_W` is represented by the bounded continuous function `g_G`, `G = 𝒢_Q f_W`:
`T_α f_W [g] = ∫ g_G(x) conj(g(x)) μ_Q(dx)` for `g ∈ 𝒟_α`. -/
theorem ex_closed_form_ii_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (W S : H →L[ℝ] H)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hWi : Function.Injective W)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    ∀ fW : spectralCore μ (gaussianMixture N α), (fW : H → ℂ) =ᵐ[μ] gaussianTarget W →
      ∀ g : spectralCore μ (gaussianMixture N α),
        frameOperator μ (gaussianMixture N α) (spectralEmbed μ (gaussianMixture N α) fW)
            (spectralEmbed μ (gaussianMixture N α) g) =
          ∫ x, spectralTarget (gaussianMixture N α) (gaussFourier μ (gaussianTarget W)) x *
            (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  With
`S_W = Q^{1/2}(I+M)⁻¹Q^{1/2}`, `R = P^{1/2}`, and
`Σ_s = 2s P^{1/2}(I + 2s P^{1/2} S_W P^{1/2})⁻¹ P^{1/2}`, the representing function is
`g_G(x) = D^{-1/2} ∫₀^∞ det(I + 2s P^{1/2} S_W P^{1/2})^{-1/2} exp(-½⟨Σ_s x,x⟩) s^{α/2-1} ds`
(`eq:filtered-gaussian-target`). -/
theorem ex_closed_form_ii_c (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (W S R : H →L[ℝ] H)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hWi : Function.Injective W)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) (hR : IsPositiveSqrt R P) :
    ∀ x : H, spectralTarget (gaussianMixture N α) (gaussFourier μ (gaussianTarget W)) x =
      (((Real.sqrt (fredholmDet (S * W * S)))⁻¹ : ℝ) : ℂ) *
        ∫ s in Set.Ioi (0 : ℝ),
          (((Real.sqrt (fredholmDet ((2 * s) • (R * gaussianTargetResolvent S W * R))))⁻¹ *
            Real.exp (-⟪mixtureLayerCovariance R (gaussianTargetResolvent S W) s x, x⟫ / 2) *
            s ^ (α / 2 - 1) : ℝ) : ℂ) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  The ridgelet
coefficient of `f_W` is the coefficient `γ_G` of its density `G = 𝒢_Q f_W`:
`R_ρ f_W = γ_G`. -/
theorem ex_closed_form_iii_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    ridgelet μ ρ (gaussianTarget W) = coefficientFormula ρ (gaussFourier μ (gaussianTarget W)) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  The ridgelet
coefficient `R_ρ f_W` has finite variation and second moment:
`∫ (1 + ‖a‖² + |c|²) |R_ρ f_W(a,c)| λ_α(da,dc) < ∞`. -/
theorem ex_closed_form_iii_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    Integrable (fun p : H × ℝ => (1 + ‖p.1‖ ^ 2 + |p.2| ^ 2) * ‖ridgelet μ ρ (gaussianTarget W) p‖)
      (parameterMeasure (gaussianMixture N α)) := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  For every
real, globally Lipschitz, non-polynomial `β` (including ReLU), the integral network
`S_β[R_ρ f_W λ_α]` equals `C^{(α)}_{β,ρ} g_G`. -/
theorem ex_closed_form_iii_c (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S))
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b) {L : ℝ≥0}
    (hb : LipschitzWith L b) (hbp : ¬ IsPolynomialFun b) :
    integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure (gaussianMixture N α))
        (ridgelet μ ρ (gaussianTarget W)) =
      fun x => temperedAdmissibilityConst α β ρ *
        spectralTarget (gaussianMixture N α) (gaussFourier μ (gaussianTarget W)) x := by
  sorry

/-- **Example [ex:closed-form]** Closed-form transform and its filtered network.  For every
real, globally Lipschitz, non-polynomial `β`, the sampled network of `R_ρ f_W λ_α` converges
to `C^{(α)}_{β,ρ} g_G` at the rate `n^{-1/2}` in `C(K)`, as in `eq:spectral-barron`:
`E‖f_n - C g_G‖_{C(K)} ≤ 8V n^{-1/2} (|β(0)| + Lip(β) R_K M₂)`. -/
theorem ex_closed_form_iii_d (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (W S : H →L[ℝ] H) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hWi : Function.Injective W) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S))
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ) (hβ : IsTemperedFunction β b) {L : ℝ≥0}
    (hb : LipschitzWith L b) (hbp : ¬ IsPolynomialFun b) (K : Set H) (hK : IsCompact K)
    (n : ℕ) (hn : 0 < n) :
    ∫⁻ θ, ENNReal.ofReal (Examples.supNormOn K fun x =>
        Examples.polarSample b (parameterMeasure (gaussianMixture N α))
            (ridgelet μ ρ (gaussianTarget W)) θ x -
          temperedAdmissibilityConst α β ρ *
            spectralTarget (gaussianMixture N α) (gaussFourier μ (gaussianTarget W)) x)
        ∂(Measure.pi fun _ : Fin n =>
          Examples.normalizedLaw (parameterMeasure (gaussianMixture N α))
            (ridgelet μ ρ (gaussianTarget W))) ≤
      ENNReal.ofReal (8 * (∫ p, ‖ridgelet μ ρ (gaussianTarget W) p‖
          ∂parameterMeasure (gaussianMixture N α)) / Real.sqrt n *
        (|b 0| + L * Examples.compactRadius K *
          Real.sqrt (Examples.secondMoment
            (Examples.normalizedLaw (parameterMeasure (gaussianMixture N α))
              (ridgelet μ ρ (gaussianTarget W)))))) := by
  sorry

/-! ### Example `ex:core-elements`, second and third claims -/

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The non-cylindrical Gaussian target
`f_W` of Example `ex:closed-form` belongs to `𝒟_α` for every `α > 0`. -/
theorem ex_core_elements_iv (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (W S : H →L[ℝ] H)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hWi : Function.Injective W)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) :
    MemSpectralCore μ (gaussianMixture N α) (gaussianTarget W) := by
  sorry

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The components `F_φ` of the
neural-operator layers with Gaussian activation of Example `ex:operator-layer` belong to `𝒟_α`
for every `α > 0`. -/
theorem ex_core_elements_v (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] [SecondCountableTopology Y] {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) :
    MemSpectralCore μ (gaussianMixture N α) (layerObservable m a b gaussianAct φ) := by
  sorry

/-! ### Example `ex:gaussian-parameter` -/

/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.
`F_Q(x) = ∫ ReLU(⟨a,x⟩) 𝒩(0,Q)(da) = √(⟨Qx,x⟩/2π)`. -/
theorem ex_gaussian_parameter_i {Q : H →L[ℝ] H} (e : HilbertBasis ℕ ℝ H) (q : ℕ → ℝ)
    (hq : ∀ j, 0 < q j) (hqs : Summable q) (hQe : ∀ j, Q (e j) = q j • e j) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    ∀ x : H, gaussianParameterReLU μ x = Real.sqrt (⟪Q x, x⟫ / (2 * Real.pi)) := by
  sorry

/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.
`Φ_Q(x) = ∫ Φ(⟨a,x⟩) 𝒩(0,Q)(da) = (1 + ⟨Qx,x⟩)^{-1/2}`. -/
theorem ex_gaussian_parameter_ii {Q : H →L[ℝ] H} (e : HilbertBasis ℕ ℝ H) (q : ℕ → ℝ)
    (hq : ∀ j, 0 < q j) (hqs : Summable q) (hQe : ∀ j, Q (e j) = q j • e j) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    ∀ x : H, gaussianParameterGauss μ x = (Real.sqrt (1 + ⟪Q x, x⟫))⁻¹ := by
  sorry

/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.
`Φ_Q(x) = ∫∫ ReLU(⟨a,x⟩ - b) φ''(b) 𝒩(0,Q)(da) db` with `φ''(b) = (b² - 1) e^{-b²/2}`. -/
theorem ex_gaussian_parameter_iii {Q : H →L[ℝ] H} (e : HilbertBasis ℕ ℝ H) (q : ℕ → ℝ)
    (hq : ∀ j, 0 < q j) (hqs : Summable q) (hQe : ∀ j, Q (e j) = q j • e j) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    ∀ x : H, gaussianParameterGauss μ x =
      ∫ p : H × ℝ, relu (⟪p.1, x⟫ - p.2) * gaussianActDeriv2 p.2 ∂(μ.prod volume) := by
  sorry

/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.
`F_Q` is not cylindrical. -/
theorem ex_gaussian_parameter_iv {Q : H →L[ℝ] H} (e : HilbertBasis ℕ ℝ H) (q : ℕ → ℝ)
    (hq : ∀ j, 0 < q j) (hqs : Summable q) (hQe : ∀ j, Q (e j) = q j • e j) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    ¬ IsCylindrical (gaussianParameterReLU μ) := by
  sorry

/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.
`Φ_Q` is not cylindrical. -/
theorem ex_gaussian_parameter_v {Q : H →L[ℝ] H} (e : HilbertBasis ℕ ℝ H) (q : ℕ → ℝ)
    (hq : ∀ j, 0 < q j) (hqs : Summable q) (hQe : ∀ j, Q (e j) = q j • e j) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    ¬ IsCylindrical (gaussianParameterGauss μ) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.  A
Gaussian-activation network with finite coefficient measure `γ λ` (with all parameter moments
finite) is the ReLU network with the coefficient measure `Γ' = (a,c,b) ↦ (a, c-b)`-pushforward
of `φ''(b) γ(a,c) λ(da,dc) db`. -/
theorem ex_gaussian_parameter_vi_a {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (lam : Measure (H × ℝ)) [SigmaFinite lam] (γ : H × ℝ → Y)
    (hγ : Integrable γ lam)
    (hmom : ∀ k : ℕ, Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ k * ‖γ θ‖) lam) :
    integralNetworkDensity (fun t => (gaussianAct t : ℂ)) lam γ =
      integralNetwork (fun t => (relu t : ℂ)) (hingeCoefficientMeasure lam γ) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.  The
ReLU coefficient measure `Γ'` of a Gaussian-activation network with finite coefficient measure
is finite. -/
theorem ex_gaussian_parameter_vi_b {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (lam : Measure (H × ℝ)) [SigmaFinite lam] (γ : H × ℝ → Y)
    (hγ : Integrable γ lam)
    (hmom : ∀ k : ℕ, Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ k * ‖γ θ‖) lam) :
    IsFiniteMeasure (hingeCoefficientMeasure lam γ).variation := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Example [ex:gaussian-parameter]** ReLU and Gaussian networks with Gaussian parameters.  The
ReLU coefficient measure `Γ'` of a Gaussian-activation network with finite coefficient measure
has all parameter moments finite. -/
theorem ex_gaussian_parameter_vi_c {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (lam : Measure (H × ℝ)) [SigmaFinite lam] (γ : H × ℝ → Y)
    (hγ : Integrable γ lam)
    (hmom : ∀ k : ℕ, Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ k * ‖γ θ‖) lam) :
    ∀ k : ℕ, ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ k)
      ∂(hingeCoefficientMeasure lam γ).variation < ⊤ := by
  sorry

/-! ### Corollary `cor:relu-discretization` -/

/-- **Corollary [cor:relu-discretization]** Discretization of the Gaussian-parameter ReLU
network.  For `a_1, …, a_n` independent with law `𝒩(0,Q)` and
`F_{Q,n}(x) = n⁻¹ ∑_j ReLU(⟨a_j,x⟩)`, every compact `K ⊆ H` satisfies
`E‖F_{Q,n} - F_Q‖_{C(K)} ≤ 8 R_K √(tr Q) / √n`. -/
theorem cor_relu_discretization {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (K : Set H) (hK : IsCompact K)
    (n : ℕ) (hn : 0 < n) :
    ∫⁻ a, ENNReal.ofReal (Examples.supNormOn K fun x =>
        Examples.gaussianReLUSample a x - gaussianParameterReLU μ x)
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      ENNReal.ofReal
        (8 * Examples.compactRadius K * Real.sqrt (traceOf Q) / Real.sqrt n) := by
  sorry

/-! ### Example `ex:operator-layer` -/

section OperatorLayer

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Network
structure: `ℱ = S_β[Γ]` with the `Y`-valued measure `Γ = ι_#(b_y m(dy))`, `ι(y) = (a_y, 0)`. -/
theorem ex_operator_layer_i_a (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (β : ℝ → ℝ) (hβc : Continuous β) (hβp : HasPolynomialGrowth β) :
    operatorLayer m a b β = integralNetwork (fun t => (β t : ℂ)) (layerMeasure m a b) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The total
variation of `Γ` is at most `∫ ‖b_y‖ m(dy)`. -/
theorem ex_operator_layer_i_b (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    totalVariation (layerMeasure m a b) ≤ ∫⁻ y, ‖b y‖ₑ ∂m := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The second
parameter moment of `Γ` is at most `‖A‖_∞²`: `∫ (‖a‖² + c²) d|Γ| ≤ ‖A‖_∞² ‖Γ‖_TV`. -/
theorem ex_operator_layer_i_c (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    ∫⁻ θ : H × ℝ, ENNReal.ofReal (‖θ.1‖ ^ 2 + |θ.2| ^ 2) ∂(layerMeasure m a b).variation ≤
      ENNReal.ofReal (layerSupNorm a ^ 2) * totalVariation (layerMeasure m a b) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Hence
Corollary `cor:vector-rates` gives width-`n` networks approximating `ℱ` at the rate `n^{-1/2}` in
`L²(ζ;Y)`: for globally Lipschitz `β`, the sampled layer of `‖b_y‖ m(dy)/V`, `V = ∫ ‖b_y‖ m(dy)`,
satisfies `E‖f_n - ℱ‖²_{L²(ζ;Y)} ≤ 2V² n⁻¹ (|β(0)|² + Lip(β)² (1 + ∫‖x‖² dζ) ‖A‖_∞²)`. -/
theorem ex_operator_layer_i_d (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (β : ℝ → ℝ) {L : ℝ≥0} (hβ : LipschitzWith L β) (ζ : Measure H)
    [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ) (n : ℕ) (hn : 0 < n) :
    ∫⁻ y, ENNReal.ofReal (∫ x, ‖Examples.layerSampleVec m a b β y x - operatorLayer m a b β x‖ ^ 2
        ∂ζ) ∂(Measure.pi fun _ : Fin n => Examples.normalizedLaw m b) ≤
      ENNReal.ofReal (2 * (∫ y, ‖b y‖ ∂m) ^ 2 / n *
        (|β 0| ^ 2 + (L : ℝ) ^ 2 * (1 + ∫ x, ‖x‖ ^ 2 ∂ζ) * layerSupNorm a ^ 2)) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  For each
`φ ∈ Y` and globally Lipschitz `β`, Theorem `thm:lipschitz-barron` gives for the sampled
observable `E‖F_{φ,n} - F_φ‖_{C(K)} ≤ 8 ‖w_φ‖_{L¹(m)} n^{-1/2} (|β(0)| + Lip(β) R_K ‖A‖_∞)`. -/
theorem ex_operator_layer_i_e (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (β : ℝ → ℝ) {L : ℝ≥0} (hβ : LipschitzWith L β) (φ : Y) (K : Set H)
    (hK : IsCompact K) (n : ℕ) (hn : 0 < n) :
    ∫⁻ y, ENNReal.ofReal (Examples.supNormOn K fun x =>
        Examples.layerSampleScalar m a (layerWeight b φ) β y x - layerObservable m a b β φ x)
        ∂(Measure.pi fun _ : Fin n => Examples.normalizedLaw m (layerWeight b φ)) ≤
      ENNReal.ofReal (8 * (∫ y, ‖layerWeight b φ y‖ ∂m) / Real.sqrt n *
        (|β 0| + L * Examples.compactRadius K * layerSupNorm a)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation `β = Φ`: `F_φ ∈ 𝒟_α` for every `α > 0`. -/
theorem ex_operator_layer_ii_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (m : Measure Ω) [IsFiniteMeasure m]
    (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) (φ : Y) :
    MemSpectralCore μ (gaussianMixture N α) (layerObservable m a b gaussianAct φ) := by
  sorry

omit [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: with `σ_y² = ⟨Qa_y,a_y⟩` and `S_y = Q - (1+σ_y²)⁻¹ (Qa_y) ⊗ (Qa_y)`,
`𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟨S_yξ,ξ⟩/2} m(dy)` (`eq:operator-layer-transform`). -/
theorem ex_operator_layer_ii_b {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (m : Measure Ω) [IsFiniteMeasure m]
    (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) (φ : Y) :
    ∀ ξ : H, gaussFourier μ (layerObservable m a b gaussianAct φ) ξ =
      ∫ y, layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) ∂m := by
  sorry

omit [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: for every band-pass `ρ`,
`R_ρ F_φ(a,c) = ∫ w_φ(y) (1+σ_y²)^{-1/2} (ρ * φ_{⟨S_ya,a⟩})(c) m(dy)`
(`eq:operator-layer-transform`). -/
theorem ex_operator_layer_ii_c {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) :
    ∀ p : H × ℝ, ridgelet μ ρ (layerObservable m a b gaussianAct φ) p =
      ∫ y, layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        gaussianSmooth ρ ⟪layerCovariance Q a y p.1, p.1⟫ p.2 : ℝ) : ℂ) ∂m := by
  sorry

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: `S_y ≥ (1 + ‖Q‖ ‖A‖_∞²)⁻¹ Q`. -/
theorem ex_operator_layer_ii_d {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (m : Measure Ω)
    [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) :
    ∀ (y : Ω) (ξ : H),
      (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ ≤ ⟪layerCovariance Q a y ξ, ξ⟫ := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: consequently `𝒢_Q F_φ` is regular along rays, for every band-pass `ρ`. -/
theorem ex_operator_layer_ii_e (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) :
    ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      IsRegularAlongRays (gaussianMixture N α) I
        (gaussFourier μ (layerObservable m a b gaussianAct φ)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: the reconstruction formulas of Theorem `thm:C` hold for `F_φ`; in particular
`T_α F_φ` is represented by `g_G`, `G = 𝒢_Q F_φ`: `T_α F_φ [g] = ∫ g_G(x) conj(g(x)) μ_Q(dx)`
for `g ∈ 𝒟_α`. -/
theorem ex_operator_layer_ii_f (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (m : Measure Ω) [IsFiniteMeasure m]
    (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) (φ : Y) :
    ∀ F : spectralCore μ (gaussianMixture N α),
      (F : H → ℂ) =ᵐ[μ] layerObservable m a b gaussianAct φ →
      ∀ g : spectralCore μ (gaussianMixture N α),
        frameOperator μ (gaussianMixture N α) (spectralEmbed μ (gaussianMixture N α) F)
            (spectralEmbed μ (gaussianMixture N α) g) =
          ∫ x, spectralTarget (gaussianMixture N α)
              (gaussFourier μ (layerObservable m a b gaussianAct φ)) x *
            (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  sorry

omit [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: the ridgelet coefficient of `F_φ` is the coefficient `γ_G` of `G = 𝒢_Q F_φ`. -/
theorem ex_operator_layer_ii_g {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) :
    ridgelet μ ρ (layerObservable m a b gaussianAct φ) =
      coefficientFormula ρ (gaussFourier μ (layerObservable m a b gaussianAct φ)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: the ridgelet coefficient `R_ρ F_φ` has finite variation and moments,
`∫ (1 + ‖a‖² + |c|²) |R_ρ F_φ(a,c)| λ_α(da,dc) < ∞`. -/
theorem ex_operator_layer_ii_h (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) :
    Integrable (fun p : H × ℝ =>
        (1 + ‖p.1‖ ^ 2 + |p.2| ^ 2) * ‖ridgelet μ ρ (layerObservable m a b gaussianAct φ) p‖)
      (parameterMeasure (gaussianMixture N α)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: the ridgelet coefficient `R_ρ F_φ` synthesizes, with any real Lipschitz
non-polynomial `β'`, the target `C^{(α)}_{β',ρ} T_α F_φ` (represented by `g_G`). -/
theorem ex_operator_layer_ii_i (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) (β' : TemperedDistribution ℝ ℂ) (b' : ℝ → ℝ)
    (hβ' : IsTemperedFunction β' b') {L : ℝ≥0} (hb' : LipschitzWith L b')
    (hb'p : ¬ IsPolynomialFun b') :
    integralNetworkDensity (fun t => (b' t : ℂ)) (parameterMeasure (gaussianMixture N α))
        (ridgelet μ ρ (layerObservable m a b gaussianAct φ)) =
      fun x => temperedAdmissibilityConst α β' ρ *
        spectralTarget (gaussianMixture N α)
          (gaussFourier μ (layerObservable m a b gaussianAct φ)) x := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  Gaussian
activation: the sampled network of `R_ρ F_φ λ_α` with a real Lipschitz non-polynomial `β'`
converges to `C^{(α)}_{β',ρ} g_G` at the finite-width rate of `eq:spectral-barron`. -/
theorem ex_operator_layer_ii_j (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) (β' : TemperedDistribution ℝ ℂ) (b' : ℝ → ℝ)
    (hβ' : IsTemperedFunction β' b') {L : ℝ≥0} (hb' : LipschitzWith L b')
    (hb'p : ¬ IsPolynomialFun b') (K : Set H) (hK : IsCompact K) (n : ℕ) (hn : 0 < n) :
    ∫⁻ θ, ENNReal.ofReal (Examples.supNormOn K fun x =>
        Examples.polarSample b' (parameterMeasure (gaussianMixture N α))
            (ridgelet μ ρ (layerObservable m a b gaussianAct φ)) θ x -
          temperedAdmissibilityConst α β' ρ *
            spectralTarget (gaussianMixture N α)
              (gaussFourier μ (layerObservable m a b gaussianAct φ)) x)
        ∂(Measure.pi fun _ : Fin n =>
          Examples.normalizedLaw (parameterMeasure (gaussianMixture N α))
            (ridgelet μ ρ (layerObservable m a b gaussianAct φ))) ≤
      ENNReal.ofReal (8 * (∫ p, ‖ridgelet μ ρ (layerObservable m a b gaussianAct φ) p‖
          ∂parameterMeasure (gaussianMixture N α)) / Real.sqrt n *
        (|b' 0| + L * Examples.compactRadius K *
          Real.sqrt (Examples.secondMoment
            (Examples.normalizedLaw (parameterMeasure (gaussianMixture N α))
              (ridgelet μ ρ (layerObservable m a b gaussianAct φ)))))) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target: `ℱ ∈ 𝒟_α(Y)` for every `α > 0`. -/
theorem ex_operator_layer_ii_k (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (m : Measure Ω) [IsFiniteMeasure m]
    (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) :
    MemSpectralCoreVec μ (gaussianMixture N α) (operatorLayer m a b gaussianAct) := by
  sorry

omit [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target:
`𝒢_Q ℱ(ξ) = ∫ (1+σ_y²)^{-1/2} e^{-⟨S_yξ,ξ⟩/2} b_y m(dy)`. -/
theorem ex_operator_layer_ii_l {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (m : Measure Ω) [IsFiniteMeasure m]
    (a : Ω → H) (b : Ω → Y) (hL : IsLayerData m a b) :
    ∀ ξ : H, gaussFourierVec μ (operatorLayer m a b gaussianAct) ξ =
      ∫ y, (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
        Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) • b y ∂m := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target: `𝒢_Q ℱ` is regular along rays for every band-pass
`ρ`. -/
theorem ex_operator_layer_ii_m (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      IsRegularAlongRays (gaussianMixture N α) I
        (gaussFourierVec μ (operatorLayer m a b gaussianAct)) := by
  sorry

omit [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target: `R_ρ ℱ = γ_{𝒢_Q ℱ}` for every band-pass `ρ`. -/
theorem ex_operator_layer_ii_n {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    ridgeletVec μ ρ (operatorLayer m a b gaussianAct) =
      coefficientFormulaVec ρ (gaussFourierVec μ (operatorLayer m a b gaussianAct)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target: `R_ρ ℱ` has finite variation and moments. -/
theorem ex_operator_layer_ii_o (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    Integrable (fun p : H × ℝ =>
        (1 + ‖p.1‖ ^ 2 + |p.2| ^ 2) * ‖ridgeletVec μ ρ (operatorLayer m a b gaussianAct) p‖)
      (parameterMeasure (gaussianMixture N α)) := by
  sorry

/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  The same
holds for `ℱ` itself as a `Y`-valued target: `R_ρ ℱ` synthesizes, with any real Lipschitz
non-polynomial `β'`, the `Y`-valued target `C^{(α)}_{β',ρ} g_{𝒢_Q ℱ}`. -/
theorem ex_operator_layer_ii_p (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (β' : TemperedDistribution ℝ ℂ) (b' : ℝ → ℝ)
    (hβ' : IsTemperedFunction β' b') {L : ℝ≥0} (hb' : LipschitzWith L b')
    (hb'p : ¬ IsPolynomialFun b') :
    integralNetworkDensity (fun t => (b' t : ℂ)) (parameterMeasure (gaussianMixture N α))
        (ridgeletVec μ ρ (operatorLayer m a b gaussianAct)) =
      fun x => temperedAdmissibilityConst α β' ρ •
        spectralTarget (gaussianMixture N α)
          (gaussFourierVec μ (operatorLayer m a b gaussianAct)) x := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  ReLU form:
by `eq:gaussian-parameter-closed-forms`, the Gaussian-activation layer is
`ℱ(x) = ∫∫ b_y φ''(b) ReLU(⟨a_y,x⟩ - b) m(dy) db`. -/
theorem ex_operator_layer_iii_a (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    ∀ x : H, operatorLayer m a b gaussianAct x =
      ∫ p : Ω × ℝ, ((gaussianActDeriv2 p.2 * relu (⟪a p.1, x⟫ - p.2) : ℝ) : ℂ) • b p.1
        ∂(m.prod volume) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  ReLU form:
the Gaussian-activation layer is the ReLU network with the coefficient measure
`(y,b) ↦ (a_y, -b)`-pushforward of `φ''(b) b_y m(dy) db`. -/
theorem ex_operator_layer_iii_b (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    operatorLayer m a b gaussianAct =
      integralNetwork (fun t => (relu t : ℂ)) (layerHingeMeasure m a b) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  ReLU form:
the ReLU coefficient measure is finite. -/
theorem ex_operator_layer_iii_c (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    IsFiniteMeasure (layerHingeMeasure m a b).variation := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.  ReLU form:
the ReLU coefficient measure has all moments finite. -/
theorem ex_operator_layer_iii_d (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) :
    ∀ k : ℕ, ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ k)
      ∂(layerHingeMeasure m a b).variation < ⊤ := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology Y] in
/-- **Example [ex:operator-layer]** Neural-operator layer as an integral network.
Non-cylindricity: if `A` has infinite rank, `β = Φ`, and `w_φ > 0` `m`-almost everywhere, then
`F_φ` is not cylindrical. -/
theorem ex_operator_layer_iv (m : Measure Ω) [IsFiniteMeasure m] (a : Ω → H) (b : Ω → Y)
    (hL : IsLayerData m a b) (φ : Y) (hA : HasInfiniteRank (layerA m a))
    (hw : ∀ᵐ y ∂m, 0 < (layerWeight b φ y).re ∧ (layerWeight b φ y).im = 0) :
    ¬ IsCylindrical (layerObservable m a b gaussianAct φ) := by
  sorry

end OperatorLayer

/-! ### Example `ex:convolution` -/

section Convolution

/-- **Example [ex:convolution]** Periodic convolution layer.  With `a_y = k(y - ·)`,
`⟨a_y, x⟩ = (k * x)(y)`. -/
theorem ex_convolution_i (d : ℕ) (k : TorusL2 d) :
    ∀ (x : TorusL2 d) (y : Torus d),
      ⟪convDirection k y, x⟫ = ∫ t, k (y - t) * x t ∂torusHaar d := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  With `a_y = k(y - ·)` and
`b_y = ψ(· - y)`, the layer is `ℱ(x) = ψ * β(k * x)`. -/
theorem ex_convolution_ii (d : ℕ) (k ψ : TorusL2 d) (β : ℝ → ℝ) (hβc : Continuous β)
    (hβp : HasPolynomialGrowth β) :
    ∀ x : TorusL2 d,
      ⇑(operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x)
        =ᵐ[torusHaar d] fun t =>
          ∫ y, ((ψ (t - y) * β ⟪convDirection k y, x⟫ : ℝ) : ℂ) ∂torusHaar d := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  `‖A‖_∞ = ‖k‖₂`. -/
theorem ex_convolution_iii (d : ℕ) (k : TorusL2 d) :
    layerSupNorm (convDirection k) = ‖k‖ := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  `∫ ‖b_y‖ dy = ‖ψ‖₂`. -/
theorem ex_convolution_iv (d : ℕ) (ψ : TorusL2 d) :
    ∫ y, ‖convOutput ψ y‖ ∂torusHaar d = ‖ψ‖ := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  The convolution layer satisfies the
standing hypotheses of the neural-operator layer (`y ↦ a_y`, `y ↦ b_y` are continuous and
bounded into `L²`), so Example `ex:operator-layer` applies. -/
theorem ex_convolution_v (d : ℕ) (k ψ : TorusL2 d) :
    IsLayerData (torusHaar d) (convDirection k) (convOutput ψ) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  `ℱ` commutes with all translations
of `𝕋^d`: `ℱ(τ_z x) = τ_z ℱ(x)`. -/
theorem ex_convolution_vi (d : ℕ) (k ψ : TorusL2 d) (β : ℝ → ℝ) (hβc : Continuous β)
    (hβp : HasPolynomialGrowth β) :
    ∀ (z : Torus d) (x : TorusL2 d),
      operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β (torusTranslate d z x) =
        torusTranslateC d z
          (operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  `ℱ` commutes with every isometry
`σ` of `𝕋^d` (an isometric automorphism of the group, measure preserving) that fixes `k` and
`ψ`: `ℱ(x ∘ σ) = ℱ(x) ∘ σ`. -/
theorem ex_convolution_vii (d : ℕ) (k ψ : TorusL2 d) (β : ℝ → ℝ) (hβc : Continuous β)
    (hβp : HasPolynomialGrowth β) :
    ∀ (σ : Torus d ≃+ Torus d), Isometry σ →
      ∀ hσ : MeasurePreserving σ (torusHaar d) (torusHaar d),
        (fun t => k (σ t)) =ᵐ[torusHaar d] k → (fun t => ψ (σ t)) =ᵐ[torusHaar d] ψ →
        ∀ x : TorusL2 d,
          operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β
              (Lp.compMeasurePreserving σ hσ x) =
            Lp.compMeasurePreserving σ hσ
              (operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  If `k̂(n) ≠ 0` for infinitely many
`n ∈ ℤ^d`, then `A` has infinite rank. -/
theorem ex_convolution_viii (d : ℕ) (k : TorusL2 d)
    (hk : Set.Infinite {n : Fin d → ℤ | torusFourierCoeff (fun t => (k t : ℂ)) n ≠ 0}) :
    HasInfiniteRank (layerA (torusHaar d) (convDirection k)) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  With `φ ≡ 1` the observable is
`F_1(x) = ψ̂(0) ∫ β((k * x)(y)) dy`. -/
theorem ex_convolution_ix (d : ℕ) (k ψ : TorusL2 d) (β : ℝ → ℝ) (hβc : Continuous β)
    (hβp : HasPolynomialGrowth β) :
    ∀ x : TorusL2 d,
      layerObservable (torusHaar d) (convDirection k) (convOutput ψ) β (torusOne d) x =
        torusFourierCoeff (fun t => (ψ t : ℂ)) 0 *
          ∫ y, ((β ⟪convDirection k y, x⟫ : ℝ) : ℂ) ∂torusHaar d := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  If `k̂(n) ≠ 0` for infinitely many
`n` and `ψ̂(0) ≠ 0`, then the observable `F_1` of the Gaussian-activation layer is not
cylindrical. -/
theorem ex_convolution_x (d : ℕ) (k ψ : TorusL2 d)
    (hk : Set.Infinite {n : Fin d → ℤ | torusFourierCoeff (fun t => (k t : ℂ)) n ≠ 0})
    (hψ : torusFourierCoeff (fun t => (ψ t : ℂ)) 0 ≠ 0) :
    ¬ IsCylindrical
      (layerObservable (torusHaar d) (convDirection k) (convOutput ψ) gaussianAct
        (torusOne d)) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  For `s > d/2`, the operator
`(I - Δ)^{-s}` is injective, positive, self-adjoint, and trace class. -/
theorem ex_convolution_xi (d : ℕ) (s : ℝ) (hs : (d : ℝ) / 2 < s) :
    IsTraceClassCovariance (besselOperator d s) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  `(I - Δ)^{-s}` is translation
invariant: `(I - Δ)^{-s} τ_z = τ_z (I - Δ)^{-s}`. -/
theorem ex_convolution_xii (d : ℕ) (s : ℝ) (hs : (d : ℝ) / 2 < s) :
    ∀ (z : Torus d) (x : TorusL2 d),
      besselOperator d s (torusTranslate d z x) = torusTranslate d z (besselOperator d s x) := by
  sorry

/-- **Example [ex:convolution]** Periodic convolution layer.  With `Q = P = (I - Δ)^{-s}`,
`s > d/2`, the transform is equivariant: `R_ρ[f ∘ τ_z](a,c) = R_ρ f(τ_z a, c)` for every
translation `τ_z` and every `f ∈ L¹(μ_Q)`. -/
theorem ex_convolution_xiii (d : ℕ) (s : ℝ) (hs : (d : ℝ) / 2 < s)
    [MeasurableSpace (TorusL2 d)] [BorelSpace (TorusL2 d)] (μ : Measure (TorusL2 d))
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian (besselOperator d s) μ)
    (ρ : SchwartzMap ℝ ℝ) (f : TorusL2 d → ℂ) (hf : Integrable f μ) :
    ∀ (z : Torus d) (p : TorusL2 d × ℝ),
      ridgelet μ ρ (fun x => f (torusTranslate d z x)) p =
        ridgelet μ ρ f (torusTranslate d z p.1, p.2) := by
  sorry

end Convolution

/-! ### Example `ex:dirichlet` -/

section Dirichlet

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  `𝖦` is
the integral operator with kernel `g`: `(𝖦x)(y) = ∫₀¹ g(y,t) x(t) dt`. -/
theorem ex_dirichlet_i :
    ∀ x : UnitL2, (dirichletOperator x : UnitOpenInterval → ℝ) =ᵐ[volume]
      fun y : UnitOpenInterval => ∫ t : UnitOpenInterval, dirichletKernel y t * x t := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  For a
continuous source `x`, `u = 𝖦x` solves `-u'' + u = x` on `(0,1)` with `u(0) = u(1) = 0`. -/
theorem ex_dirichlet_ii (x : ℝ → ℝ) (hx : Continuous x) :
    dirichletSolution x 0 = 0 ∧ dirichletSolution x 1 = 0 ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (dirichletSolution x) y) ∧
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (deriv (dirichletSolution x)) (dirichletSolution x y - x y) y := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  `𝖦` has
the eigenpairs `λ_n = (1 + π²n²)⁻¹`, `e_n(t) = √2 sin(nπt)`, `n ≥ 1`. -/
theorem ex_dirichlet_iii :
    ∀ n : ℕ, 1 ≤ n →
      dirichletOperator (dirichletEigenfunction n) =
        dirichletEigenvalue n • dirichletEigenfunction n := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  `𝖦` is
injective, positive, self-adjoint, and trace class. -/
theorem ex_dirichlet_iv : IsTraceClassCovariance dirichletOperator := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  `𝖦` has
infinite rank. -/
theorem ex_dirichlet_v : HasInfiniteRank (dirichletOperator : UnitL2 →ₗ[ℝ] UnitL2) := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.
`‖A‖_∞ ≤ sup_y ‖g(y,·)‖₂ < ∞`: the directions `a_y = g(y,·)` are bounded in `L²(0,1)`. -/
theorem ex_dirichlet_vi :
    BddAbove (Set.range fun y : UnitOpenInterval => ‖dirichletDirection y‖) := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  With
`a_y = b_y = g(y,·)` the standing hypotheses of the neural-operator layer hold, so Example
`ex:operator-layer` applies. -/
theorem ex_dirichlet_vii : IsLayerData volume dirichletDirection dirichletOutput := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  With
`a_y = b_y = g(y,·)` the layer is `ℱ(x) = 𝖦 β(𝖦x)`. -/
theorem ex_dirichlet_viii (β : ℝ → ℝ) (hβc : Continuous β) (hβp : HasPolynomialGrowth β) :
    ∀ x : UnitL2, operatorLayer volume dirichletDirection dirichletOutput β x =
      Complex.ofRealCLM.compLp
        (dirichletOperator (toLpOrZero 2 volume fun t => β (dirichletOperator x t))) := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  `𝖦` is
the exact ReLU network `𝖦x = ∑_n λ_n e_n [ReLU(⟨e_n,x⟩) - ReLU(-⟨e_n,x⟩)]`. -/
theorem ex_dirichlet_ix :
    ∀ x : UnitL2, HasSum
      (fun n : ℕ => (dirichletEigenvalue n *
        (relu ⟪dirichletEigenfunction n, x⟫ - relu (-⟪dirichletEigenfunction n, x⟫))) •
          dirichletEigenfunction n)
      (dirichletOperator x) := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  The
`2N`-neuron truncation has error `‖𝖦x - 𝖦_N x‖ ≤ λ_{N+1} ‖x‖`, uniformly on bounded sets. -/
theorem ex_dirichlet_x :
    ∀ (n : ℕ) (x : UnitL2),
      ‖dirichletOperator x - dirichletReLUTruncation n x‖ ≤ dirichletEigenvalue (n + 1) * ‖x‖ := by
  sorry

/-- **Example [ex:dirichlet]** Dirichlet solution operator with a pointwise nonlinearity.  The
truncation error is `O(N^{-2})`: `λ_{N+1} ≤ π⁻² (N+1)⁻²`. -/
theorem ex_dirichlet_xi :
    ∀ n : ℕ, dirichletEigenvalue (n + 1) ≤ (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := by
  intro n
  unfold dirichletEigenvalue
  push_cast
  exact inv_anti₀ (by positivity) (by linarith)

end Dirichlet

end OperatorRidgelet.Paper
