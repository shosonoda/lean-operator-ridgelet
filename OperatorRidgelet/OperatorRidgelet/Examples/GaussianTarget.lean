import OperatorRidgelet.Examples.GaussianQuadratic
import OperatorRidgelet.Examples.SliceCoefficient
import OperatorRidgelet.Reconstruction.Basic

/-!
# The Gaussian target `f_W` of Example `ex:closed-form`

The Gaussian integral of a quadratic exponential (`integral_exp_quadratic`, Lemma
`lem:gaussian-quadratic`(ii)) computes the transform of the Gaussian target
`f_W(x) = e^{-⟪Wx,x⟫/2}`,
`𝒢_Q f_W(ξ) = D^{-1/2} e^{-κ_W(ξ)/2}` with `D = det(I+M)`, `M = Q^{1/2} W Q^{1/2}` and
`κ_W(ξ) = ⟪S_W ξ, ξ⟫`, `S_W = Q^{1/2}(I+M)^{-1}Q^{1/2}`
(`gaussFourier_gaussianTarget`).  The resolvent bound `S_W ≥ (1+‖M‖)^{-1} Q`
(`inner_gaussianTargetResolvent_ge`) turns this into the Gaussian decay of Lemma
`lem:gaussian-decay` and into the regularity along rays of Lemma
`lem:ray-regular-examples`(a).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

/-! ### A frequency window always exists -/

/-- The symmetrized support of `ρ̂` is a frequency window for a band-pass `ρ`. -/
theorem IsBandPass.exists_isFrequencyWindow {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) :
    ∃ I : Set ℝ, IsFrequencyWindow (⇑ρ) I := by
  classical
  refine ⟨tsupport (filterFourier ρ) ∪ -tsupport (filterFourier ρ), ?_, ?_, ?_, ?_⟩
  · exact IsCompact.union hρ.hasCompactSupport (IsCompact.neg hρ.hasCompactSupport)
  · rintro (h | h)
    · exact hρ.zero_notMem_tsupport h
    · rw [Set.mem_neg, neg_zero] at h
      exact hρ.zero_notMem_tsupport h
  · rintro ω (h | h)
    · exact Or.inr (by rwa [Set.mem_neg, neg_neg])
    · rw [Set.mem_neg] at h
      exact Or.inl h
  · exact Set.subset_union_left

/-! ### The transform of the Gaussian target -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `S_W = Q^{1/2}(I+M)^{-1}Q^{1/2}` is self-adjoint. -/
theorem isSelfAdjoint_gaussianTargetResolvent {Q W S : H →L[ℝ] H} (hW : IsSelfAdjoint W)
    (hS : IsPositiveSqrt S Q) : IsSelfAdjoint (gaussianTargetResolvent S W) := by
  have hM : IsSelfAdjoint (S * W * S) := isSelfAdjoint_sqrt_mul_mul hW hS
  have h1 : IsSelfAdjoint ((1 : H →L[ℝ] H) + S * W * S) := IsSelfAdjoint.add (IsSelfAdjoint.one _) hM
  have h2 : IsSelfAdjoint (Ring.inverse ((1 : H →L[ℝ] H) + S * W * S)) := h1.ringInverse
  show star (S * Ring.inverse (1 + S * W * S) * S) = S * Ring.inverse (1 + S * W * S) * S
  rw [star_mul, star_mul, hS.isSelfAdjoint.star_eq, h2.star_eq, ← mul_assoc]

/-- `κ_W(ξ) = ⟪S_W ξ, ξ⟫`. -/
theorem gaussianKappa_eq_inner (S W : H →L[ℝ] H) (ξ : H) :
    gaussianKappa S W ξ = ⟪gaussianTargetResolvent S W ξ, ξ⟫ := rfl

variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The resolvent bound `S_W ≥ (1 + ‖M‖)^{-1} Q`. -/
theorem inner_gaussianTargetResolvent_ge {Q W S : H →L[ℝ] H} (hW : IsSelfAdjoint W)
    (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S))
    (ξ : H) :
    (1 + ‖S * W * S‖)⁻¹ * ⟪Q ξ, ξ⟫ ≤ ⟪gaussianTargetResolvent S W ξ, ξ⟫ :=
  inner_cov_le_resolventForm hW hW0 hS hM ξ

/-- **Example `ex:closed-form`(i)**: `𝒢_Q f_W(ξ) = D^{-1/2} e^{-κ_W(ξ)/2}`. -/
theorem gaussFourier_gaussianTarget {Q W S : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hS : IsPositiveSqrt S Q)
    (hM : HasSummableTrace (S * W * S)) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (ξ : H) :
    gaussFourier μ (gaussianTarget W) ξ =
      (((Real.sqrt (fredholmDet (S * W * S)))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((gaussianKappa S W ξ / 2 : ℝ) : ℂ)) := by
  have hneg : resolventForm S (S * W * S) (-ξ) = gaussianKappa S W ξ := by
    show ⟪(S * Ring.inverse (1 + S * W * S) * S) (-ξ), -ξ⟫ = _
    rw [map_neg, inner_neg_neg]
    rfl
  rw [← hneg, ← integral_exp_quadratic hQ hW hW0 hS hM hμ (-ξ)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h1 : (⟪-ξ, x⟫ : ℝ) = -⟪x, ξ⟫ := by
    rw [inner_neg_left, real_inner_comm]
  show ((Real.exp (-⟪W x, x⟫ / 2) : ℝ) : ℂ) * Complex.exp (-((⟪x, ξ⟫ : ℝ) * Complex.I)) =
    Complex.exp (((⟪-ξ, x⟫ : ℝ) : ℂ) * Complex.I - ((⟪W x, x⟫ / 2 : ℝ) : ℂ))
  rw [Complex.ofReal_exp, ← Complex.exp_add, h1]
  congr 1
  push_cast
  ring

/-- The Gaussian target is bounded by `1`. -/
theorem norm_gaussianTarget_le_one (W : H →L[ℝ] H) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (x : H) :
    ‖gaussianTarget W x‖ ≤ 1 := by
  rw [gaussianTarget, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.exp_le_one_iff]
  linarith [hW0 x]

theorem continuous_gaussianTarget (W : H →L[ℝ] H) : Continuous (gaussianTarget W) := by
  unfold gaussianTarget
  fun_prop

theorem integrable_gaussianTarget (W : H →L[ℝ] H) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (μ : Measure H)
    [IsFiniteMeasure μ] : Integrable (gaussianTarget W) μ :=
  Integrable.of_bound (continuous_gaussianTarget W).aestronglyMeasurable 1
    (Eventually.of_forall (norm_gaussianTarget_le_one W hW0))

theorem memLp_two_gaussianTarget (W : H →L[ℝ] H) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (μ : Measure H)
    [IsFiniteMeasure μ] : MemLp (gaussianTarget W) 2 μ :=
  MemLp.of_bound (continuous_gaussianTarget W).aestronglyMeasurable 1
    (Eventually.of_forall (norm_gaussianTarget_le_one W hW0))

/-- The Gaussian decay of the transform of `f_W`. -/
theorem norm_gaussFourier_gaussianTarget_le {Q W S : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hS : IsPositiveSqrt S Q)
    (hM : HasSummableTrace (S * W * S)) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (ξ : H) :
    ‖gaussFourier μ (gaussianTarget W) ξ‖ ≤
      (Real.sqrt (fredholmDet (S * W * S)))⁻¹ *
        Real.exp (-(1 + ‖S * W * S‖)⁻¹ * ⟪Q ξ, ξ⟫ / 2) := by
  rw [gaussFourier_gaussianTarget hQ hW hW0 hS hM hμ ξ, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_exp]
  have hre : (-((gaussianKappa S W ξ / 2 : ℝ) : ℂ)).re = -(gaussianKappa S W ξ / 2) := by
    simp
  rw [hre]
  have hb := inner_gaussianTargetResolvent_ge hW hW0 hS hM ξ
  rw [← gaussianKappa_eq_inner] at hb
  have hD : (0 : ℝ) ≤ (Real.sqrt (fredholmDet (S * W * S)))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hD
  rw [Real.exp_le_exp]
  linarith

/-- The transform of `f_W` is integrable against any measure with the Gaussian decay of
Lemma `lem:gaussian-decay`(i). -/
theorem integrable_gaussFourier_gaussianTarget {Q W S : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q)
    (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫) (hS : IsPositiveSqrt S Q)
    (hM : HasSummableTrace (S * W * S)) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) {ν : Measure H}
    (hdecay : ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν) :
    Integrable (gaussFourier μ (gaussianTarget W)) ν := by
  have h0 := hdecay ((1 + ‖S * W * S‖)⁻¹ / 2) (by positivity) 0
  simp only [mul_zero, pow_zero, one_mul] at h0
  have hcont : Continuous (gaussFourier μ (gaussianTarget W)) :=
    continuous_gaussFourier μ (integrable_gaussianTarget W hW0 μ)
  refine (h0.const_mul ((Real.sqrt (fredholmDet (S * W * S)))⁻¹)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have harg : -(1 + ‖S * W * S‖)⁻¹ * ⟪Q ξ, ξ⟫ / 2 =
      -((1 + ‖S * W * S‖)⁻¹ / 2) * ⟪Q ξ, ξ⟫ := by ring
  have hb := norm_gaussFourier_gaussianTarget_le hQ hW hW0 hS hM hμ ξ
  rwa [harg] at hb

/-- **Example `ex:closed-form`(ii)**: `G = 𝒢_Q f_W` is regular along rays. -/
theorem isRegularAlongRays_gaussFourier_gaussianTarget {Q W S : H →L[ℝ] H}
    (hQ : IsPositiveTraceClass Q) (hW : IsSelfAdjoint W) (hW0 : ∀ x, 0 ≤ ⟪W x, x⟫)
    (hS : IsPositiveSqrt S Q) (hM : HasSummableTrace (S * W * S)) {μ : Measure H}
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ν : Measure H)
    (hdecay : ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν)
    {I : Set ℝ} (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) :
    IsRegularAlongRays ν I (gaussFourier μ (gaussianTarget W)) := by
  classical
  set ℓ : Fin 0 → (H →L[ℝ] ℝ) := Fin.elim0 with hℓ
  set q : MvPolynomial (Option (Fin 0)) ℂ :=
    MvPolynomial.C (((Real.sqrt (fredholmDet (S * W * S)))⁻¹ : ℝ) : ℂ) with hq
  have hfun : gaussFourier μ (gaussianTarget W) = fun ξ =>
      MvPolynomial.eval (fun o : Option (Fin 0) =>
          o.elim ((⟪gaussianTargetResolvent S W ξ, ξ⟫ : ℝ) : ℂ) fun i => ((ℓ i ξ : ℝ) : ℂ)) q *
        Complex.exp (-((⟪gaussianTargetResolvent S W ξ, ξ⟫ / 2 : ℝ) : ℂ)) := by
    funext ξ
    rw [gaussFourier_gaussianTarget hQ hW hW0 hS hM hμ ξ, hq, MvPolynomial.eval_C]
    rfl
  rw [hfun]
  exact isRegularAlongRays_of_gaussian_decay ν hQ.inner_nonneg hdecay
    (gaussianTargetResolvent S W) (θ := (1 + ‖S * W * S‖)⁻¹) (by positivity)
    (inner_gaussianTargetResolvent_ge hW hW0 hS hM) ℓ (fun i => i.elim0) q hI hI0

end OperatorRidgelet
