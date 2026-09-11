import OperatorRidgelet.Examples.GaussianTarget

/-!
# The layers of the Gaussian mixture applied to a Gaussian density

Each layer `𝒩(0,2sP)` of the mixture `ν_α` integrates the Gaussian density
`e^{-⟪Tξ,ξ⟫/2}` by Lemma `lem:gaussian-quadratic`(ii) applied with the covariance `2sP`, whose
positive square root is `√(2s) P^{1/2}`:
`∫ e^{i⟪x,ξ⟫ - ⟪Tξ,ξ⟫/2} 𝒩(0,2sP)(dξ) = det(I + 2sP^{1/2}TP^{1/2})^{-1/2} e^{-⟪Σ_s x,x⟫/2}`
with `Σ_s = 2sP^{1/2}(I + 2sP^{1/2}TP^{1/2})^{-1}P^{1/2}` (`integral_layer_exp_quadratic`); this
is the integrand of `eq:filtered-gaussian-target`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `(cR) X (cR) = c² (R X R)`. -/
theorem smul_mul_mul_smul (c : ℝ) (R X : H →L[ℝ] H) :
    (c • R) * X * (c • R) = (c * c) • (R * X * R) := by
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A real multiple of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_real_smul {A : H →L[ℝ] H} (hA : IsSelfAdjoint A) (c : ℝ) :
    IsSelfAdjoint (c • A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro y z
  show ⟪(c • A) y, z⟫ = ⟪y, (c • A) z⟫
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, real_inner_smul_left,
    real_inner_smul_right]
  exact congrArg (fun t : ℝ => c * t) (hA.isSymmetric y z)

/-- Real scaling preserves summability of the trace. -/
theorem HasSummableTrace.smul {M : H →L[ℝ] H} (h : HasSummableTrace M) (c : ℝ) :
    HasSummableTrace (c • M) := by
  obtain ⟨ι, b, hb⟩ := h
  refine ⟨ι, b, ?_⟩
  have hval : ∀ i, ⟪(c • M) (b i), b i⟫ = c * ⟪M (b i), b i⟫ := fun i => by
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
  exact (hb.mul_left c).congr fun i => (hval i).symm

/-- Nonnegative scaling preserves positive trace-class operators. -/
theorem IsPositiveTraceClass.smul {P : H →L[ℝ] H} (hP : IsPositiveTraceClass P) {c : ℝ}
    (hc : 0 ≤ c) : IsPositiveTraceClass (c • P) where
  isSelfAdjoint := isSelfAdjoint_real_smul hP.isSelfAdjoint c
  inner_nonneg := fun y => by
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    exact mul_nonneg hc (hP.inner_nonneg y)
  hasSummableTrace := hP.hasSummableTrace.smul c

/-- `√c R` is the positive square root of `c P` when `R` is that of `P` and `c ≥ 0`. -/
theorem IsPositiveSqrt.smul {P R : H →L[ℝ] H} (hR : IsPositiveSqrt R P) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveSqrt ((Real.sqrt c) • R) (c • P) where
  isSelfAdjoint := isSelfAdjoint_real_smul hR.isSelfAdjoint _
  inner_nonneg := fun y => by
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    exact mul_nonneg (Real.sqrt_nonneg c) (hR.inner_nonneg y)
  mul_self := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hc, hR.mul_self]

variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The layer integral of `eq:filtered-gaussian-target`: Lemma `lem:gaussian-quadratic`(ii) on
the layer `𝒩(0,2sP)` of the mixture. -/
theorem integral_layer_exp_quadratic {P T R : H →L[ℝ] H} (hP : IsPositiveTraceClass P)
    (hT : IsSelfAdjoint T) (hT0 : ∀ y, 0 ≤ ⟪T y, y⟫) (hR : IsPositiveSqrt R P)
    (hTr : HasSummableTrace (R * T * R)) {s : ℝ} (hs : 0 < s) {ν : Measure H}
    [IsProbabilityMeasure ν] (hν : IsCenteredGaussian ((2 * s) • P) ν) (x : H) :
    ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I - ((⟪T ξ, ξ⟫ / 2 : ℝ) : ℂ)) ∂ν =
      (((Real.sqrt (fredholmDet ((2 * s) • (R * T * R))))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((⟪mixtureLayerCovariance R T s x, x⟫ / 2 : ℝ) : ℂ)) := by
  have h2s : (0 : ℝ) ≤ 2 * s := by linarith
  have hAsq : IsPositiveSqrt ((Real.sqrt (2 * s)) • R) ((2 * s) • P) := hR.smul h2s
  have hATA : (Real.sqrt (2 * s) • R) * T * (Real.sqrt (2 * s) • R) = (2 * s) • (R * T * R) := by
    rw [smul_mul_mul_smul, Real.mul_self_sqrt h2s]
  have hTr' : HasSummableTrace ((Real.sqrt (2 * s) • R) * T * (Real.sqrt (2 * s) • R)) := by
    rw [hATA]
    exact hTr.smul _
  have hkey := integral_exp_quadratic (hP.smul h2s) hT hT0 hAsq hTr' hν x
  rw [hATA] at hkey
  have hres : resolventForm (Real.sqrt (2 * s) • R) ((2 * s) • (R * T * R)) x =
      ⟪mixtureLayerCovariance R T s x, x⟫ := by
    have hop : (Real.sqrt (2 * s) • R) * Ring.inverse (1 + (2 * s) • (R * T * R)) *
        (Real.sqrt (2 * s) • R) = mixtureLayerCovariance R T s := by
      rw [smul_mul_mul_smul, Real.mul_self_sqrt h2s, mixtureLayerCovariance]
    show ⟪((Real.sqrt (2 * s) • R) * Ring.inverse (1 + (2 * s) • (R * T * R)) *
      (Real.sqrt (2 * s) • R)) x, x⟫ = _
    rw [hop]
  rw [hkey, hres]

end OperatorRidgelet
