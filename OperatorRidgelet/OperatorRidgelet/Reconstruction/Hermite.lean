import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.ToMathlib.HermiteExpansion
import OperatorRidgelet.ToMathlib.EntirePowerSeries

/-!
# The Hermite expansion of the weighted Fourier transform along a ray

For a centred Gaussian `μ = 𝒩(0,Q)` and `ξ ≠ 0`, the coordinate `Y(x) = ⟪x,ξ⟫/τ(ξ)`,
`τ(ξ) = ⟪Qξ,ξ⟫^{1/2}`, is a standard Gaussian coordinate (`isStdGaussianCoord_inner_div`).
Under this identification the objects of Lemma `lem:hermite-totality` are the objects of
`OperatorRidgelet.ToMathlib.HermiteExpansion` at the complex parameter `-i z τ(ξ)`:

* `hermiteCoefficient_eq`: `E_μ[f Heₙ(Y)] = ∫ f Heₙ(Y) dμ`;
* `hermiteExtension_eq`: `G_f(zξ) = ∫ f e^{wY - w²/2} dμ` with `w = -i z τ(ξ)`.

The lemma then follows from the one-dimensional expansion together with
`OperatorRidgelet.ToMathlib.EntirePowerSeries`.
-/

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped RealInnerProductSpace NNReal

noncomputable section

namespace OperatorRidgelet

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- For `μ = 𝒩(0,Q)` and `⟪Qξ,ξ⟫ > 0`, the normalized coordinate `x ↦ ⟪x,ξ⟫/τ(ξ)` is a
standard Gaussian coordinate. -/
theorem isStdGaussianCoord_inner_div {Q : H →L[ℝ] H} {μ : Measure H}
    (hμ : IsCenteredGaussian Q μ) (ξ : H) (hpos : 0 < ⟪Q ξ, ξ⟫) :
    IsStdGaussianCoord μ fun x => ⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫ := by
  haveI := hμ.isProbabilityMeasure
  set τ := Real.sqrt ⟪Q ξ, ξ⟫ with hτ
  have hτpos : 0 < τ := Real.sqrt_pos.mpr hpos
  have hmeas : Measurable fun x : H => ⟪x, ξ⟫ := (continuous_id.inner continuous_const).measurable
  refine ⟨hmeas.div_const _, ?_⟩
  have h1 : μ.map (fun x => ⟪x, ξ⟫) = gaussianReal 0 (Real.toNNReal ⟪Q ξ, ξ⟫) :=
    hμ.map_inner_eq_gaussianReal ξ hpos.le
  have h2 : (fun x : H => ⟪x, ξ⟫ / τ) = (fun y : ℝ => τ⁻¹ * y) ∘ fun x : H => ⟪x, ξ⟫ := by
    funext x
    simp [div_eq_inv_mul]
  have hτ2 : τ ^ 2 = ⟪Q ξ, ξ⟫ := Real.sq_sqrt hpos.le
  rw [h2, ← Measure.map_map (measurable_const_mul _) hmeas, h1,
    show (fun y : ℝ => τ⁻¹ * y) = (τ⁻¹ * ·) from rfl, gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, Real.coe_toNNReal _ hpos.le]
  rw [← hτ2]
  field_simp

end OperatorRidgelet
