import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral
import OperatorRidgelet.RankOneLift

/-!
# Operator-valued ridgelet transform

This file formalizes the operator-parameter lift used in the manuscript.  A fixed nonzero readout
vector `ψ` gives the parameter map

`T (A, b) = (A† ψ, inner ℝ ψ b)`.

The normalized rank-one map gives a continuous section `J` of `T`.  Consequently, a scalar
complex ridgelet measure can be lifted by pushforward along `J`; pushing the lift forward along
`T` recovers the original measure.  Any scalar reconstruction theorem therefore induces an exact
operator-valued reconstruction theorem.

The ambient operator type below is the space of bounded operators.  The section itself consists
of rank-one operators, and hence represents the rank-one Hilbert--Schmidt submodel appearing in
the manuscript without requiring a separate bundled Hilbert--Schmidt-operator type.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory

/-- Scalar ridge parameters `(a, c)` on a real Hilbert space. -/
abbrev ScalarRidgeParameter (H : Type*) := H × ℝ

/-- Operator ridge parameters `(A, b)`. -/
abbrev OperatorRidgeParameter (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  (H →L[ℝ] H) × H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Read an operator parameter through the fixed vector `ψ`. -/
def operatorParameterMap (ψ : H) :
    OperatorRidgeParameter H → ScalarRidgeParameter H :=
  fun p => (ContinuousLinearMap.adjoint p.1 ψ, inner ℝ ψ p.2)

/-- The bias component of the normalized rank-one section. -/
def biasLift (ψ : H) (c : ℝ) : H :=
  (c * (‖ψ‖ ^ 2)⁻¹) • ψ

/-- The rank-one section from scalar ridge parameters to operator parameters. -/
def operatorRidgeletSection (ψ : H) :
    ScalarRidgeParameter H → OperatorRidgeParameter H :=
  fun p => (rankOneLift ψ p.1, biasLift ψ p.2)

omit [CompleteSpace H] in
/-- Reading out a lifted bias recovers its scalar value. -/
theorem inner_biasLift (ψ : H) (c : ℝ) (hψ : ψ ≠ 0) :
    inner ℝ ψ (biasLift ψ c) = c := by
  rw [biasLift, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)), mul_one]

/-- The parameter reduction is a left inverse of the rank-one section. -/
theorem operatorParameterMap_section (ψ : H) (hψ : ψ ≠ 0) :
    Function.LeftInverse (operatorParameterMap ψ) (operatorRidgeletSection ψ) := by
  intro p
  apply Prod.ext
  · exact adjoint_rankOneLift_apply ψ p.1 hψ
  · exact inner_biasLift ψ p.2 hψ

/-- Continuity of `operatorParameterMap`. -/
theorem continuous_operatorParameterMap (ψ : H) :
    Continuous (operatorParameterMap ψ) := by
  unfold operatorParameterMap
  fun_prop

omit [CompleteSpace H] in
/-- Continuity of `operatorRidgeletSection`. -/
theorem continuous_operatorRidgeletSection (ψ : H) :
    Continuous (operatorRidgeletSection ψ) := by
  unfold operatorRidgeletSection rankOneLift biasLift
  fun_prop

/-- The scalar ridge feature associated with `(a, c)`. -/
def scalarRidgeFeature (β : ℝ → ℂ) (p : ScalarRidgeParameter H) (x : H) : ℂ :=
  β (inner ℝ p.1 x + p.2)

/-- The operator ridge feature read through `ψ`. -/
def operatorRidgeFeature (ψ : H) (β : ℝ → ℂ)
    (p : OperatorRidgeParameter H) (x : H) : ℂ :=
  β (inner ℝ (ContinuousLinearMap.adjoint p.1 ψ) x + inner ℝ ψ p.2)

/-- Along the rank-one section, the operator feature equals the scalar ridge feature. -/
theorem operatorRidgeFeature_section (ψ : H) (hψ : ψ ≠ 0) (β : ℝ → ℂ)
    (p : ScalarRidgeParameter H) (x : H) :
    operatorRidgeFeature ψ β (operatorRidgeletSection ψ p) x =
      scalarRidgeFeature β p x := by
  rw [operatorRidgeFeature, scalarRidgeFeature, operatorRidgeletSection,
    adjoint_rankOneLift_apply ψ p.1 hψ, inner_biasLift ψ p.2 hψ]

section Measures

variable [MeasurableSpace H] [BorelSpace H]

/-- Measurability of `operatorParameterMap`. -/
theorem measurable_operatorParameterMap (ψ : H) :
    Measurable (operatorParameterMap ψ) := by
  unfold operatorParameterMap
  fun_prop

omit [CompleteSpace H] in
/-- Measurability of `operatorRidgeletSection`. -/
theorem measurable_operatorRidgeletSection (ψ : H) :
    Measurable (operatorRidgeletSection ψ) := by
  unfold operatorRidgeletSection rankOneLift biasLift
  fun_prop

/-- Complex scalar ridge synthesis as an integral against a complex measure. -/
def scalarComplexRidgeSynthesis (β : ℝ → ℂ)
    (μ : ComplexMeasure (ScalarRidgeParameter H)) (x : H) : ℂ :=
  VectorMeasure.integral μ (fun p => scalarRidgeFeature β p x)
    (ContinuousLinearMap.lsmul ℝ ℂ)

/-- Direct complex operator-parameter synthesis. -/
def operatorComplexRidgeSynthesis (ψ : H) (β : ℝ → ℂ)
    (Γ : ComplexMeasure (OperatorRidgeParameter H)) (x : H) : ℂ :=
  VectorMeasure.integral Γ (fun p => operatorRidgeFeature ψ β p x)
    (ContinuousLinearMap.lsmul ℝ ℂ)

/-- Pushing coefficients along the section preserves the scalar synthesis integral. -/
theorem operatorComplexRidgeSynthesis_map_section (ψ : H) (hψ : ψ ≠ 0)
    (β : ℝ → ℂ) (μ : ComplexMeasure (ScalarRidgeParameter H)) (x : H)
    (hstrong : AEStronglyMeasurable (fun q => operatorRidgeFeature ψ β q x)
      (μ.variation.map (operatorRidgeletSection ψ)))
    (hint : μ.Integrable
      ((fun q => operatorRidgeFeature ψ β q x) ∘ operatorRidgeletSection ψ)) :
    operatorComplexRidgeSynthesis ψ β (μ.map (operatorRidgeletSection ψ)) x =
      scalarComplexRidgeSynthesis β μ x := by
  rw [operatorComplexRidgeSynthesis, scalarComplexRidgeSynthesis]
  rw [VectorMeasure.integral_map (measurable_operatorRidgeletSection ψ) hstrong hint]
  congr 1
  funext p
  exact operatorRidgeFeature_section ψ hψ β p x

/-- Pushforward of vector measures respects composition of measurable maps. -/
theorem vectorMeasure_map_map
    {α β γ M : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [AddCommMonoid M] [TopologicalSpace M] (v : VectorMeasure α M)
    (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    (v.map f).map g = v.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs]
  rw [VectorMeasure.map_apply _ hf (hg hs)]
  rw [VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

/-- Lift a scalar complex ridgelet transform to operator parameters along the rank-one section. -/
def operatorValuedRidgeletTransform {F : Type*} (ψ : H)
    (R : F → ComplexMeasure (ScalarRidgeParameter H)) (f : F) :
    ComplexMeasure (OperatorRidgeParameter H) :=
  (R f).map (operatorRidgeletSection ψ)

/-- Operator synthesis factors through scalar synthesis by pushforward along `T`. -/
def operatorValuedSynthesis {F : Type*} (ψ : H)
    (S : ComplexMeasure (ScalarRidgeParameter H) → F)
    (Γ : ComplexMeasure (OperatorRidgeParameter H)) : F :=
  S (Γ.map (operatorParameterMap ψ))

/-- Reducing the lifted coefficient measure recovers the scalar ridgelet coefficients. -/
theorem operatorValuedRidgeletTransform_pushforward {F : Type*}
    (ψ : H) (hψ : ψ ≠ 0) (R : F → ComplexMeasure (ScalarRidgeParameter H)) (f : F) :
    (operatorValuedRidgeletTransform ψ R f).map (operatorParameterMap ψ) = R f := by
  rw [operatorValuedRidgeletTransform,
    vectorMeasure_map_map _ _ _ (measurable_operatorRidgeletSection ψ)
      (measurable_operatorParameterMap ψ)]
  have hcomp : operatorParameterMap ψ ∘ operatorRidgeletSection ψ = id := by
    funext p
    exact operatorParameterMap_section ψ hψ p
  rw [hcomp, VectorMeasure.map_id]

/-- Scalar reconstruction transfers to the lifted operator-valued architecture. -/
theorem operatorValuedRidgelet_reconstruction {F : Type*}
    (ψ : H) (hψ : ψ ≠ 0)
    (R : F → ComplexMeasure (ScalarRidgeParameter H))
    (S : ComplexMeasure (ScalarRidgeParameter H) → F)
    (hrec : Function.RightInverse R S) (f : F) :
    operatorValuedSynthesis ψ S (operatorValuedRidgeletTransform ψ R f) = f := by
  rw [operatorValuedSynthesis,
    operatorValuedRidgeletTransform_pushforward ψ hψ R f]
  exact hrec f

omit [BorelSpace H] in
/-- Coefficient measures with the same reduced pushforward have the same synthesis. -/
theorem operatorValuedSynthesis_eq_of_map_eq {F : Type*} (ψ : H)
    (S : ComplexMeasure (ScalarRidgeParameter H) → F)
    (Γ₁ Γ₂ : ComplexMeasure (OperatorRidgeParameter H))
    (hmap : Γ₁.map (operatorParameterMap ψ) = Γ₂.map (operatorParameterMap ψ)) :
    operatorValuedSynthesis ψ S Γ₁ = operatorValuedSynthesis ψ S Γ₂ := by
  exact congrArg S hmap

end Measures

end OperatorRidgelet
