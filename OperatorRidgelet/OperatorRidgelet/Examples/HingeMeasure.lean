import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.Basic
import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.ToMathlib.VectorMeasureMapDensity

/-!
# The ReLU coefficient measures of Gaussian-activation networks

The hinge representation `Φ(u) = ∫ ReLU(u - t) φ''(t) dt` turns a Gaussian-activation network
into a ReLU network whose coefficient measure is a pushforward of `φ''(t) γ λ(dθ) dt`
(`hingeCoefficientMeasure`, Example `ex:gaussian-parameter`(vi)) or of `φ''(t) b_y m(dy) dt`
(`layerHingeMeasure`, Example `ex:operator-layer`(iii)).  This module shows that these measures
have finite variation and finite parameter moments of every order, using the domination of the
variation of a pushed-forward measure with a density
(`MeasureTheory.VectorMeasure.lintegral_variation_map_withDensityᵥ_le`) and the moments of `φ''`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory LeanRidgelet Filter
open scoped RealInnerProductSpace ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The Lebesgue integral `∫⁻ ‖g‖ₑ F` is finite when `‖g‖ F` is dominated by an integrable
function. -/
theorem lintegral_enorm_mul_ofReal_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] {g : X → E} {F B : X → ℝ}
    (hB : Integrable B μ) (hFB : ∀ x, ‖g x‖ * F x ≤ B x) (hF : ∀ x, 0 ≤ F x) :
    ∫⁻ x, ‖g x‖ₑ * ENNReal.ofReal (F x) ∂μ < ⊤ := by
  have hB0 : ∀ x, 0 ≤ B x := fun x => (mul_nonneg (norm_nonneg _) (hF x)).trans (hFB x)
  calc ∫⁻ x, ‖g x‖ₑ * ENNReal.ofReal (F x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hFB x)
    _ < ⊤ := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hB0)).mp hB.2

/-! ### The hinge measure of the neural-operator layer -/

section Layer

variable {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} [IsFiniteMeasure m] {a : Ω → H}
  {b : Ω → Y}

omit [InnerProductSpace ℝ H] [CompleteSpace Y] [IsFiniteMeasure m] in
/-- The density `(y, t) ↦ φ''(t) • b_y` of the hinge measure of the layer is integrable. -/
theorem IsLayerData.integrable_gaussianActDeriv2_smul (hL : IsLayerData m a b) :
    Integrable (fun p : Ω × ℝ => gaussianActDeriv2 p.2 • b p.1) (m.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : Ω × ℝ => gaussianActDeriv2 p.2 • b p.1)
      (m.prod volume) :=
    ((continuous_gaussianActDeriv2.comp_stronglyMeasurable measurable_snd.stronglyMeasurable).smul
      (hL.stronglyMeasurable_b.comp_measurable measurable_fst)).aestronglyMeasurable
  refine (hL.integrable_b.norm.mul_prod integrable_gaussianActDeriv2.norm).mono' hmeas
    (Eventually.of_forall fun p => ?_)
  rw [norm_smul]
  exact le_of_eq (mul_comm _ _)

variable [MeasurableSpace H]

omit [InnerProductSpace ℝ H] [IsFiniteMeasure m] in
/-- **Example `ex:operator-layer`(iii)**: the hinge measure of the layer has finite variation. -/
theorem IsLayerData.isFiniteMeasure_layerHingeMeasure_variation (hL : IsLayerData m a b) :
    IsFiniteMeasure (layerHingeMeasure m a b).variation :=
  ⟨by
    unfold layerHingeMeasure
    exact lt_of_le_of_lt (VectorMeasure.variation_map_withDensityᵥ_univ_le
      hL.integrable_gaussianActDeriv2_smul _) hL.integrable_gaussianActDeriv2_smul.2⟩

omit [IsFiniteMeasure m] [InnerProductSpace ℝ H] in
/-- **Example `ex:operator-layer`(iii)**: the hinge measure of the layer has finite moments of
every order. -/
theorem IsLayerData.lintegral_layerHingeMeasure_variation_lt_top (hL : IsLayerData m a b)
    (k : ℕ) :
    ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ k)
      ∂(layerHingeMeasure m a b).variation < ⊤ := by
  unfold layerHingeMeasure
  refine lt_of_le_of_lt (VectorMeasure.lintegral_variation_map_withDensityᵥ_le
    hL.integrable_gaussianActDeriv2_smul _ _) ?_
  have hC : 0 ≤ layerSupNorm a := layerSupNorm_nonneg a
  refine lintegral_enorm_mul_ofReal_lt_top (B := fun p : Ω × ℝ =>
    ‖b p.1‖ * ((1 + layerSupNorm a + |p.2|) ^ k * |gaussianActDeriv2 p.2|))
    (hL.integrable_b.norm.mul_prod
      (integrable_const_add_abs_pow_mul_abs_gaussianActDeriv2 hC k)) (fun p => ?_)
    (fun p => by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  calc |gaussianActDeriv2 p.2| * ‖b p.1‖ * (1 + ‖a p.1‖ + |p.2|) ^ k
      ≤ |gaussianActDeriv2 p.2| * ‖b p.1‖ * (1 + layerSupNorm a + |p.2|) ^ k := by
        gcongr
        exact hL.norm_le_layerSupNorm p.1
    _ = _ := by ring

end Layer

/-! ### The hinge coefficient measure of a coefficient density -/

section Density

variable [MeasurableSpace H] (lam : Measure (H × ℝ)) [SigmaFinite lam] {γ : H × ℝ → Y}

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace Y] [SigmaFinite lam] in
/-- The density `(θ, t) ↦ φ''(t) • γ(θ)` of the hinge coefficient measure is integrable. -/
theorem integrable_gaussianActDeriv2_smul_of_integrable (hγ : Integrable γ lam) :
    Integrable (fun p : (H × ℝ) × ℝ => gaussianActDeriv2 p.2 • γ p.1) (lam.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : (H × ℝ) × ℝ => gaussianActDeriv2 p.2 • γ p.1)
      (lam.prod volume) :=
    (continuous_gaussianActDeriv2.comp_aestronglyMeasurable
      measurable_snd.aestronglyMeasurable).smul
      (hγ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  refine (hγ.norm.mul_prod integrable_gaussianActDeriv2.norm).mono' hmeas
    (Eventually.of_forall fun p => ?_)
  rw [norm_smul]
  exact le_of_eq (mul_comm _ _)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SigmaFinite lam] in
/-- **Example `ex:gaussian-parameter`(vi)**: the hinge coefficient measure has finite
variation. -/
theorem isFiniteMeasure_hingeCoefficientMeasure_variation (hγ : Integrable γ lam) :
    IsFiniteMeasure (hingeCoefficientMeasure lam γ).variation :=
  ⟨by
    unfold hingeCoefficientMeasure
    exact lt_of_le_of_lt (VectorMeasure.variation_map_withDensityᵥ_univ_le
      (integrable_gaussianActDeriv2_smul_of_integrable lam hγ) _)
      (integrable_gaussianActDeriv2_smul_of_integrable lam hγ).2⟩

omit [InnerProductSpace ℝ H] [SigmaFinite lam] in
/-- **Example `ex:gaussian-parameter`(vi)**: the hinge coefficient measure has finite moments
of every order when the coefficient density does. -/
theorem lintegral_hingeCoefficientMeasure_variation_lt_top (hγ : Integrable γ lam)
    (hmom : ∀ k : ℕ, Integrable (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ k * ‖γ θ‖) lam)
    (k : ℕ) :
    ∫⁻ θ : H × ℝ, ENNReal.ofReal ((1 + ‖θ.1‖ + |θ.2|) ^ k)
      ∂(hingeCoefficientMeasure lam γ).variation < ⊤ := by
  unfold hingeCoefficientMeasure
  refine lt_of_le_of_lt (VectorMeasure.lintegral_variation_map_withDensityᵥ_le
    (integrable_gaussianActDeriv2_smul_of_integrable lam hγ) _ _) ?_
  have hB : Integrable (fun p : (H × ℝ) × ℝ => 2 ^ k *
      ((1 + ‖p.1.1‖ + |p.1.2|) ^ k * ‖γ p.1‖ * |gaussianActDeriv2 p.2| +
        ‖γ p.1‖ * (|p.2| ^ k * |gaussianActDeriv2 p.2|))) (lam.prod volume) :=
    (((hmom k).mul_prod integrable_gaussianActDeriv2.norm).add
      (hγ.norm.mul_prod (integrable_abs_pow_mul_abs_gaussianActDeriv2 k))).const_mul _
  refine lintegral_enorm_mul_ofReal_lt_top hB (fun p => ?_) (fun p => by positivity)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : (1 + ‖p.1.1‖ + |p.1.2 - p.2|) ^ k ≤
      2 ^ k * ((1 + ‖p.1.1‖ + |p.1.2|) ^ k + |p.2| ^ k) := by
    calc (1 + ‖p.1.1‖ + |p.1.2 - p.2|) ^ k
        ≤ ((1 + ‖p.1.1‖ + |p.1.2|) + |p.2|) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith [abs_sub p.1.2 p.2]) k
      _ ≤ 2 ^ k * ((1 + ‖p.1.1‖ + |p.1.2|) ^ k + |p.2| ^ k) :=
          add_pow_le_two_pow_mul_add_pow (by positivity) (abs_nonneg _) k
  calc |gaussianActDeriv2 p.2| * ‖γ p.1‖ * (1 + ‖p.1.1‖ + |p.1.2 - p.2|) ^ k
      ≤ |gaussianActDeriv2 p.2| * ‖γ p.1‖ *
          (2 ^ k * ((1 + ‖p.1.1‖ + |p.1.2|) ^ k + |p.2| ^ k)) := by gcongr
    _ = _ := by ring

end Density

end OperatorRidgelet
