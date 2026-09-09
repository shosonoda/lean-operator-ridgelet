import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.ToMathlib.LpOfReal
import LeanRidgelet.ToMathlib.BochnerIntegralL2
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The periodic convolution layer

Elementary facts about the convolution layer of Example `ex:convolution`: the directions
`a_y = k(y - ·)` and outputs `b_y = ψ(· - y)` are translates, so they all have the norm of `k`
and of `ψ` (`norm_convDirection`, `norm_convOutput`), and the pairing `⟪a_y, x⟫` is the
convolution `(k * x)(y)` (`inner_convDirection`).  Translation acts continuously on `L²`, so
`y ↦ a_y` and `y ↦ b_y` are continuous (`continuous_convDirection`, `continuous_convOutput`)
and the standing hypotheses of the neural-operator layer hold (`isLayerData_conv`).  The layer
is the convolution `ℱ(x) = ψ * β(k * x)` (`operatorLayer_conv_coeFn_ae`), and its observable
against `φ ≡ 1` is `ψ̂(0) ∫ β((k * x)(y)) dy` (`layerObservable_conv_torusOne`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- `‖a_y‖ = ‖k‖₂` for the direction `a_y = k(y - ·)`. -/
theorem norm_convDirection (k : TorusL2 d) (y : Torus d) : ‖convDirection k y‖ = ‖k‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- `‖b_y‖ = ‖ψ‖₂` for the output `b_y = ψ(· - y)`. -/
theorem norm_convOutput (ψ : TorusL2 d) (y : Torus d) : ‖convOutput ψ y‖ = ‖ψ‖ := by
  unfold convOutput
  rw [norm_ofRealCLM_compLp, LinearIsometry.norm_map]

/-- **Example `ex:convolution`**: `‖A‖_∞ = ‖k‖₂`. -/
theorem layerSupNorm_convDirection (k : TorusL2 d) : layerSupNorm (convDirection k) = ‖k‖ := by
  unfold layerSupNorm
  simp_rw [norm_convDirection]
  exact ciSup_const

/-- **Example `ex:convolution`**: `∫ ‖b_y‖ dy = ‖ψ‖₂`. -/
theorem integral_norm_convOutput (ψ : TorusL2 d) :
    ∫ y, ‖convOutput ψ y‖ ∂torusHaar d = ‖ψ‖ := by
  simp_rw [norm_convOutput]
  simp

/-- **Example `ex:convolution`**: `⟪a_y, x⟫ = (k * x)(y)`. -/
theorem inner_convDirection (k x : TorusL2 d) (y : Torus d) :
    ⟪convDirection k y, x⟫ = ∫ t, k (y - t) * x t ∂torusHaar d := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving k
    (Measure.measurePreserving_sub_left (torusHaar d) y)] with t ht
  change ⟪(Lp.compMeasurePreserving (fun t => y - t)
    (Measure.measurePreserving_sub_left (torusHaar d) y) k) t, x t⟫ = _
  rw [ht, Function.comp_apply]
  simp [RCLike.inner_apply, mul_comm]


/-! ### Continuity in the parameter and the layer hypotheses -/

/-- `y ↦ a_y = k(y - ·)` is continuous into `L²(𝕋^d; ℝ)`. -/
theorem continuous_convDirection (k : TorusL2 d) : Continuous (convDirection k) := by
  have hg : Continuous fun y : Torus d =>
      (⟨fun t => y - t, by fun_prop⟩ : C(Torus d, Torus d)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.sub continuous_snd)
  refine continuous_iff_continuousAt.mpr fun y => ?_
  exact ContinuousAt.compMeasurePreservingLp (f := fun _ => k) continuousAt_const
    hg.continuousAt (fun y => Measure.measurePreserving_sub_left (torusHaar d) y)
    ENNReal.ofNat_ne_top

/-- `y ↦ τ_y ψ = ψ(· - y)` is continuous into `L²(𝕋^d; ℝ)`. -/
theorem continuous_torusTranslate_apply (ψ : TorusL2 d) :
    Continuous fun y : Torus d => torusTranslate d y ψ := by
  have hg : Continuous fun y : Torus d =>
      (⟨fun t => t - y, by fun_prop⟩ : C(Torus d, Torus d)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  refine continuous_iff_continuousAt.mpr fun y => ?_
  exact ContinuousAt.compMeasurePreservingLp (f := fun _ => ψ) continuousAt_const
    hg.continuousAt (fun y => measurePreserving_sub_right (torusHaar d) y)
    ENNReal.ofNat_ne_top

/-- `y ↦ b_y = ψ(· - y)` is continuous into `L²(𝕋^d)`. -/
theorem continuous_convOutput (ψ : TorusL2 d) : Continuous (convOutput ψ) :=
  (Complex.ofRealCLM.compLpL 2 (torusHaar d)).continuous.comp
    (continuous_torusTranslate_apply ψ)

/-- **Example `ex:convolution`**: the standing hypotheses of the neural-operator layer hold. -/
theorem isLayerData_conv (k ψ : TorusL2 d) :
    IsLayerData (torusHaar d) (convDirection k) (convOutput ψ) where
  stronglyMeasurable_a := (continuous_convDirection k).stronglyMeasurable
  bounded_a := ⟨‖k‖, fun y => (norm_convDirection k y).le⟩
  stronglyMeasurable_b := (continuous_convOutput ψ).stronglyMeasurable
  integrable_b := Integrable.of_bound (continuous_convOutput ψ).aestronglyMeasurable ‖ψ‖
    (Eventually.of_forall fun y => (norm_convOutput ψ y).le)

/-! ### The layer as a convolution -/

/-- `b_y` is the class of `t ↦ ψ(t - y)`. -/
theorem convOutput_coeFn_ae (ψ : TorusL2 d) (y : Torus d) :
    (convOutput ψ y : Torus d → ℂ) =ᵐ[torusHaar d] fun t => ((ψ (t - y) : ℝ) : ℂ) := by
  unfold convOutput
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' (torusTranslate d y ψ),
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_sub_right (torusHaar d) y)] with t ht ht'
  rw [ht, Complex.ofRealCLM_apply]
  change (((Lp.compMeasurePreserving (fun t => t - y)
    (measurePreserving_sub_right (torusHaar d) y) ψ) t : ℝ) : ℂ) = _
  rw [ht', Function.comp_apply]

/-- `y ↦ β(⟪a_y, x⟫)` is continuous for a continuous activation `β`. -/
theorem continuous_conv_activation (k : TorusL2 d) {β : ℝ → ℝ} (hβ : Continuous β)
    (x : TorusL2 d) : Continuous fun y => β ⟪convDirection k y, x⟫ :=
  hβ.comp ((continuous_convDirection k).inner continuous_const)

/-- The two-variable integrand `(y, t) ↦ ψ(t - y) β(⟪a_y, x⟫)` of the convolution layer is
integrable on `𝕋^d × 𝕋^d`. -/
theorem integrable_conv_integrand (k ψ : TorusL2 d) {β : ℝ → ℝ} (hβ : Continuous β)
    (x : TorusL2 d) :
    Integrable (fun p : Torus d × Torus d =>
      ((ψ (p.2 - p.1) * β ⟪convDirection k p.1, x⟫ : ℝ) : ℂ))
      ((torusHaar d).prod (torusHaar d)) := by
  obtain ⟨C, hC⟩ := (isLayerData_conv k ψ).exists_bound_comp_inner hβ x
  have hmp : MeasurePreserving (fun p : Torus d × Torus d => p.2 - p.1)
      ((torusHaar d).prod (torusHaar d)) (torusHaar d) :=
    measurePreserving_snd.comp (measurePreserving_prod_sub (torusHaar d) (torusHaar d))
  have hψ : Integrable (fun p : Torus d × Torus d => ψ (p.2 - p.1))
      ((torusHaar d).prod (torusHaar d)) :=
    hmp.integrable_comp_of_integrable ((Lp.memLp ψ).integrable one_le_two)
  refine (hψ.mul_bdd (c := C) ?_ (Eventually.of_forall fun p => ?_)).ofReal
  · exact ((continuous_conv_activation k hβ x).comp continuous_fst).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hC p.1

/-- **Example `ex:convolution`**: the layer is the convolution `ℱ(x) = ψ * β(k * x)`. -/
theorem operatorLayer_conv_coeFn_ae (k ψ : TorusL2 d) {β : ℝ → ℝ} (hβ : Continuous β)
    (x : TorusL2 d) :
    ⇑(operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x)
      =ᵐ[torusHaar d] fun t =>
        ∫ y, ((ψ (t - y) * β ⟪convDirection k y, x⟫ : ℝ) : ℂ) ∂torusHaar d := by
  unfold operatorLayer
  refine integral_L2_coeFn_ae
    (F := fun y t => ((ψ (t - y) * β ⟪convDirection k y, x⟫ : ℝ) : ℂ))
    ((isLayerData_conv k ψ).integrable_ofReal_comp_inner_smul hβ x)
    (integrable_conv_integrand k ψ hβ x) (Eventually.of_forall fun y => ?_)
  filter_upwards [Lp.coeFn_smul ((β ⟪convDirection k y, x⟫ : ℝ) : ℂ) (convOutput ψ y),
    convOutput_coeFn_ae ψ y] with t ht ht'
  rw [ht, Pi.smul_apply, ht', smul_eq_mul, Complex.ofReal_mul, mul_comm]

/-- The constant function `1 ∈ L²(𝕋^d)` is the class of `t ↦ 1`. -/
theorem torusOne_coeFn_ae : (torusOne d : Torus d → ℂ) =ᵐ[torusHaar d] fun _ => (1 : ℂ) := by
  unfold torusOne toLpOrZero
  rw [dif_pos (memLp_const (1 : ℂ))]
  exact MemLp.coeFn_toLp _

/-- The zeroth Fourier coefficient is the mean. -/
theorem torusFourierCoeff_zero (f : Torus d → ℂ) :
    torusFourierCoeff f 0 = ∫ t, f t ∂torusHaar d := by
  unfold torusFourierCoeff torusCharacter
  simp

/-- `⟪1, b_y⟫ = ψ̂(0)`: every translate of `ψ` has the mean of `ψ`. -/
theorem inner_torusOne_convOutput (ψ : TorusL2 d) (y : Torus d) :
    inner ℂ (torusOne d) (convOutput ψ y) = torusFourierCoeff (fun t => (ψ t : ℂ)) 0 := by
  rw [L2.inner_def, torusFourierCoeff_zero]
  have h : ∫ t, ((ψ (t - y) : ℝ) : ℂ) ∂torusHaar d = ∫ t, ((ψ t : ℝ) : ℂ) ∂torusHaar d :=
    integral_sub_right_eq_self (fun t => ((ψ t : ℝ) : ℂ)) y
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [torusOne_coeFn_ae (d := d), convOutput_coeFn_ae ψ y] with t ht ht'
  rw [RCLike.inner_apply, ht, ht']
  simp

/-- **Example `ex:convolution`**: with `φ ≡ 1` the observable is
`F_1(x) = ψ̂(0) ∫ β((k * x)(y)) dy`. -/
theorem layerObservable_conv_torusOne (k ψ : TorusL2 d) {β : ℝ → ℝ} (hβ : Continuous β)
    (x : TorusL2 d) :
    layerObservable (torusHaar d) (convDirection k) (convOutput ψ) β (torusOne d) x =
      torusFourierCoeff (fun t => (ψ t : ℂ)) 0 *
        ∫ y, ((β ⟪convDirection k y, x⟫ : ℝ) : ℂ) ∂torusHaar d := by
  rw [(isLayerData_conv k ψ).layerObservable_eq_integral_inner hβ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [inner_torusOne_convOutput, mul_comm]


/-! ### Translation equivariance -/

/-- `τ_z x` is the class of `t ↦ x(t - z)`. -/
theorem torusTranslate_coeFn_ae (z : Torus d) (x : TorusL2 d) :
    ⇑(torusTranslate d z x) =ᵐ[torusHaar d] fun t => x (t - z) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_sub_right (torusHaar d) z)

/-- `τ_z u` is the class of `t ↦ u(t - z)`. -/
theorem torusTranslateC_coeFn_ae (z : Torus d) (u : TorusL2C d) :
    ⇑(torusTranslateC d z u) =ᵐ[torusHaar d] fun t => u (t - z) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right (torusHaar d) z)

/-- `⟪a_y, τ_z x⟫ = ⟪a_{y-z}, x⟫`. -/
theorem inner_convDirection_torusTranslate (k x : TorusL2 d) (y z : Torus d) :
    ⟪convDirection k y, torusTranslate d z x⟫ = ⟪convDirection k (y - z), x⟫ := by
  rw [inner_convDirection, inner_convDirection]
  have h1 : ∫ t, k (y - t) * (torusTranslate d z x) t ∂torusHaar d =
      ∫ t, k (y - t) * x (t - z) ∂torusHaar d := by
    refine integral_congr_ae ?_
    filter_upwards [torusTranslate_coeFn_ae z x] with t ht
    rw [ht]
  rw [h1, ← integral_add_right_eq_self (fun t => k (y - t) * x (t - z)) z]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [add_sub_cancel_right, sub_add_eq_sub_sub]
  rw [sub_right_comm]

/-- `τ_z b_y = b_{y+z}`. -/
theorem torusTranslateC_convOutput (ψ : TorusL2 d) (y z : Torus d) :
    torusTranslateC d z (convOutput ψ y) = convOutput ψ (y + z) := by
  refine Lp.ext ?_
  filter_upwards [torusTranslateC_coeFn_ae z (convOutput ψ y),
    (measurePreserving_sub_right (torusHaar d) z).quasiMeasurePreserving.ae_eq_comp
      (convOutput_coeFn_ae ψ y), convOutput_coeFn_ae ψ (y + z)] with t h1 h2 h3
  simp only [Function.comp_apply] at h2
  rw [h1, h3, h2, sub_sub, add_comm]

/-- **Example `ex:convolution`**: the layer commutes with translations, `ℱ(τ_z x) = τ_z ℱ(x)`. -/
theorem operatorLayer_conv_torusTranslate (k ψ : TorusL2 d) {β : ℝ → ℝ} (hβ : Continuous β)
    (z : Torus d) (x : TorusL2 d) :
    operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β (torusTranslate d z x) =
      torusTranslateC d z (operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x) := by
  have hT := (isLayerData_conv k ψ).map_operatorLayer hβ
    (torusTranslateC d z).toContinuousLinearMap x
  rw [LinearIsometry.coe_toContinuousLinearMap] at hT
  rw [hT]
  simp_rw [torusTranslateC_convOutput]
  rw [operatorLayer_comp_measurePreserving (e := MeasurableEquiv.subRight z)
    (measurePreserving_sub_right (torusHaar d) z) (convDirection k)
    (fun y => convOutput ψ (y + z))]
  show _ = operatorLayer (torusHaar d) (fun y => convDirection k (y - z))
    (fun y => convOutput ψ (y - z + z)) β x
  simp only [sub_add_cancel]
  exact operatorLayer_congr_inner (fun y => inner_convDirection_torusTranslate k x y z) _ _

/-! ### Equivariance under isometries -/

/-- An isometric automorphism of the torus as a measurable equivalence. -/
def torusIsometryEquiv {σ : Torus d ≃+ Torus d} (hiso : Isometry σ) : Torus d ≃ᵐ Torus d where
  toEquiv := σ.toEquiv
  measurable_toFun := hiso.continuous.measurable
  measurable_invFun := (hiso.right_inv σ.apply_symm_apply).continuous.measurable

/-- `torusIsometryEquiv` acts as `σ`. -/
theorem torusIsometryEquiv_apply {σ : Torus d ≃+ Torus d} (hiso : Isometry σ) (t : Torus d) :
    torusIsometryEquiv hiso t = σ t :=
  rfl

/-- The inverse of `torusIsometryEquiv` acts as `σ⁻¹`. -/
theorem torusIsometryEquiv_symm_apply {σ : Torus d ≃+ Torus d} (hiso : Isometry σ)
    (t : Torus d) : (torusIsometryEquiv hiso).symm t = σ.symm t :=
  rfl

/-- `⟪a_y, x ∘ σ⟫ = ⟪a_{σ y}, x⟫` for a measure-preserving isometry `σ` fixing `k`. -/
theorem inner_convDirection_compMeasurePreserving {σ : Torus d ≃+ Torus d} (hiso : Isometry σ)
    (hσ : MeasurePreserving σ (torusHaar d) (torusHaar d)) (k x : TorusL2 d)
    (hk : (fun t => k (σ t)) =ᵐ[torusHaar d] k) (y : Torus d) :
    ⟪convDirection k y, Lp.compMeasurePreserving σ hσ x⟫ = ⟪convDirection k (σ y), x⟫ := by
  have he : MeasurePreserving (torusIsometryEquiv hiso) (torusHaar d) (torusHaar d) := hσ
  rw [inner_convDirection, inner_convDirection]
  have h1 : ∫ t, k (y - t) * (Lp.compMeasurePreserving σ hσ x) t ∂torusHaar d =
      ∫ t, k (y - t) * x (σ t) ∂torusHaar d := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving x hσ] with t ht
    rw [ht, Function.comp_apply]
  have h2 : ∫ t, k (y - t) * x (σ t) ∂torusHaar d =
      ∫ s, k (y - σ.symm s) * x s ∂torusHaar d := by
    rw [← he.integral_comp' (fun s => k (y - σ.symm s) * x s)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [torusIsometryEquiv_apply, AddEquiv.symm_apply_apply]
  rw [h1, h2]
  have hk' : (fun t => k (σ.symm t)) =ᵐ[torusHaar d] k := by
    filter_upwards [(he.symm (torusIsometryEquiv hiso)).quasiMeasurePreserving.ae_eq_comp hk]
      with t ht
    simp only [Function.comp_apply, torusIsometryEquiv_symm_apply,
      AddEquiv.apply_symm_apply] at ht
    exact ht.symm
  refine integral_congr_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left (torusHaar d)
    (σ y)).quasiMeasurePreserving.ae_eq_comp hk'] with s hs
  simp only [Function.comp_apply, map_sub, AddEquiv.symm_apply_apply] at hs
  rw [hs]

/-- `b_y ∘ σ = b_{σ⁻¹ y}` for a measure-preserving isometry `σ` fixing `ψ`. -/
theorem compMeasurePreserving_convOutput {σ : Torus d ≃+ Torus d}
    (hσ : MeasurePreserving σ (torusHaar d) (torusHaar d)) (ψ : TorusL2 d)
    (hψ : (fun t => ψ (σ t)) =ᵐ[torusHaar d] ψ) (y : Torus d) :
    Lp.compMeasurePreserving σ hσ (convOutput ψ y) = convOutput ψ (σ.symm y) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (convOutput ψ y) hσ,
    hσ.quasiMeasurePreserving.ae_eq_comp (convOutput_coeFn_ae ψ y),
    convOutput_coeFn_ae ψ (σ.symm y),
    (measurePreserving_sub_right (torusHaar d) (σ.symm y)).quasiMeasurePreserving.ae_eq_comp hψ]
    with t h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h4
  rw [h1, h2, h3, ← h4, map_sub, AddEquiv.apply_symm_apply]

/-- **Example `ex:convolution`**: the layer commutes with every measure-preserving isometry of
the torus fixing `k` and `ψ`: `ℱ(x ∘ σ) = ℱ(x) ∘ σ`. -/
theorem operatorLayer_conv_compMeasurePreserving {σ : Torus d ≃+ Torus d} (hiso : Isometry σ)
    (hσ : MeasurePreserving σ (torusHaar d) (torusHaar d)) (k ψ : TorusL2 d) {β : ℝ → ℝ}
    (hβ : Continuous β) (hk : (fun t => k (σ t)) =ᵐ[torusHaar d] k)
    (hψ : (fun t => ψ (σ t)) =ᵐ[torusHaar d] ψ) (x : TorusL2 d) :
    operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β
        (Lp.compMeasurePreserving σ hσ x) =
      Lp.compMeasurePreserving σ hσ
        (operatorLayer (torusHaar d) (convDirection k) (convOutput ψ) β x) := by
  have hT := (isLayerData_conv k ψ).map_operatorLayer hβ
    (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap x
  rw [LinearIsometry.coe_toContinuousLinearMap] at hT
  refine Eq.trans ?_ hT.symm
  have he : MeasurePreserving (torusIsometryEquiv hiso) (torusHaar d) (torusHaar d) := hσ
  rw [operatorLayer_comp_measurePreserving he (convDirection k)
    (fun y => (Lp.compMeasurePreservingₗᵢ ℂ σ hσ) (convOutput ψ y))]
  have hb : ∀ y, (Lp.compMeasurePreservingₗᵢ ℂ σ hσ) (convOutput ψ (torusIsometryEquiv hiso y)) =
      convOutput ψ y := fun y => by
    rw [torusIsometryEquiv_apply]
    change Lp.compMeasurePreserving σ hσ (convOutput ψ (σ y)) = _
    rw [compMeasurePreserving_convOutput hσ ψ hψ, AddEquiv.symm_apply_apply]
  simp_rw [hb]
  exact operatorLayer_congr_inner
    (fun y => inner_convDirection_compMeasurePreserving hiso hσ k x hk y) _ _

end OperatorRidgelet
