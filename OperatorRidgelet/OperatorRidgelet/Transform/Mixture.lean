import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.ToMathlib.GiryMonad
import OperatorRidgelet.ToMathlib.RpowIntegral

/-!
# The Gaussian mixture as a Giry-monad bind

Infrastructure for Lemmas `lem:homogeneous-mixture` and `lem:mixture-integration`: the Gaussian
layers `N s = 𝒩(0,2sP)` are the dilates `(√s • ·)_# N 1` of the layer at `s = 1` (by Fourier
uniqueness of finite measures on a separable Hilbert space), which gives a *measurable* family
`scaledLayer N`; the mixture `∫_S N s s^{α/2-1} ds` is the bind of the weight against this
family, and the integration formulas, the divergence `ν_α(H) = ∞`, and the homogeneity
`(D_ω)_# ν_α = |ω|^{-α} ν_α` follow from the monad laws (`OperatorRidgelet.ToMathlib.GiryMonad`)
and the substitution `u = ω² s` in the weight.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

/-! ### The scaled layers -/

section LayersBasic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  {P : H →L[ℝ] H} {N : ℝ → Measure H}

theorem IsCenteredGaussianLayers.charFun_eq (hN : IsCenteredGaussianLayers P N) {s : ℝ}
    (hs : 0 < s) (ξ : H) :
    charFun (N s) ξ = Complex.exp (-((s * ⟪P ξ, ξ⟫ : ℝ) : ℂ)) := by
  rw [(hN s hs).charFun_eq]
  congr 3
  change ⟪(2 * s) • P ξ, ξ⟫ / 2 = s * ⟪P ξ, ξ⟫
  rw [real_inner_smul_left]
  ring

theorem IsCenteredGaussianLayers.isProbabilityMeasure (hN : IsCenteredGaussianLayers P N) {s : ℝ}
    (hs : 0 < s) : IsProbabilityMeasure (N s) :=
  (hN s hs).isProbabilityMeasure

end LayersBasic

section Layers

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The dilated layer `(√s • ·)_# N 1`; for `s > 0` it is `N s = 𝒩(0,2sP)`, and it depends
measurably on `s`. -/
def scaledLayer (N : ℝ → Measure H) (s : ℝ) : Measure H :=
  (N 1).map fun x => Real.sqrt s • x

variable {P : H →L[ℝ] H} {N : ℝ → Measure H}

/-- The dilate of a layer by `c` is the layer at `c² s`. -/
theorem IsCenteredGaussianLayers.map_smul (hN : IsCenteredGaussianLayers P N) {s : ℝ}
    (hs : 0 < s) {c : ℝ} (hc : c ≠ 0) :
    (N s).map (fun x => c • x) = N (c ^ 2 * s) := by
  haveI := hN.isProbabilityMeasure hs
  haveI := hN.isProbabilityMeasure (s := c ^ 2 * s) (by positivity)
  haveI : IsProbabilityMeasure ((N s).map fun x => c • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_map_smul, hN.charFun_eq hs, hN.charFun_eq (by positivity)]
  congr 3
  rw [P.map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem IsCenteredGaussianLayers.eq_scaledLayer (hN : IsCenteredGaussianLayers P N) {s : ℝ}
    (hs : 0 < s) : N s = scaledLayer N s := by
  unfold scaledLayer
  rw [hN.map_smul one_pos (Real.sqrt_pos.mpr hs).ne', Real.sq_sqrt hs.le, mul_one]

theorem IsCenteredGaussianLayers.scaledLayer_eq_scaledLayer_abs (hN : IsCenteredGaussianLayers P N)
    (c : ℝ) : (N 1).map (fun x => c • x) = (N 1).map fun x => |c| • x := by
  haveI := hN.isProbabilityMeasure one_pos
  haveI : IsProbabilityMeasure ((N 1).map fun x => c • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure ((N 1).map fun x => |c| • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_map_smul, charFun_map_smul, hN.charFun_eq one_pos, hN.charFun_eq one_pos]
  congr 3
  rw [P.map_smul, real_inner_smul_left, real_inner_smul_right, P.map_smul, real_inner_smul_left,
    real_inner_smul_right]
  linear_combination (-⟪P ξ, ξ⟫) * abs_mul_abs_self c

omit [CompleteSpace H] in
/-- The scaled layers form a measurable family of probability measures. -/
theorem IsCenteredGaussianLayers.measurable_scaledLayer (hN : IsCenteredGaussianLayers P N) :
    Measurable (scaledLayer N) := by
  haveI := hN.isProbabilityMeasure one_pos
  refine Measure.measurable_of_measurable_coe _ fun E hE => ?_
  have : (fun s => scaledLayer N s E) =
      fun s => (N 1) (Prod.mk s ⁻¹' {p : ℝ × H | Real.sqrt p.1 • p.2 ∈ E}) := by
    funext s
    rw [scaledLayer, Measure.map_apply (by fun_prop) hE]
    rfl
  rw [this]
  exact measurable_measure_prodMk_left
    ((by fun_prop : Measurable fun p : ℝ × H => Real.sqrt p.1 • p.2) hE)

omit [CompleteSpace H] [SecondCountableTopology H] in
theorem IsCenteredGaussianLayers.isProbabilityMeasure_scaledLayer
    (hN : IsCenteredGaussianLayers P N) (s : ℝ) : IsProbabilityMeasure (scaledLayer N s) :=
  haveI := hN.isProbabilityMeasure one_pos
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Dilating a scaled layer by `ω` gives the scaled layer at `ω² s`. -/
theorem IsCenteredGaussianLayers.scaledLayer_map_smul (hN : IsCenteredGaussianLayers P N)
    (s ω : ℝ) :
    (scaledLayer N s).map (fun x => ω • x) = scaledLayer N (ω ^ 2 * s) := by
  unfold scaledLayer
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h1 : ((fun x : H => ω • x) ∘ fun x => Real.sqrt s • x) = fun x => (ω * Real.sqrt s) • x := by
    funext x
    simp [Function.comp, smul_smul]
  rw [h1, hN.scaledLayer_eq_scaledLayer_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg s),
    Real.sqrt_mul (sq_nonneg ω), Real.sqrt_sq_eq_abs]

end Layers

/-! ### The mixture as a bind of the scaled layers -/

section Mixture

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {P : H →L[ℝ] H} {N : ℝ → Measure H}

/-- The weight `s^{α/2-1}` as a function into `ℝ≥0∞`. -/
theorem measurable_mixtureDensity (α : ℝ) :
    Measurable fun s : ℝ => ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  fun_prop

instance instSFiniteMixtureWeight (α : ℝ) (S : Set ℝ) : SFinite (mixtureWeight α S) := by
  unfold mixtureWeight
  infer_instance

theorem IsCenteredGaussianLayers.gaussianMixtureOn_eq_bind (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS' : S ⊆ Set.Ioi 0) :
    gaussianMixtureOn N α S = (mixtureWeight α S).bind (scaledLayer N) := by
  unfold gaussianMixtureOn
  apply Measure.bind_congr_right
  refine (withDensity_absolutelyContinuous _ _).ae_eq ?_
  exact ae_restrict_of_forall_mem hS fun s hs => hN.eq_scaledLayer (hS' hs)

theorem IsCenteredGaussianLayers.gaussianMixtureOn_apply (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS' : S ⊆ Set.Ioi 0) {E : Set H}
    (hE : MeasurableSet E) :
    gaussianMixtureOn N α S E = ∫⁻ s in S, N s E * ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  rw [hN.gaussianMixtureOn_eq_bind α hS hS',
    Measure.bind_apply hE hN.measurable_scaledLayer.aemeasurable, mixtureWeight,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_mixtureDensity α)
      (g := fun s => scaledLayer N s E)
      (show Measurable fun s => scaledLayer N s E from
        (Measure.measurable_coe hE).comp hN.measurable_scaledLayer)]
  refine setLIntegral_congr_fun hS fun s hs => ?_
  rw [Pi.mul_apply, mul_comm, hN.eq_scaledLayer (hS' hs)]

theorem IsCenteredGaussianLayers.lintegral_gaussianMixtureOn (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS' : S ⊆ Set.Ioi 0) {F : H → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ξ, F ξ ∂gaussianMixtureOn N α S =
      ∫⁻ s in S, (∫⁻ ξ, F ξ ∂N s) * ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  rw [hN.gaussianMixtureOn_eq_bind α hS hS',
    Measure.lintegral_bind hN.measurable_scaledLayer.aemeasurable hF.aemeasurable, mixtureWeight,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_mixtureDensity α)
      (g := fun s => ∫⁻ ξ, F ξ ∂scaledLayer N s)
      (show Measurable fun s => ∫⁻ ξ, F ξ ∂scaledLayer N s from
        (Measure.measurable_lintegral hF).comp hN.measurable_scaledLayer)]
  refine setLIntegral_congr_fun hS fun s hs => ?_
  rw [Pi.mul_apply, mul_comm, hN.eq_scaledLayer (hS' hs)]

theorem IsCenteredGaussianLayers.integral_gaussianMixtureOn (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS' : S ⊆ Set.Ioi 0) {F : H → ℂ}
    (hF : Integrable F (gaussianMixtureOn N α S)) :
    ∫ ξ, F ξ ∂gaussianMixtureOn N α S =
      ∫ s in S, (∫ ξ, F ξ ∂N s) * ((s ^ (α / 2 - 1) : ℝ) : ℂ) := by
  rw [hN.gaussianMixtureOn_eq_bind α hS hS'] at hF ⊢
  haveI := hN.isProbabilityMeasure_scaledLayer
  rw [Measure.integral_bind_eq hN.measurable_scaledLayer hF, mixtureWeight]
  have hw : (fun s : ℝ => ENNReal.ofReal (s ^ (α / 2 - 1))) =
      fun s => ((Real.toNNReal (s ^ (α / 2 - 1)) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hw, integral_withDensity_eq_integral_smul (by fun_prop)]
  refine setIntegral_congr_fun hS fun s hs => ?_
  have hs' : 0 < s := hS' hs
  rw [← hN.eq_scaledLayer hs', NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg hs'.le _),
    Complex.real_smul, mul_comm]

/-- The total mass of the mixture on `S` is `∫_S s^{α/2-1} ds`. -/
theorem IsCenteredGaussianLayers.gaussianMixtureOn_univ (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS' : S ⊆ Set.Ioi 0) :
    gaussianMixtureOn N α S Set.univ = ∫⁻ s in S, ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  rw [hN.gaussianMixtureOn_apply α hS hS' MeasurableSet.univ]
  refine setLIntegral_congr_fun hS fun s hs => ?_
  haveI := hN.isProbabilityMeasure (hS' hs)
  rw [measure_univ, one_mul]

end Mixture

/-! ### Scaling of the weight -/

section Weight


/-- The dilation `u = c s`, `c > 0`, scales the weight `s^{α/2-1} ds` on `(0,∞)` by
`c^{-α/2}`. -/
theorem mixtureWeight_map_mul (α : ℝ) {c : ℝ} (hc : 0 < c) :
    (mixtureWeight α (Set.Ioi 0)).map (fun s => c * s) =
      ENNReal.ofReal (c ^ (-(α / 2))) • mixtureWeight α (Set.Ioi 0) := by
  have hmul : Measurable fun s : ℝ => c * s := by fun_prop
  have hw := measurable_mixtureDensity α
  ext E hE
  have hpre : (fun s : ℝ => c * s) ⁻¹' Set.Ioi 0 = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩
  rw [Measure.map_apply hmul hE, Measure.smul_apply, smul_eq_mul, mixtureWeight,
    withDensity_apply _ (hmul hE), withDensity_apply _ hE, Measure.restrict_restrict (hmul hE),
    Measure.restrict_restrict hE]
  -- rewrite the left side as an integral of `G (c * s)`
  set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (α / 2 - 1)) with hw_def
  set G : ℝ → ℝ≥0∞ := (E ∩ Set.Ioi 0).indicator fun u => w (c⁻¹ * u) with hG_def
  have hG_meas : Measurable G :=
    (hw.comp (measurable_const_mul c⁻¹)).indicator (hE.inter measurableSet_Ioi)
  have h1 : ∫⁻ s in (fun s : ℝ => c * s) ⁻¹' E ∩ Set.Ioi 0, w s = ∫⁻ s, G (c * s) := by
    rw [← lintegral_indicator (hE.preimage hmul |>.inter measurableSet_Ioi)]
    refine lintegral_congr fun s => ?_
    have : (fun s : ℝ => c * s) ⁻¹' E ∩ Set.Ioi 0 = (fun s : ℝ => c * s) ⁻¹' (E ∩ Set.Ioi 0) := by
      rw [Set.preimage_inter, hpre]
    rw [this, hG_def, ← Set.indicator_comp_right (fun s : ℝ => c * s)]
    simp only [Function.comp_def, inv_mul_cancel_left₀ hc.ne']
  have h2 : ∫⁻ s, G (c * s) = ENNReal.ofReal |c⁻¹| * ∫⁻ u, G u := by
    rw [← lintegral_map hG_meas hmul, Real.map_volume_mul_left hc.ne', lintegral_smul_measure,
      smul_eq_mul]
  have h3 : ∫⁻ u, G u = ENNReal.ofReal (c⁻¹ ^ (α / 2 - 1)) * ∫⁻ u in E ∩ Set.Ioi 0, w u := by
    rw [hG_def, lintegral_indicator (hE.inter measurableSet_Ioi), ← lintegral_const_mul _ hw]
    refine setLIntegral_congr_fun (hE.inter measurableSet_Ioi) fun u hu => ?_
    have hu' : 0 < u := hu.2
    rw [hw_def]
    simp only
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hu'.le, ENNReal.ofReal_mul (by positivity)]
  rw [h1, h2, h3, ← mul_assoc, abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← Real.rpow_neg_one, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  congr 1
  ring

end Weight

/-! ### Homogeneity and infinitude of the mixture -/

section Homogeneous

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {P : H →L[ℝ] H} {N : ℝ → Measure H}

theorem IsCenteredGaussianLayers.gaussianMixture_univ (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) : gaussianMixture N α Set.univ = ⊤ := by
  rw [gaussianMixture, hN.gaussianMixtureOn_univ α measurableSet_Ioi le_rfl]
  exact lintegral_Ioi_rpow_eq_top _

/-- Homogeneity of the mixture: `(D_ω)_# ν_α = |ω|^{-α} ν_α`. -/
theorem IsCenteredGaussianLayers.isHomogeneous_gaussianMixture (hN : IsCenteredGaussianLayers P N)
    (α : ℝ) : IsHomogeneous α (gaussianMixture N α) := by
  intro ω hω
  have hω2 : 0 < ω ^ 2 := by positivity
  rw [gaussianMixture, hN.gaussianMixtureOn_eq_bind α measurableSet_Ioi le_rfl,
    Measure.map_bind_eq hN.measurable_scaledLayer (by fun_prop)]
  have h1 : (fun s => (scaledLayer N s).map fun x => ω • x) =
      scaledLayer N ∘ fun s => ω ^ 2 * s := by
    funext s
    exact hN.scaledLayer_map_smul s ω
  rw [h1, ← Measure.bind_map_eq (by fun_prop) hN.measurable_scaledLayer,
    mixtureWeight_map_mul α hω2, Measure.bind_smul]
  congr 2
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg ω)]
  congr 1
  push_cast
  ring

end Homogeneous

end OperatorRidgelet
