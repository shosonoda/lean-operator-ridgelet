import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Radon–Nikodym densities for Hilbert-valued measures

The Riesz representation theorem applied to the pairing integral on `L²(|Γ|; Y)`
constructs a Bochner density of every Hilbert-valued measure of finite variation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace MeasureTheory.VectorMeasure

variable {X Y : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The pairing integral of an `L²` function against a finite-variation vector measure. -/
def l2Pairing (Γ : VectorMeasure X Y) [IsFiniteMeasure Γ.variation] :
    (X →₂[Γ.variation] Y) →ₗ[ℝ] ℝ where
  toFun f := ∫ᵛ x, f x ∂[innerSL ℝ; Γ]
  map_add' f g := by
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    exact integral_add ((Lp.memLp f).integrable (by norm_num))
      ((Lp.memLp g).integrable (by norm_num))
  map_smul' c f := by
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    exact integral_smul f Γ (innerSL ℝ) c

omit [InnerProductSpace ℝ Y] [CompleteSpace Y] in
/-- The `L¹` norm is bounded by a constant times the `L²` norm on a finite measure space. -/
theorem integral_norm_le_l2_norm (μ : Measure X) [IsFiniteMeasure μ] (f : X →₂[μ] Y) :
    ∫ x, ‖f x‖ ∂μ ≤
      ‖indicatorConstLp (E := ℝ) 2 MeasurableSet.univ (measure_ne_top μ Set.univ) 1‖ * ‖f‖ := by
  let r := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have hr : (r : X → ℝ) =ᵐ[μ] fun x => ‖f x‖ := MemLp.coeFn_toLp _
  have hrn : ‖r‖ = ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]
  have he : ∫ x, ‖f x‖ ∂μ =
      inner ℝ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ)) r := by
    rw [L2.inner_indicatorConstLp_one, Measure.restrict_univ]
    exact MeasureTheory.integral_congr_ae hr.symm
  rw [he, ← hrn]
  exact real_inner_le_norm _ _

/-- The pairing integral is a bounded linear functional on `L²` of the variation measure. -/
def l2PairingCLM (Γ : VectorMeasure X Y) [IsFiniteMeasure Γ.variation] :
    (X →₂[Γ.variation] Y) →L[ℝ] ℝ :=
  (l2Pairing Γ).mkContinuous
    (‖(innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ)‖ *
      ‖indicatorConstLp (E := ℝ) 2 MeasurableSet.univ
        (measure_ne_top Γ.variation Set.univ) 1‖) (fun f => by
    exact (norm_integral_le_integral_norm (B := innerSL ℝ)).trans
      ((mul_le_mul_of_nonneg_left (integral_norm_le_l2_norm Γ.variation f)
        (norm_nonneg (innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ))).trans_eq (mul_assoc _ _ _).symm))

/-- Every Hilbert-valued vector measure of finite variation has an integrable density
with respect to its variation. -/
theorem exists_withDensity_variation (Γ : VectorMeasure X Y) [IsFiniteMeasure Γ.variation] :
    ∃ g : X → Y, Integrable g Γ.variation ∧ Γ = Γ.variation.withDensityᵥ g := by
  let g := (InnerProductSpace.toDual ℝ (X →₂[Γ.variation] Y)).symm (l2PairingCLM Γ)
  have hg : Integrable (g : X → Y) Γ.variation := (Lp.memLp g).integrable (by norm_num)
  refine ⟨g, hg, ?_⟩
  ext s hs
  rw [withDensityᵥ_apply hg hs]
  apply ext_inner_left ℝ
  intro y
  let f : X →₂[Γ.variation] Y := indicatorConstLp 2 hs (measure_ne_top Γ.variation s) y
  have hR : inner ℝ g f = l2PairingCLM Γ f := InnerProductSpace.toDual_symm_apply
  have hleft : inner ℝ g f = inner ℝ y (∫ x in s, g x ∂Γ.variation) := by
    rw [real_inner_comm]
    exact L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hs
      (measure_ne_top Γ.variation s) y g
  have hright : l2PairingCLM Γ f = inner ℝ y (Γ s) := by
    change (∫ᵛ x, f x ∂[innerSL ℝ; Γ]) = _
    rw [integral_congr_ae (show (f : X → Y) =ᵐ[Γ.variation] s.indicator (fun _ => y)
        from indicatorConstLp_coeFn),
      integral_eq_setToFun, setToFun_indicator_const _ hs (measure_ne_top Γ.variation s)]
    rfl
  rw [hleft, hright] at hR
  exact hR.symm

/-- Polar decomposition of a finite-variation Hilbert-valued measure. -/
theorem exists_withDensityᵥ_variation_eq (Γ : VectorMeasure X Y) [IsFiniteMeasure Γ.variation] :
    ∃ g : X → Y, (∀ᵐ x ∂Γ.variation, ‖g x‖ = 1) ∧ Γ = Γ.variation.withDensityᵥ g := by
  obtain ⟨g, hg, hΓ⟩ := exists_withDensity_variation Γ
  refine ⟨g, ?_, hΓ⟩
  have hvar : Γ.variation = Γ.variation.withDensity (fun x => ‖g x‖ₑ) := by
    conv_lhs => rw [hΓ]
    exact Measure.variation_withDensityᵥ hg
  have he : (fun x => ‖g x‖ₑ) =ᵐ[Γ.variation] fun _ => (1 : ℝ≥0∞) := by
    apply (withDensity_eq_iff_of_sigmaFinite hg.aestronglyMeasurable.enorm aemeasurable_const).mp
    rw [← hvar]
    exact withDensity_one.symm
  filter_upwards [he] with x hx
  rw [enorm_eq_nnnorm, ENNReal.coe_eq_one] at hx
  rw [← coe_nnnorm, hx, NNReal.coe_one]

end MeasureTheory.VectorMeasure
