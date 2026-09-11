import OperatorRidgelet.Examples.ConvolutionFourier
import OperatorRidgelet.ToMathlib.AEEqFunComplex

/-! # Infinite rank and non-cylindricity of periodic convolution layers -/

noncomputable section
open MeasureTheory Filter
open scoped RealInnerProductSpace ComplexConjugate
namespace OperatorRidgelet
variable {d : ℕ}


theorem torusFourierBasis_coeFn (n : Fin d → ℤ) :
    (torusFourierBasis d n : Torus d → ℂ) =ᵐ[torusHaar d] torusCharacter n := by
  change (AddTorus.mFourierBasis n : Torus d → ℂ) =ᵐ[torusHaar d] _
  rw [AddTorus.coe_mFourierBasis]
  exact AddTorus.coeFn_mFourierLp 2 n

theorem continuous_torusCharacter (n : Fin d → ℤ) : Continuous (torusCharacter n) := by
  unfold torusCharacter
  fun_prop

theorem norm_torusCharacter (n : Fin d → ℤ) (t : Torus d) : ‖torusCharacter n t‖ = 1 := by
  simp only [torusCharacter, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem torusCharacter_neg (n : Fin d → ℤ) (t : Torus d) :
    torusCharacter n (-t) = conj (torusCharacter n t) := by
  simp only [torusCharacter, Pi.neg_apply, fourier_apply, zsmul_neg, AddCircle.toCircle_neg,
    Circle.coe_inv, map_prod]
  congr 1
  ext j
  simpa only [Circle.coe_inv] using Circle.coe_inv_eq_conj (AddCircle.toCircle (n j • t j))

theorem integral_torusCharacter_convolution (k : TorusL2 d) (n : Fin d → ℤ) (y : Torus d) :
    (∫ t, (k (y-t) : ℂ) * torusCharacter n t ∂torusHaar d) =
      torusFourierCoeff (fun t => (k t : ℂ)) n * torusCharacter n y := by
  rw [← integral_sub_left_eq_self (fun t => (k (y-t) : ℂ) * torusCharacter n t) (torusHaar d) y]
  simp only [sub_sub_cancel]
  simp_rw [sub_eq_add_neg, torusCharacter_add, torusCharacter_neg]
  unfold torusFourierCoeff
  rw [← integral_mul_const]
  congr 1
  funext t
  ring

theorem layerA_conv_coeFn (k x : TorusL2 d) :
    (layerA (torusHaar d) (convDirection k) x : Torus d → ℝ) =ᵐ[torusHaar d]
      fun y => ∫ t, k (y-t) * x t ∂torusHaar d := by
  classical
  have ha : AEStronglyMeasurable (convDirection k) (torusHaar d) :=
    (continuous_convDirection k).aestronglyMeasurable
  change (if h : AEStronglyMeasurable (convDirection k) (torusHaar d) then
      AEEqFun.mk _ (h.inner aestronglyMeasurable_const) else 0 : Torus d →ₘ[torusHaar d] ℝ) =ᵐ[_] _
  rw [dif_pos ha]
  filter_upwards [AEEqFun.coeFn_mk (fun y => ⟪convDirection k y, x⟫)
    (ha.inner (aestronglyMeasurable_const (b := x)))] with y hy
  rw [hy, inner_convDirection]

theorem integrable_character_convolution (k : TorusL2 d) (n : Fin d → ℤ) (y : Torus d) :
    Integrable (fun t => (k (y-t) : ℂ) * torusCharacter n t) (torusHaar d) := by
  have hk : Integrable (fun t => k (y-t)) (torusHaar d) :=
    (Measure.measurePreserving_sub_left (torusHaar d) y).integrable_comp_of_integrable
      ((Lp.memLp k).integrable one_le_two)
  exact hk.ofReal.mul_bdd (c := 1) (continuous_torusCharacter n).aestronglyMeasurable
    (Eventually.of_forall fun t => (norm_torusCharacter n t).le)

theorem convolution_real_character (k : TorusL2 d) (n : Fin d → ℤ) (y : Torus d) :
    (∫ t, k (y-t) * (Complex.reCLM.compLp (torusFourierBasis d n)) t ∂torusHaar d) =
      (torusFourierCoeff (fun t => (k t : ℂ)) n * torusCharacter n y).re := by
  rw [← integral_torusCharacter_convolution]
  trans ∫ t, ((k (y-t) : ℂ) * torusCharacter n t).re ∂torusHaar d
  swap
  · exact integral_re (integrable_character_convolution k n y)
  apply integral_congr_ae
  filter_upwards [Complex.reCLM.coeFn_compLp' (torusFourierBasis d n),
    torusFourierBasis_coeFn n] with t h1 h2
  rw [h1, h2]
  simp [Complex.mul_re]

theorem convolution_imag_character (k : TorusL2 d) (n : Fin d → ℤ) (y : Torus d) :
    (∫ t, k (y-t) * (Complex.imCLM.compLp (torusFourierBasis d n)) t ∂torusHaar d) =
      (torusFourierCoeff (fun t => (k t : ℂ)) n * torusCharacter n y).im := by
  rw [← integral_torusCharacter_convolution]
  trans ∫ t, ((k (y-t) : ℂ) * torusCharacter n t).im ∂torusHaar d
  swap
  · exact integral_im (integrable_character_convolution k n y)
  apply integral_congr_ae
  filter_upwards [Complex.imCLM.coeFn_compLp' (torusFourierBasis d n),
    torusFourierBasis_coeFn n] with t h1 h2
  rw [h1, h2]
  simp [Complex.mul_im]

theorem complexified_layerA_character (k : TorusL2 d) (n : Fin d → ℤ) :
    aeOfReal (torusHaar d) (layerA (torusHaar d) (convDirection k)
      (Complex.reCLM.compLp (torusFourierBasis d n))) +
    Complex.I • aeOfReal (torusHaar d) (layerA (torusHaar d) (convDirection k)
      (Complex.imCLM.compLp (torusFourierBasis d n))) =
    ((torusFourierCoeff (fun t => (k t : ℂ)) n • torusFourierBasis d n : TorusL2C d) :
      Torus d →ₘ[torusHaar d] ℂ) := by
  let ar := layerA (torusHaar d) (convDirection k) (Complex.reCLM.compLp (torusFourierBasis d n))
  let ai := layerA (torusHaar d) (convDirection k) (Complex.imCLM.compLp (torusFourierBasis d n))
  apply AEEqFun.ext
  filter_upwards [AEEqFun.coeFn_add (aeOfReal (torusHaar d) ar)
      (Complex.I • aeOfReal (torusHaar d) ai),
    AEEqFun.coeFn_smul Complex.I (aeOfReal (torusHaar d) ai),
    AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal ar,
    AEEqFun.coeFn_comp Complex.ofReal Complex.continuous_ofReal ai,
    layerA_conv_coeFn k (Complex.reCLM.compLp (torusFourierBasis d n)),
    layerA_conv_coeFn k (Complex.imCLM.compLp (torusFourierBasis d n)),
    Lp.coeFn_smul (torusFourierCoeff (fun t => (k t : ℂ)) n) (torusFourierBasis d n),
    torusFourierBasis_coeFn n] with y h1 h2 h3 h4 h5 h6 h7 h8
  simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply] at *
  change (aeOfReal (torusHaar d) ar + Complex.I • aeOfReal (torusHaar d) ai) y = _
  rw [h1, h2]
  change (AEEqFun.comp Complex.ofReal Complex.continuous_ofReal ar) y +
    Complex.I * (AEEqFun.comp Complex.ofReal Complex.continuous_ofReal ai) y = _
  rw [h3, h4]
  change ((layerA (torusHaar d) (convDirection k) _ y : ℝ) : ℂ) +
    Complex.I * ((layerA (torusHaar d) (convDirection k) _ y : ℝ) : ℂ) = _
  rw [h5, h6, convolution_real_character, convolution_imag_character, h7, h8]
  simp only [smul_eq_mul]
  rw [mul_comm Complex.I, Complex.re_add_im]

def aeComplexPair (k : TorusL2 d) :
    (LinearMap.range (layerA (torusHaar d) (convDirection k)) ×
      LinearMap.range (layerA (torusHaar d) (convDirection k))) →ₗ[ℝ]
      (Torus d →ₘ[torusHaar d] ℂ) where
  toFun p := aeOfReal (torusHaar d) p.1.val + Complex.I • aeOfReal (torusHaar d) p.2.val
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
    map_add, smul_add]; abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, RingHom.id_apply,
      smul_add, smul_comm c Complex.I]

def torusLpToAE : TorusL2C d →ₗ[ℂ] (Torus d →ₘ[torusHaar d] ℂ) where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hasInfiniteRank_conv (k : TorusL2 d)
    (hk : Set.Infinite {n : Fin d → ℤ | torusFourierCoeff (fun t => (k t : ℂ)) n ≠ 0}) :
    HasInfiniteRank (layerA (torusHaar d) (convDirection k)) := by
  classical
  intro hfin
  letI := hfin
  let ι := {n : Fin d → ℤ // torusFourierCoeff (fun t => (k t : ℂ)) n ≠ 0}
  letI : Infinite ι := hk.to_subtype
  let c (n : ι) := torusFourierCoeff (fun t => (k t : ℂ)) n.val
  let e (n : ι) : TorusL2C d := c n • torusFourierBasis d n.val
  have hli : LinearIndependent ℂ e := by
    have hb := (torusFourierBasis d).orthonormal.linearIndependent.comp
      (fun n : ι => n.val) Subtype.val_injective
    convert! hb.units_smul (fun n => Units.mk0 (c n) n.property) using 1
  have hae : LinearIndependent ℝ (fun n : ι => (e n : Torus d →ₘ[torusHaar d] ℂ)) :=
    (hli.map' torusLpToAE (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).restrict_scalars' ℝ
  let v (n : ι) : LinearMap.range (aeComplexPair k) :=
    ⟨(e n : Torus d →ₘ[torusHaar d] ℂ), by
      refine ⟨(⟨_, ⟨Complex.reCLM.compLp (torusFourierBasis d n.val), rfl⟩⟩,
        ⟨_, ⟨Complex.imCLM.compLp (torusFourierBasis d n.val), rfl⟩⟩), ?_⟩
      exact complexified_layerA_character k n.val⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (LinearMap.range (aeComplexPair k)).subtype hae
  haveI : Finite ι := hv.finite
  exact not_finite ι

theorem not_isCylindrical_convolution_gaussian (k ψ : TorusL2 d)
    (hk : Set.Infinite {n : Fin d → ℤ | torusFourierCoeff (fun t => (k t : ℂ)) n ≠ 0})
    (hψ : torusFourierCoeff (fun t => (ψ t : ℂ)) 0 ≠ 0) :
    ¬ IsCylindrical (layerObservable (torusHaar d) (convDirection k) (convOutput ψ)
      gaussianFun (torusOne d)) := by
  let c := torusFourierCoeff (fun t => (ψ t : ℂ)) 0
  have hnc := (isLayerData_conv k ψ).not_isCylindrical_layerObservable_gaussianFun
    (c • torusOne d) (hasInfiniteRank_conv k hk) (Eventually.of_forall fun y => ?_)
  · rintro ⟨m, L, G, hG⟩
    apply hnc
    refine ⟨m, L, fun z => conj c * G z, ?_⟩
    funext x
    change inner ℂ (c • torusOne d) _ = _
    rw [inner_smul_left]
    change conj c * layerObservable _ _ _ _ _ x = _
    rw [hG]
    rfl
  · simp only [layerWeight, inner_smul_left, inner_torusOne_convOutput]
    change 0 < (conj c * c).re ∧ (conj c * c).im = 0
    rw [← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_pos.mpr hψ, rfl⟩

end OperatorRidgelet
