import OperatorRidgelet.ToMathlib.AddTorusFourier
import OperatorRidgelet.Examples.Convolution
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Fourier coefficients and translation on the periodic convolution space -/

noncomputable section
open scoped ComplexConjugate

namespace OperatorRidgelet
open MeasureTheory
variable {d : ℕ}

/-- The real torus `L²` space has a countable topological basis. -/
instance (d : ℕ) : SecondCountableTopology (TorusL2 d) := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- The complex torus `L²` space has a countable topological basis. -/
instance (d : ℕ) : SecondCountableTopology (TorusL2C d) := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- The normalized complex Fourier Hilbert basis on the torus of period `2π`. -/
def torusFourierBasis (d : ℕ) : HilbertBasis (Fin d → ℤ) ℂ (TorusL2C d) :=
  AddTorus.mFourierBasis

/-- The Fourier Hilbert-basis coordinates agree with the integral Fourier coefficients. -/
theorem torusFourierBasis_repr (f : TorusL2C d) (n : Fin d → ℤ) :
    (torusFourierBasis d).repr f n = torusFourierCoeff f n := by
  change (AddTorus.mFourierBasis (T := 2 * Real.pi)).repr f n = _
  have h := AddTorus.mFourierBasis_repr (T := 2 * Real.pi) f n
  convert! h using 1
  simp only [AddTorus.mFourierCoeff, AddTorus.mFourier, Pi.neg_apply, fourier_neg, map_prod,
    ContinuousMap.coe_mk, smul_eq_mul, torusFourierCoeff, torusCharacter, torusHaar]
  rfl

/-- Equality of all Fourier coefficients determines a complex torus `L²` function. -/
theorem torusFourierCoeff_ext {f g : TorusL2C d}
    (h : ∀ n, torusFourierCoeff f n = torusFourierCoeff g n) : f = g := by
  apply (torusFourierBasis d).repr.injective
  ext n
  simpa only [torusFourierBasis_repr] using h n

/-- Embedding a real `L²` function into the complex space preserves its coefficients. -/
theorem torusFourierCoeff_ofReal_compLp (f : TorusL2 d) (n : Fin d → ℤ) :
    torusFourierCoeff (Complex.ofRealCLM.compLp f) n =
      torusFourierCoeff (fun t => (f t : ℂ)) n := by
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' f] with t ht
  rw [ht, Complex.ofRealCLM_apply]

/-- Equality of all complex Fourier coefficients determines a real torus function. -/
theorem torusFourierCoeff_real_ext {f g : TorusL2 d}
    (h : ∀ n, torusFourierCoeff (fun t => (f t : ℂ)) n =
      torusFourierCoeff (fun t => (g t : ℂ)) n) : f = g := by
  have he : Complex.ofRealCLM.compLp f = Complex.ofRealCLM.compLp g := by
    apply torusFourierCoeff_ext
    simpa only [torusFourierCoeff_ofReal_compLp] using h
  apply Lp.ext
  filter_upwards [Lp.ext_iff.mp he, Complex.ofRealCLM.coeFn_compLp' f,
    Complex.ofRealCLM.coeFn_compLp' g] with t ht hf hg
  rw [hf, hg, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply] at ht
  exact Complex.ofReal_injective ht

/-- A torus character sends addition to multiplication. -/
theorem torusCharacter_add (n : Fin d → ℤ) (x y : Torus d) :
    torusCharacter n (x + y) = torusCharacter n x * torusCharacter n y := by
  simp only [torusCharacter, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Translation multiplies each Fourier coefficient by the corresponding character. -/
theorem torusFourierCoeff_torusTranslate (f : TorusL2 d) (z : Torus d) (n : Fin d → ℤ) :
    torusFourierCoeff (fun t => (torusTranslate d z f t : ℂ)) n =
      conj (torusCharacter n z) * torusFourierCoeff (fun t => (f t : ℂ)) n := by
  have hae := Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right (torusHaar d) z)
  unfold torusFourierCoeff
  calc
    _ = ∫ t, conj (torusCharacter n t) * (f (t-z) : ℂ) ∂torusHaar d := by
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      change conj (torusCharacter n t) *
        ((Lp.compMeasurePreserving _ _ f) t : ℂ) = _
      rw [ht, Function.comp_apply]
    _ = ∫ t, conj (torusCharacter n (t+z)) * (f t : ℂ) ∂torusHaar d := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun t => conj (torusCharacter n t) * (f (t-z) : ℂ)) z).symm
    _ = _ := by
      simp_rw [torusCharacter_add, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext t
      ring

/-- The Bessel Fourier multiplier commutes with torus translations. -/
theorem besselOperator_commutes_translate (s : ℝ) (z : Torus d) (x : TorusL2 d) :
    besselOperator d s (torusTranslate d z x) =
      torusTranslate d z (besselOperator d s x) := by
  unfold besselOperator
  split_ifs with h
  · apply torusFourierCoeff_real_ext
    intro n
    rw [h.choose_spec, torusFourierCoeff_torusTranslate, torusFourierCoeff_torusTranslate,
      h.choose_spec]
    ring
  · simp

/-- Translation by the negative parameter cancels translation. -/
theorem torusTranslate_neg_cancel (z : Torus d) (x : TorusL2 d) :
    torusTranslate d (-z) (torusTranslate d z x) = x := by
  apply Lp.ext
  filter_upwards [torusTranslate_coeFn_ae (-z) (torusTranslate d z x),
    (measurePreserving_sub_right (torusHaar d) (-z)).quasiMeasurePreserving.ae_eq_comp
      (torusTranslate_coeFn_ae z x)] with t h1 h2
  simpa only [Function.comp_apply, h1, sub_neg_eq_add, add_sub_cancel_right] using h2

/-- Translation on the torus as a real linear isometric equivalence of `L²`. -/
def torusTranslateEquiv (d : ℕ) (z : Torus d) : TorusL2 d ≃ₗᵢ[ℝ] TorusL2 d :=
  { torusTranslate d z with
    invFun := torusTranslate d (-z)
    left_inv := torusTranslate_neg_cancel z
    right_inv := by intro x; simpa using torusTranslate_neg_cancel (-z) x }

end OperatorRidgelet
