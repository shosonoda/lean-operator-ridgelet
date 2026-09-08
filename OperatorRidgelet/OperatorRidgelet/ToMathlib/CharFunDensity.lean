import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier uniqueness for integrable densities

A complex integrable density `f` against a finite measure `μ` on a complete second-countable
real inner product space is determined by its Fourier transform
`t ↦ ∫ f(x) exp(i⟪x, t⟫) dμ(x)`: if the transform vanishes identically, then `f = 0`
`μ`-almost everywhere.  The proof reduces to `MeasureTheory.Measure.ext_of_charFun` by splitting
`f` into real and imaginary parts and each of those into positive and negative parts, which
are densities of finite measures.
-/

open scoped ENNReal RealInnerProductSpace ComplexConjugate

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- The characteristic function of the measure with density `max u 0` against `μ`, in terms of
the density. -/
theorem charFun_withDensity_ofReal (u : E → ℝ) (hu : AEMeasurable u μ) (t : E) :
    charFun (μ.withDensity fun x => ENNReal.ofReal (u x)) t =
      ∫ x, ((max (u x) 0 : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀ hu.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal', Complex.real_smul]

section OpensMeasurable

variable [OpensMeasurableSpace E]

/-- Multiplying an integrable function by the unimodular character `exp(i⟪x, t⟫)` preserves
integrability. -/
theorem Integrable.mul_exp_inner_mul_I {g : E → ℂ} (hg : Integrable g μ) (t : E) :
    Integrable (fun x => g x * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := by
  have hm : AEStronglyMeasurable (fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ :=
    (by fun_prop : Continuous fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I))
      |>.aestronglyMeasurable
  have := hg.bdd_mul (c := 1) hm
    (Filter.Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [mul_comm] using this

end OpensMeasurable

/-- The complex conjugate of an integrable function is integrable. -/
theorem Integrable.conj_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)
    (Filter.Eventually.of_forall fun x => by rw [Complex.norm_conj])

variable [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E]

/-- **Fourier uniqueness for real densities**: a real integrable function whose Fourier
transform against the finite measure `μ` vanishes identically is zero almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_integral_mul_exp_eq_zero_real [IsFiniteMeasure μ]
    {u : E → ℝ} (hu : Integrable u μ)
    (h : ∀ t : E, ∫ x, (u x : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ = 0) :
    u =ᵐ[μ] 0 := by
  set μp : Measure E := μ.withDensity fun x => ENNReal.ofReal (u x) with hμp
  set μm : Measure E := μ.withDensity fun x => ENNReal.ofReal (-u x) with hμm
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hu.2
  haveI : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hu.neg.2
  have hpos : ∀ t : E, Integrable
      (fun x => ((max (u x) 0 : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := fun t =>
    (hu.pos_part.ofReal (𝕜 := ℂ)).mul_exp_inner_mul_I t
  have hneg : ∀ t : E, Integrable
      (fun x => ((max (-u x) 0 : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := fun t =>
    (hu.neg.pos_part.ofReal (𝕜 := ℂ)).mul_exp_inner_mul_I t
  have hchar : charFun μp = charFun μm := by
    funext t
    rw [hμp, hμm, charFun_withDensity_ofReal u hu.aemeasurable,
      charFun_withDensity_ofReal (fun x => -u x) hu.aemeasurable.neg, ← sub_eq_zero,
      ← integral_sub (hpos t) (hneg t), ← h t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [← sub_mul]
    congr 1
    have : max (u x) 0 - max (-u x) 0 = u x := by
      rcases le_total (u x) 0 with hx | hx
      · rw [max_eq_right hx, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left hx, max_eq_right (by linarith)]
        ring
    rw [← Complex.ofReal_sub, this]
  have hμ : μp = μm := Measure.ext_of_charFun hchar
  have hfin : ∫⁻ x, ENNReal.ofReal (u x) ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => ?_) hu.2)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hae := (withDensity_eq_iff hu.aemeasurable.ennreal_ofReal
    hu.aemeasurable.neg.ennreal_ofReal hfin).mp hμ
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply]
  have hx' : ENNReal.ofReal (u x) = ENNReal.ofReal (-u x) := by simpa using hx
  rcases lt_trichotomy (u x) 0 with hlt | heq | hgt
  · exfalso
    rw [ENNReal.ofReal_eq_zero.mpr hlt.le] at hx'
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hx'.symm
  · exact heq
  · exfalso
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith : -u x ≤ 0)] at hx'
    exact (ENNReal.ofReal_pos.mpr hgt).ne' hx'

/-- **Fourier uniqueness for complex densities**: a complex integrable function whose Fourier
transform against the finite measure `μ` vanishes identically is zero almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_integral_mul_exp_eq_zero [IsFiniteMeasure μ]
    {f : E → ℂ} (hf : Integrable f μ)
    (h : ∀ t : E, ∫ x, f x * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have hconj : ∀ t : E, ∫ x, conj (f x) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ = 0 := by
    intro t
    have h' := h (-t)
    have : (fun x => conj (f x) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) =
        fun x => conj (f x * Complex.exp ((⟪x, -t⟫ : ℝ) * Complex.I)) := by
      funext x
      rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
        inner_neg_right]
      congr 2
      push_cast
      ring
    rw [this, integral_conj, h', map_zero]
  have hre : (fun x => Complex.re (f x)) =ᵐ[μ] 0 := by
    refine hf.re.ae_eq_zero_of_forall_integral_mul_exp_eq_zero_real fun t => ?_
    simp only [RCLike.re_to_complex]
    have : (fun x => ((Complex.re (f x) : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) =
        fun x => (1 / 2 : ℂ) * (f x * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) +
          conj (f x) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) := by
      funext x
      rw [← add_mul, Complex.add_conj]
      push_cast
      ring
    rw [this, integral_const_mul, integral_add (hf.mul_exp_inner_mul_I t)
      (hf.conj_comp.mul_exp_inner_mul_I t), h t, hconj t, add_zero, mul_zero]
  have him : (fun x => Complex.im (f x)) =ᵐ[μ] 0 := by
    refine hf.im.ae_eq_zero_of_forall_integral_mul_exp_eq_zero_real fun t => ?_
    simp only [RCLike.im_to_complex]
    have : (fun x => ((Complex.im (f x) : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) =
        fun x => (1 / (2 * Complex.I) : ℂ) * (f x * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) -
          conj (f x) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) := by
      funext x
      rw [← sub_mul, Complex.sub_conj]
      push_cast
      field_simp
    rw [this, integral_const_mul, integral_sub (hf.mul_exp_inner_mul_I t)
      (hf.conj_comp.mul_exp_inner_mul_I t), h t, hconj t, sub_zero, mul_zero]
  filter_upwards [hre, him] with x hx₁ hx₂
  simp only [Pi.zero_apply] at hx₁ hx₂ ⊢
  exact Complex.ext hx₁ hx₂

end MeasureTheory
