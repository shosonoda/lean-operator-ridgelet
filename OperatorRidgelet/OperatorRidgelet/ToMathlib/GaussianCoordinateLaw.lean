import OperatorRidgelet.ToMathlib.CharFunCoordinate
import OperatorRidgelet.ToMathlib.GaussianRealIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laws of Gaussian coordinates and a mixed Gaussian integral

For a probability measure `μ` on a real inner product space whose characteristic function along
the span of `v` (or of `v, w`) is Gaussian:

* `map_inner_eq_gaussianReal`: the law of the coordinate `⟪·, v⟫` is `𝒩(0, σ²)`;
* `ae_inner_eq_zero_of_charFun`: a coordinate with characteristic function `1` vanishes a.e.;
* `sq_le_mul_of_charFun`: the covariance data `(σ², r, τ²)` of two coordinates satisfy
  `r² ≤ σ² τ²`;
* `map_inner_pair_eq_map_prod_gaussianReal`: the joint law of `(⟪·, v⟫, ⟪·, w⟫)` is the image
  of `𝒩(0, σ²) ⊗ 𝒩(0, τ² - r²/σ²)` under the shear `(z, u) ↦ (z, (r/σ²) z + u)`;
* `integral_inner_pair_eq_integral_prod_gaussianReal`: the corresponding change of variables
  for integrals of continuous functions of the two coordinates;
* `integral_exp_neg_inner_sq_half_mul_exp_neg_inner_mul_I`: the mixed Gaussian integral
  `∫ e^{-⟪x,v⟫²/2} e^{-i⟪x,w⟫} μ(dx) = (1 + σ²)^{-1/2} exp(-τ²/2 + r²/(2(1 + σ²)))`.

Here `σ² = Var ⟪·, v⟫`, `τ² = Var ⟪·, w⟫`, and `r = Cov(⟪·, v⟫, ⟪·, w⟫)` are read off the
characteristic function `charFun μ (s • v + t • w) = exp(-(s²σ² + 2str + t²τ²)/2)`.

The statements are first proved for an arbitrary σ-algebra on `E` under the hypothesis that
the coordinates involved are `AEMeasurable` (primed names), and then specialized to the Borel
case, where the coordinates are continuous.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace NNReal ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-! ### Characteristic functions of a.e.-measurable coordinates -/

/-- The characteristic function of the law of an a.e.-measurable coordinate `x ↦ ⟪x, v⟫` is
`s ↦ charFun μ (s • v)`. -/
theorem charFun_map_inner_right' (μ : Measure E) (v : E)
    (hv : AEMeasurable (fun x => ⟪x, v⟫) μ) (s : ℝ) :
    charFun (μ.map fun x => ⟪x, v⟫) s = charFun μ (s • v) := by
  rw [charFun_apply_real, charFun_apply, integral_map hv (Continuous.aestronglyMeasurable
    (by fun_prop))]
  congr 1
  funext x
  rw [real_inner_smul_right, Complex.ofReal_mul]

/-- The characteristic function of the joint law of two a.e.-measurable coordinates, taken in
the Hilbert space `WithLp 2 (ℝ × ℝ)`, is `t ↦ charFun μ (t₁ • v + t₂ • w)`. -/
theorem charFun_map_inner_pair' (μ : Measure E) (v w : E)
    (hvw : AEMeasurable (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) μ) (t : WithLp 2 (ℝ × ℝ)) :
    charFun (μ.map fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) t =
      charFun μ ((WithLp.ofLp t).1 • v + (WithLp.ofLp t).2 • w) := by
  rw [charFun_apply, charFun_apply, integral_map hvw (Continuous.aestronglyMeasurable
    (by fun_prop))]
  congr 1
  funext x
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial, inner_add_right,
    real_inner_smul_right]

/-! ### The law of one coordinate -/

/-- If `charFun μ (s • v) = exp(-σ² s²/2)` for all `s` and the coordinate `⟪·, v⟫` is
a.e.-measurable, its law is `𝒩(0, σ²)`. -/
theorem map_inner_eq_gaussianReal' (μ : Measure E) [IsProbabilityMeasure μ] (v : E)
    (hv : AEMeasurable (fun x => ⟪x, v⟫) μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (h : ∀ s : ℝ, charFun μ (s • v) = Complex.exp (-((σ2 * s ^ 2 / 2 : ℝ) : ℂ))) :
    μ.map (fun x => ⟪x, v⟫) = gaussianReal 0 σ2.toNNReal := by
  haveI : IsProbabilityMeasure (μ.map fun x => ⟪x, v⟫) :=
    Measure.isProbabilityMeasure_map hv
  refine Measure.ext_of_charFun (funext fun s => ?_)
  rw [charFun_map_inner_right' μ v hv, h, charFun_gaussianReal, Real.coe_toNNReal σ2 hσ]
  congr 1
  push_cast
  ring

/-- If `charFun μ (s • v) = 1` for all `s` and `⟪·, v⟫` is a.e.-measurable, then `⟪·, v⟫ = 0`
almost everywhere. -/
theorem ae_inner_eq_zero_of_charFun' (μ : Measure E) [IsProbabilityMeasure μ] (v : E)
    (hv : AEMeasurable (fun x => ⟪x, v⟫) μ) (h : ∀ s : ℝ, charFun μ (s • v) = 1) :
    ∀ᵐ x ∂μ, ⟪x, v⟫ = 0 := by
  have hmap := map_inner_eq_gaussianReal' μ v hv (σ2 := 0) le_rfl (fun s => by rw [h]; simp)
  rw [Real.toNNReal_zero, gaussianReal_zero_var] at hmap
  have hs : MeasurableSet {t : ℝ | t ≠ 0} := (measurableSet_singleton 0).compl
  have key := Measure.map_apply_of_aemeasurable (μ := μ) hv hs
  rw [hmap, Measure.dirac_apply' _ hs] at key
  rw [ae_iff]
  have hind : ({t : ℝ | t ≠ 0}.indicator (1 : ℝ → ℝ≥0∞) 0) = 0 := by
    simp
  rw [hind] at key
  simpa [Set.preimage] using key.symm

/-! ### The covariance data of two coordinates -/

/-- The covariance data `(σ², r, τ²)` of a Gaussian characteristic function along a plane are
positive semidefinite: `r² ≤ σ² τ²`. -/
theorem sq_le_mul_of_charFun (μ : Measure E) [IsProbabilityMeasure μ] (v w : E) {σ2 r τ2 : ℝ}
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ))) :
    r ^ 2 ≤ σ2 * τ2 := by
  have hQ : ∀ s t : ℝ, 0 ≤ s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2 := by
    intro s t
    have h1 := norm_charFun_le_one (μ := μ) (s • v + t • w)
    rw [h s t, ← Complex.ofReal_neg, Complex.norm_exp_ofReal, Real.exp_le_one_iff] at h1
    linarith
  have hd := discrim_le_zero (a := σ2) (b := 2 * r) (c := τ2) fun s => by
    have := hQ s 1
    nlinarith [this]
  rw [discrim] at hd
  nlinarith [hd]

/-! ### The joint law of two coordinates -/

/-- For `σ² > 0`, the joint law of a.e.-measurable coordinates `(⟪·, v⟫, ⟪·, w⟫)` (in
`WithLp 2 (ℝ × ℝ)`) is the image of `𝒩(0, σ²) ⊗ 𝒩(0, τ² - r²/σ²)` under the shear
`(z, u) ↦ (z, (r/σ²) z + u)`. -/
theorem map_inner_pair_eq_map_prod_gaussianReal' (μ : Measure E) [IsProbabilityMeasure μ]
    (v w : E) (hvw : AEMeasurable (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) μ) {σ2 r τ2 : ℝ}
    (hσ : 0 < σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ))) :
    μ.map (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) =
      ((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)).map
        (fun p : ℝ × ℝ => WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2)) := by
  have hδ : 0 ≤ τ2 - r ^ 2 / σ2 := by
    have := sq_le_mul_of_charFun μ v w h
    rw [sub_nonneg, div_le_iff₀ hσ]
    linarith
  have hΨ : Measurable fun p : ℝ × ℝ => WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2) := by fun_prop
  haveI : IsProbabilityMeasure (μ.map fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) :=
    Measure.isProbabilityMeasure_map hvw
  haveI : IsProbabilityMeasure
      (((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)).map
        (fun p : ℝ × ℝ => WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2))) :=
    Measure.isProbabilityMeasure_map hΨ.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_inner_pair' μ v w hvw, h, charFun_apply,
    integral_map hΨ.aemeasurable (by fun_prop)]
  have hfun : ∀ p : ℝ × ℝ,
      Complex.exp ((⟪WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2), t⟫ : ℝ) * I) =
        Complex.exp (((t.ofLp.1 + r / σ2 * t.ofLp.2 : ℝ) : ℂ) * p.1 * I) *
          Complex.exp (((t.ofLp.2 : ℝ) : ℂ) * p.2 * I) := by
    intro p
    rw [← Complex.exp_add, WithLp.prod_inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring_nf
  simp_rw [hfun]
  have hprod : ∫ p : ℝ × ℝ, Complex.exp (((t.ofLp.1 + r / σ2 * t.ofLp.2 : ℝ) : ℂ) * p.1 * I) *
        Complex.exp (((t.ofLp.2 : ℝ) : ℂ) * p.2 * I)
        ∂((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)) =
      (∫ a : ℝ, Complex.exp (((t.ofLp.1 + r / σ2 * t.ofLp.2 : ℝ) : ℂ) * a * I)
          ∂gaussianReal 0 σ2.toNNReal) *
        ∫ b : ℝ, Complex.exp (((t.ofLp.2 : ℝ) : ℂ) * b * I)
          ∂gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal :=
    integral_prod_mul (fun a : ℝ => Complex.exp (((t.ofLp.1 + r / σ2 * t.ofLp.2 : ℝ) : ℂ) * a * I))
      (fun b : ℝ => Complex.exp (((t.ofLp.2 : ℝ) : ℂ) * b * I))
  rw [hprod, ← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal,
    charFun_gaussianReal, ← Complex.exp_add, Real.coe_toNNReal _ hσ.le, Real.coe_toNNReal _ hδ]
  have hσc : (σ2 : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  congr 1
  push_cast
  field_simp
  ring

/-- Change of variables for integrals of continuous functions of two a.e.-measurable Gaussian
coordinates:
`∫ g(⟪x,v⟫, ⟪x,w⟫) μ(dx) = ∫∫ g(z, (r/σ²) z + u) 𝒩(0,σ²)(dz) 𝒩(0, τ² - r²/σ²)(du)`. -/
theorem integral_inner_pair_eq_integral_prod_gaussianReal' {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (μ : Measure E) [IsProbabilityMeasure μ] (v w : E)
    (hvw : AEMeasurable (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) μ) {σ2 r τ2 : ℝ}
    (hσ : 0 < σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ)))
    (g : ℝ → ℝ → G) (hg : Continuous (Function.uncurry g)) :
    ∫ x, g ⟪x, v⟫ ⟪x, w⟫ ∂μ =
      ∫ p, g p.1 (r / σ2 * p.1 + p.2)
        ∂((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)) := by
  have hΨ : Measurable fun p : ℝ × ℝ => WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2) := by fun_prop
  have hG : Continuous fun y : WithLp 2 (ℝ × ℝ) => g y.ofLp.1 y.ofLp.2 := by
    have : (fun y : WithLp 2 (ℝ × ℝ) => g y.ofLp.1 y.ofLp.2) =
        Function.uncurry g ∘ fun y : WithLp 2 (ℝ × ℝ) => y.ofLp := by
      funext y
      rfl
    rw [this]
    exact hg.comp (by fun_prop)
  calc ∫ x, g ⟪x, v⟫ ⟪x, w⟫ ∂μ
      = ∫ y, g y.ofLp.1 y.ofLp.2 ∂(μ.map fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) := by
        rw [integral_map hvw hG.aestronglyMeasurable]
    _ = ∫ p, g p.1 (r / σ2 * p.1 + p.2)
          ∂((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)) := by
        rw [map_inner_pair_eq_map_prod_gaussianReal' μ v w hvw hσ h,
          integral_map hΨ.aemeasurable hG.aestronglyMeasurable]

/-! ### The mixed Gaussian integral -/

/-- The mixed Gaussian integral of two a.e.-measurable coordinates:
`∫ e^{-⟪x,v⟫²/2} e^{-i⟪x,w⟫} μ(dx) = (1 + σ²)^{-1/2} exp(-(τ²/2 - r²/(2(1 + σ²))))`. -/
theorem integral_exp_neg_inner_sq_half_mul_exp_neg_inner_mul_I' (μ : Measure E)
    [IsProbabilityMeasure μ] (v w : E) (hv : AEMeasurable (fun x => ⟪x, v⟫) μ)
    (hw : AEMeasurable (fun x => ⟪x, w⟫) μ) {σ2 r τ2 : ℝ} (hσ : 0 ≤ σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ))) :
    ∫ x, Complex.exp (-((⟪x, v⟫ ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-((⟪x, w⟫ : ℝ) : ℂ) * I) ∂μ =
      (((Real.sqrt (1 + σ2))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((τ2 / 2 - r ^ 2 / (2 * (1 + σ2)) : ℝ) : ℂ)) := by
  rcases hσ.lt_or_eq with hσ | hσ0
  · have hδ : 0 ≤ τ2 - r ^ 2 / σ2 := by
      have := sq_le_mul_of_charFun μ v w h
      rw [sub_nonneg, div_le_iff₀ hσ]
      linarith
    have hvw : AEMeasurable (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) μ :=
      (WithLp.measurable_toLp 2 _).comp_aemeasurable (hv.prodMk hw)
    have key := integral_inner_pair_eq_integral_prod_gaussianReal' μ v w hvw hσ h
      (fun z u => Complex.exp (-((z ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-((u : ℝ) : ℂ) * I))
      (by fun_prop)
    rw [key]
    have hfun : ∀ p : ℝ × ℝ,
        Complex.exp (-((p.1 ^ 2 / 2 : ℝ) : ℂ)) *
            Complex.exp (-((r / σ2 * p.1 + p.2 : ℝ) : ℂ) * I) =
          (Complex.exp (-((p.1 ^ 2 / 2 : ℝ) : ℂ)) *
              Complex.exp (-((r / σ2 * p.1 : ℝ) : ℂ) * I)) *
            Complex.exp (((-1 : ℝ) : ℂ) * (p.2 : ℂ) * I) := by
      intro p
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hfun]
    have hprod : ∫ p : ℝ × ℝ, (Complex.exp (-((p.1 ^ 2 / 2 : ℝ) : ℂ)) *
            Complex.exp (-((r / σ2 * p.1 : ℝ) : ℂ) * I)) *
          Complex.exp (((-1 : ℝ) : ℂ) * (p.2 : ℂ) * I)
          ∂((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)) =
        (∫ a : ℝ, Complex.exp (-((a ^ 2 / 2 : ℝ) : ℂ)) *
            Complex.exp (-((r / σ2 * a : ℝ) : ℂ) * I) ∂gaussianReal 0 σ2.toNNReal) *
          ∫ b : ℝ, Complex.exp (((-1 : ℝ) : ℂ) * (b : ℂ) * I)
            ∂gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal :=
      integral_prod_mul (fun a : ℝ => Complex.exp (-((a ^ 2 / 2 : ℝ) : ℂ)) *
          Complex.exp (-((r / σ2 * a : ℝ) : ℂ) * I))
        (fun b : ℝ => Complex.exp (((-1 : ℝ) : ℂ) * (b : ℂ) * I))
    rw [hprod, integral_exp_neg_sq_half_mul_exp_neg_mul_I_gaussianReal,
      ← charFun_apply_real, charFun_gaussianReal, mul_assoc, ← Complex.exp_add,
      Real.coe_toNNReal _ hσ.le, Real.coe_toNNReal _ hδ]
    have hσc : (σ2 : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have h1σ : (1 + (σ2 : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + σ2 := by linarith
      exact_mod_cast this.ne'
    congr 2
    push_cast
    field_simp
    ring
  · subst hσ0
    have hr : r = 0 := by
      have := sq_le_mul_of_charFun μ v w h
      nlinarith [sq_nonneg r]
    subst hr
    have hae := ae_inner_eq_zero_of_charFun' μ v hv fun s => by
      have := h s 0
      simpa using this
    have hw := h 0 (-1)
    simp only [zero_smul, zero_add, neg_one_smul, charFun_apply, inner_neg_right] at hw
    rw [integral_congr_ae (g := fun x => Complex.exp (-((⟪x, w⟫ : ℝ) : ℂ) * I)) ?_]
    · have h1 : (fun x : E => Complex.exp (-((⟪x, w⟫ : ℝ) : ℂ) * I)) =
          fun x : E => Complex.exp (((-⟪x, w⟫ : ℝ) : ℂ) * I) := by
        funext x
        push_cast
        ring_nf
      rw [h1, hw]
      norm_num
    · filter_upwards [hae] with x hx
      rw [hx]
      simp

/-! ### The Borel case -/

section Borel

variable [OpensMeasurableSpace E]

/-- If `charFun μ (s • v) = exp(-σ² s²/2)` for all `s`, the coordinate `⟪·, v⟫` has the law
`𝒩(0, σ²)`. -/
theorem map_inner_eq_gaussianReal (μ : Measure E) [IsProbabilityMeasure μ] (v : E) {σ2 : ℝ}
    (hσ : 0 ≤ σ2)
    (h : ∀ s : ℝ, charFun μ (s • v) = Complex.exp (-((σ2 * s ^ 2 / 2 : ℝ) : ℂ))) :
    μ.map (fun x => ⟪x, v⟫) = gaussianReal 0 σ2.toNNReal :=
  map_inner_eq_gaussianReal' μ v (by fun_prop) hσ h

/-- If `charFun μ (s • v) = 1` for all `s`, then `⟪·, v⟫ = 0` almost everywhere. -/
theorem ae_inner_eq_zero_of_charFun (μ : Measure E) [IsProbabilityMeasure μ] (v : E)
    (h : ∀ s : ℝ, charFun μ (s • v) = 1) : ∀ᵐ x ∂μ, ⟪x, v⟫ = 0 :=
  ae_inner_eq_zero_of_charFun' μ v (by fun_prop) h

/-- For `σ² > 0`, the joint law of the coordinates `(⟪·, v⟫, ⟪·, w⟫)` (in `WithLp 2 (ℝ × ℝ)`)
is the image of `𝒩(0, σ²) ⊗ 𝒩(0, τ² - r²/σ²)` under the shear `(z, u) ↦ (z, (r/σ²) z + u)`. -/
theorem map_inner_pair_eq_map_prod_gaussianReal (μ : Measure E) [IsProbabilityMeasure μ]
    (v w : E) {σ2 r τ2 : ℝ} (hσ : 0 < σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ))) :
    μ.map (fun x => WithLp.toLp 2 (⟪x, v⟫, ⟪x, w⟫)) =
      ((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)).map
        (fun p : ℝ × ℝ => WithLp.toLp 2 (p.1, r / σ2 * p.1 + p.2)) :=
  map_inner_pair_eq_map_prod_gaussianReal' μ v w (by fun_prop) hσ h

/-- Change of variables for integrals of continuous functions of two Gaussian coordinates:
`∫ g(⟪x,v⟫, ⟪x,w⟫) μ(dx) = ∫∫ g(z, (r/σ²) z + u) 𝒩(0,σ²)(dz) 𝒩(0, τ² - r²/σ²)(du)`. -/
theorem integral_inner_pair_eq_integral_prod_gaussianReal {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (μ : Measure E) [IsProbabilityMeasure μ] (v w : E) {σ2 r τ2 : ℝ}
    (hσ : 0 < σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ)))
    (g : ℝ → ℝ → G) (hg : Continuous (Function.uncurry g)) :
    ∫ x, g ⟪x, v⟫ ⟪x, w⟫ ∂μ =
      ∫ p, g p.1 (r / σ2 * p.1 + p.2)
        ∂((gaussianReal 0 σ2.toNNReal).prod (gaussianReal 0 (τ2 - r ^ 2 / σ2).toNNReal)) :=
  integral_inner_pair_eq_integral_prod_gaussianReal' μ v w (by fun_prop) hσ h g hg

/-- The mixed Gaussian integral
`∫ e^{-⟪x,v⟫²/2} e^{-i⟪x,w⟫} μ(dx) = (1 + σ²)^{-1/2} exp(-(τ²/2 - r²/(2(1 + σ²))))`. -/
theorem integral_exp_neg_inner_sq_half_mul_exp_neg_inner_mul_I (μ : Measure E)
    [IsProbabilityMeasure μ] (v w : E) {σ2 r τ2 : ℝ} (hσ : 0 ≤ σ2)
    (h : ∀ s t : ℝ, charFun μ (s • v + t • w) =
      Complex.exp (-(((s ^ 2 * σ2 + 2 * s * t * r + t ^ 2 * τ2) / 2 : ℝ) : ℂ))) :
    ∫ x, Complex.exp (-((⟪x, v⟫ ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-((⟪x, w⟫ : ℝ) : ℂ) * I) ∂μ =
      (((Real.sqrt (1 + σ2))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((τ2 / 2 - r ^ 2 / (2 * (1 + σ2)) : ℝ) : ℂ)) :=
  integral_exp_neg_inner_sq_half_mul_exp_neg_inner_mul_I' μ v w (by fun_prop) (by fun_prop) hσ h

end Borel

end MeasureTheory
