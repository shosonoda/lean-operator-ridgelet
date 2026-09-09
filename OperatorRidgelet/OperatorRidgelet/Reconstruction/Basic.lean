import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.ToMathlib.PolynomialGaussianDeriv
import OperatorRidgelet.ToMathlib.PolynomialGrowthBounds
import OperatorRidgelet.ToMathlib.IteratedDerivMeasurable
import OperatorRidgelet.ToMathlib.ContDiffOnParametricIntegral
import LeanRidgelet.ToMathlib.GaussianSchwartz
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Auxiliary lemmas for Section 4 (representation and reconstruction)

Elementary facts about the anti-dual representation of `𝓔_α'` used by the proofs in
`OperatorRidgelet.Paper.Reconstruction`: the functional `innerSLFlip ℂ x` has norm `‖x‖`, and
the inverse Riesz map `rieszInv` is a right inverse of the Riesz map `rieszMap`.

The second half treats the Gaussian-type densities `G(ξ) = q(κ(ξ), ℓ₁(ξ), …) e^{-κ(ξ)/2}`,
`κ(ξ) = ⟪Sξ, ξ⟫`, of Lemma `lem:ray-regular-examples`(a) (`gaussianTypeDensity`).  Along a ray,
`G(ωa) = P_a(ω) e^{-ω² κ(a)/2}` with a polynomial `P_a` (`rayPolynomial`) whose degree is bounded
uniformly in `a` and whose coefficients grow polynomially in `‖a‖`; the derivative formula of
`OperatorRidgelet.ToMathlib.PolynomialGaussianDeriv` then gives the pointwise ray-derivative
bound `sup_{ω ∈ I} |∂_ω^n G(ωa)| ≤ C_n (1 + ‖a‖)^{p_n} e^{-r² κ(a)/2}`, `r = min_I |ω|`, and the
reduction lemma `isRegularAlongRays_of_gaussian_decay` derives regularity along rays from the
Gaussian-decay integrability of Lemma `lem:gaussian-decay`, taken as a hypothesis.

The remaining sections prove the other parts of Lemma `lem:ray-regular-examples`: densities
vanishing outside a bounded set with polynomially bounded ray derivatives are regular along rays
for any direction measure finite on balls (the ray derivatives vanish for `‖a‖ > R₀ / min_I |ω|`),
radial bumps `φ(‖ξ - ξ₀‖²)` by the chain-rule bound `norm_iteratedFDeriv_comp_le`, and finite
linear combinations; the last needs the Borel measurability of the ray-derivative bound
`a ↦ max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖` (`measurable_rayDerivBound`), obtained from
`OperatorRidgelet.ToMathlib.IteratedDerivMeasurable` and a countable dense subset of `I`.  This
module is not imported by `Challenge`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace Polynomial

/-- The conjugate-linear functional `y ↦ ⟪y, x⟫` has norm `‖x‖`. -/
theorem norm_innerSLFlip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    ‖innerSLFlip ℂ x‖ = ‖x‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => ?_) ?_
  · rw [innerSLFlip_apply_apply]
    exact (norm_inner_le_norm y x).trans (le_of_eq (mul_comm _ _))
  · by_cases hx : x = 0
    · simp [hx]
    · have h1 : ‖innerSLFlip ℂ x x‖ ≤ ‖innerSLFlip ℂ x‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      simp only [innerSLFlip_apply_apply, inner_self_eq_norm_sq_to_K, norm_pow,
        RCLike.norm_ofReal, abs_norm] at h1
      rw [sq] at h1
      exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hx)

/-- The Riesz representation: `innerSLFlip ℂ` applied to the vector representing a continuous
conjugate-linear functional gives the functional back. -/
theorem innerSLFlip_toDual_symm_antiDualConj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F : E →L⋆[ℂ] ℂ) :
    innerSLFlip ℂ ((InnerProductSpace.toDual ℂ E).symm (antiDualConj F)) = F := by
  ext g
  rw [innerSLFlip_apply_apply, ← inner_conj_symm, InnerProductSpace.toDual_symm_apply,
    antiDualConj_apply, Complex.conj_conj]

/-- `innerSLFlip ℂ` is injective. -/
theorem innerSLFlip_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Function.Injective (innerSLFlip ℂ : E →L[ℂ] E →L⋆[ℂ] ℂ) := by
  intro f g hfg
  apply ext_inner_left ℂ
  intro h
  have := congrArg (fun T : E →L⋆[ℂ] ℂ => T h) hfg
  simpa [innerSLFlip_apply_apply] using this

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- `J (J⁻¹ F) = F`. -/
theorem rieszMap_rieszInv (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDual μ ν) :
    rieszMap μ ν (rieszInv μ ν F) = F :=
  innerSLFlip_toDual_symm_antiDualConj F

/-- `J (J⁻¹ F) = F` for `Y`-valued targets. -/
theorem rieszMapVec_rieszInvVec {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (μ ν : Measure H) [IsFiniteMeasure μ] (F : SpectralAntiDualVec Y μ ν) :
    rieszMapVec Y μ ν (rieszInvVec μ ν F) = F :=
  innerSLFlip_toDual_symm_antiDualConj F

end

/-! ### Gaussian-type densities -/

section GaussianType

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gaussian-type density `G(ξ) = q(κ(ξ), ℓ₁(ξ), …, ℓ_k(ξ)) e^{-κ(ξ)/2}`, `κ(ξ) = ⟪Sξ, ξ⟫`,
of Lemma `lem:ray-regular-examples`(a): `q` is a polynomial with complex coefficients in the
quadratic form `κ` (variable `none`) and in the bounded linear functionals `ℓ i` (variables
`some i`). -/
def gaussianTypeDensity (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) (ξ : H) : ℂ :=
  MvPolynomial.eval (fun o : Option (Fin k) =>
      o.elim ((⟪S ξ, ξ⟫ : ℝ) : ℂ) fun i => ((ℓ i ξ : ℝ) : ℂ)) q *
    Complex.exp (-((⟪S ξ, ξ⟫ / 2 : ℝ) : ℂ))

/-- The exponents of the ray substitution: `κ(ωa) = ω² κ(a)` and `ℓ_i(ωa) = ω ℓ_i(a)`. -/
def rayExponent {k : ℕ} (o : Option (Fin k)) : ℕ :=
  o.elim 2 fun _ => 1

/-- The values `κ(a)` and `ℓ_i(a)` substituted along the ray through `a`. -/
def rayValue (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ)) (a : H) (o : Option (Fin k)) :
    ℂ :=
  o.elim ((⟪S a, a⟫ : ℝ) : ℂ) fun i => ((ℓ i a : ℝ) : ℂ)

/-- The polynomial `P_a ∈ ℂ[X]` with `G(ωa) = P_a(ω) e^{-ω² κ(a)/2}`, obtained from `q` by the
substitution `κ ↦ κ(a) X²`, `ℓ_i ↦ ℓ_i(a) X`. -/
def rayPolynomial (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) (a : H) : ℂ[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun o => Polynomial.C (rayValue S ℓ a o) * Polynomial.X ^ rayExponent o) q

/-- Along the ray through `a`, `G(ωa) = P_a(ω) e^{-ω² κ(a)/2}`. -/
theorem gaussianTypeDensity_smul (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) (a : H) (ω : ℝ) :
    gaussianTypeDensity S ℓ q (ω • a) =
      (rayPolynomial S ℓ q a).eval (ω : ℂ) *
        Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2)) := by
  unfold gaussianTypeDensity rayPolynomial
  rw [MvPolynomial.eval_eval₂_C_mul_X_pow]
  have hκ : ⟪S (ω • a), ω • a⟫ = ω ^ 2 * ⟪S a, a⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hfun : (fun o : Option (Fin k) =>
      o.elim ((⟪S (ω • a), ω • a⟫ : ℝ) : ℂ) fun i => ((ℓ i (ω • a) : ℝ) : ℂ)) =
        fun o => rayValue S ℓ a o * (ω : ℂ) ^ rayExponent o := by
    funext o
    cases o with
    | none =>
      simp only [Option.elim, rayValue, rayExponent, hκ]
      push_cast
      ring
    | some i =>
      simp only [Option.elim, rayValue, rayExponent, map_smul, smul_eq_mul]
      push_cast
      ring
  rw [hfun]
  congr 2
  rw [hκ]
  push_cast
  ring

/-- Degree and coefficient bounds for the ray polynomials: for a weight `t ≥ 1` with
`|κ(a)| ≤ b₀ t(a)²` and `|ℓ_i(a)| ≤ b_i t(a)`, the polynomial `P_a` has degree at most `d` and
coefficients of norm at most `C t(a)^d`, with `d` and `C` independent of `a`. -/
theorem exists_bound_rayPolynomial (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) (t : H → ℝ) (ht : ∀ a, 1 ≤ t a) {b₀ : ℝ}
    (hb₀ : 0 ≤ b₀) (hS : ∀ a, |⟪S a, a⟫| ≤ b₀ * t a ^ 2) {b : Fin k → ℝ} (hb : ∀ i, 0 ≤ b i)
    (hℓ : ∀ i a, |ℓ i a| ≤ b i * t a) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : H, (rayPolynomial S ℓ q a).natDegree ≤ d ∧
      ∀ j, ‖(rayPolynomial S ℓ q a).coeff j‖ ≤ C * t a ^ d := by
  obtain ⟨d, C, hC, h⟩ := MvPolynomial.exists_bound_eval₂_C_mul_X_pow q rayExponent
    (fun o => o.elim b₀ b) (fun o => by cases o <;> simp [hb₀, hb])
  refine ⟨d, C, hC, fun a => h (rayValue S ℓ a) (t a) (ht a) fun o => ?_⟩
  cases o with
  | none => simpa [rayValue, rayExponent] using hS a
  | some i => simpa [rayValue, rayExponent] using hℓ i a

/-- The ray polynomials have degree at most `d` and coefficients of norm at most
`C (1 + ‖a‖)^d`, with `d` and `C` independent of `a`. -/
theorem exists_bound_rayPolynomial_norm (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : H, (rayPolynomial S ℓ q a).natDegree ≤ d ∧
      ∀ j, ‖(rayPolynomial S ℓ q a).coeff j‖ ≤ C * (1 + ‖a‖) ^ d := by
  refine exists_bound_rayPolynomial S ℓ q (fun a => 1 + ‖a‖)
    (fun a => by linarith [norm_nonneg a]) (norm_nonneg S) (fun a => ?_)
    (b := fun i => ‖ℓ i‖) (fun i => norm_nonneg (ℓ i)) (fun i a => ?_)
  · have h1 : |⟪S a, a⟫| ≤ ‖S a‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h2 : ‖S a‖ ≤ ‖S‖ * ‖a‖ := S.le_opNorm a
    have h3 : ‖a‖ ^ 2 ≤ (1 + ‖a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg a) (by linarith [norm_nonneg a]) 2
    nlinarith [norm_nonneg a, norm_nonneg S, norm_nonneg (S a)]
  · have h1 : ‖ℓ i a‖ ≤ ‖ℓ i‖ * ‖a‖ := (ℓ i).le_opNorm a
    rw [Real.norm_eq_abs] at h1
    nlinarith [norm_nonneg a, norm_nonneg (ℓ i)]

/-- When the functionals are dominated by the quadratic form, `ℓ_i(ξ)² ≤ C_i κ(ξ)`, the ray
polynomials have coefficients of norm at most `C (1 + √κ(a))^d`. -/
theorem exists_bound_rayPolynomial_sqrt (S : H →L[ℝ] H) (hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫) {k : ℕ}
    (ℓ : Fin k → (H →L[ℝ] ℝ)) (hℓ : ∀ i, ∃ C : ℝ, ∀ ξ, (ℓ i ξ) ^ 2 ≤ C * ⟪S ξ, ξ⟫)
    (q : MvPolynomial (Option (Fin k)) ℂ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : H, (rayPolynomial S ℓ q a).natDegree ≤ d ∧
      ∀ j, ‖(rayPolynomial S ℓ q a).coeff j‖ ≤ C * (1 + Real.sqrt ⟪S a, a⟫) ^ d := by
  choose Cℓ hCℓ using hℓ
  refine exists_bound_rayPolynomial S ℓ q (fun a => 1 + Real.sqrt ⟪S a, a⟫)
    (fun a => by linarith [Real.sqrt_nonneg ⟪S a, a⟫]) zero_le_one (fun a => ?_)
    (b := fun i => Real.sqrt (max (Cℓ i) 0)) (fun i => Real.sqrt_nonneg _) (fun i a => ?_)
  · rw [abs_of_nonneg (hS0 a), one_mul]
    have h := Real.sq_sqrt (hS0 a)
    nlinarith [Real.sqrt_nonneg ⟪S a, a⟫]
  · have h1 : (ℓ i a) ^ 2 ≤ max (Cℓ i) 0 * ⟪S a, a⟫ :=
      (hCℓ i a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hS0 a))
    have h2 : |ℓ i a| ≤ Real.sqrt (max (Cℓ i) 0) * Real.sqrt ⟪S a, a⟫ := by
      rw [← Real.sqrt_mul (le_max_right _ _), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    refine h2.trans ?_
    have := Real.sqrt_nonneg (max (Cℓ i) 0)
    nlinarith [Real.sqrt_nonneg ⟪S a, a⟫]

/-- A Gaussian-type density is bounded when the functionals are dominated by the quadratic
form. -/
theorem exists_norm_gaussianTypeDensity_le (S : H →L[ℝ] H) (hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫) {k : ℕ}
    (ℓ : Fin k → (H →L[ℝ] ℝ)) (hℓ : ∀ i, ∃ C : ℝ, ∀ ξ, (ℓ i ξ) ^ 2 ≤ C * ⟪S ξ, ξ⟫)
    (q : MvPolynomial (Option (Fin k)) ℂ) :
    ∃ M : ℝ, ∀ ξ : H, ‖gaussianTypeDensity S ℓ q ξ‖ ≤ M := by
  obtain ⟨d, C, hC, h⟩ := exists_bound_rayPolynomial_sqrt S hS0 ℓ hℓ q
  refine ⟨(d + 1) * C * 2 ^ d * (2 ^ d * (1 + 2 ^ d * (d.factorial : ℝ))), fun ξ => ?_⟩
  have hξ := gaussianTypeDensity_smul S ℓ q ξ 1
  rw [one_smul] at hξ
  rw [hξ, norm_mul]
  obtain ⟨hd, hc⟩ := h ξ
  have hP := Polynomial.norm_eval_le_of_norm_coeff_le hd hc (1 : ℂ)
  rw [norm_one] at hP
  set u := Real.sqrt ⟪S ξ, ξ⟫ with hu_def
  have hexp : ‖Complex.exp (-(((⟪S ξ, ξ⟫ : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2))‖ =
      Real.exp (-u ^ 2 / 2) := by
    rw [← Complex.norm_exp_ofReal]
    congr 2
    rw [hu_def, Real.sq_sqrt (hS0 ξ)]
    push_cast
    ring
  rw [hexp]
  have hu : (1 + u) ^ d * Real.exp (-u ^ 2 / 2) ≤ 2 ^ d * (1 + 2 ^ d * (d.factorial : ℝ)) := by
    have := Real.one_add_abs_pow_mul_exp_neg_sq_div_two_le d u
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  calc ‖(rayPolynomial S ℓ q ξ).eval 1‖ * Real.exp (-u ^ 2 / 2)
      ≤ ((d + 1) * (C * (1 + u) ^ d) * (1 + 1) ^ d) * Real.exp (-u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ = (d + 1) * C * 2 ^ d * ((1 + u) ^ d * Real.exp (-u ^ 2 / 2)) := by ring
    _ ≤ (d + 1) * C * 2 ^ d * (2 ^ d * (1 + 2 ^ d * (d.factorial : ℝ))) := by
        gcongr

/-- A Gaussian-type density is continuous. -/
theorem continuous_gaussianTypeDensity (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) :
    Continuous (gaussianTypeDensity S ℓ q) := by
  unfold gaussianTypeDensity
  have hκ : Continuous fun ξ : H => ⟪S ξ, ξ⟫ := S.continuous.inner continuous_id
  have hv : Continuous fun ξ : H => fun o : Option (Fin k) =>
      o.elim ((⟪S ξ, ξ⟫ : ℝ) : ℂ) fun i => ((ℓ i ξ : ℝ) : ℂ) := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => exact Complex.continuous_ofReal.comp hκ
    | some i => exact Complex.continuous_ofReal.comp (ℓ i).continuous
  refine ((MvPolynomial.continuous_eval q).comp hv).mul ?_
  exact Complex.continuous_exp.comp
    (Complex.continuous_ofReal.comp (hκ.div_const 2)).neg

/-- Along every ray, a Gaussian-type density is smooth. -/
theorem contDiff_gaussianTypeDensity_smul (S : H →L[ℝ] H) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) (a : H) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun ω : ℝ => gaussianTypeDensity S ℓ q (ω • a) := by
  have : (fun ω : ℝ => gaussianTypeDensity S ℓ q (ω • a)) = fun ω : ℝ =>
      (rayPolynomial S ℓ q a).eval (ω : ℂ) *
        Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2)) :=
    funext (gaussianTypeDensity_smul S ℓ q a)
  rw [this]
  exact Polynomial.contDiff_eval_ofReal_mul_cexp _ _

/-- The pointwise ray-derivative bound of Lemma `lem:ray-regular-examples`(a): on the annulus
`r ≤ |ω| ≤ R`, `‖∂_ω^n G(ωa)‖ ≤ C (1 + ‖a‖)^p e^{-r² κ(a)/2}` with `C`, `p` independent of
`a` and `ω`. -/
theorem exists_norm_iteratedDeriv_gaussianTypeDensity_smul_le (S : H →L[ℝ] H)
    (hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫) {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ))
    (q : MvPolynomial (Option (Fin k)) ℂ) {r : ℝ} (hr : 0 ≤ r) (R : ℝ) (n : ℕ) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ (a : H) (ω : ℝ), r ≤ |ω| → |ω| ≤ R →
      ‖iteratedDeriv n (fun ω : ℝ => gaussianTypeDensity S ℓ q (ω • a)) ω‖ ≤
        C * (1 + ‖a‖) ^ p * Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
  obtain ⟨d, C, hC, h⟩ := exists_bound_rayPolynomial_norm S ℓ q
  refine ⟨(d + n + 1) * (d + n + ‖S‖) ^ n * C * (1 + |R|) ^ (d + n), d + 2 * n,
    by positivity, fun a ω hrω hωR => ?_⟩
  have hfun : (fun ω : ℝ => gaussianTypeDensity S ℓ q (ω • a)) = fun ω : ℝ =>
      (rayPolynomial S ℓ q a).eval (ω : ℂ) *
        Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2)) :=
    funext (gaussianTypeDensity_smul S ℓ q a)
  rw [hfun]
  obtain ⟨hd, hc⟩ := h a
  refine (Polynomial.norm_iteratedDeriv_eval_ofReal_mul_cexp_le _ hd hc n ω).trans ?_
  have hκ0 : 0 ≤ ⟪S a, a⟫ := hS0 a
  have hκ : ⟪S a, a⟫ ≤ ‖S‖ * (1 + ‖a‖) ^ 2 := by
    have h1 : |⟪S a, a⟫| ≤ ‖S a‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h2 : ‖S a‖ ≤ ‖S‖ * ‖a‖ := S.le_opNorm a
    have h3 : ‖a‖ ^ 2 ≤ (1 + ‖a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg a) (by linarith [norm_nonneg a]) 2
    rw [abs_of_nonneg hκ0] at h1
    nlinarith [norm_nonneg a, norm_nonneg S, norm_nonneg (S a)]
  have ha1 : (1 : ℝ) ≤ (1 + ‖a‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg a])
  have h1 : (d + n + |⟪S a, a⟫|) ^ n ≤ (d + n + ‖S‖) ^ n * (1 + ‖a‖) ^ (2 * n) := by
    rw [pow_mul, ← mul_pow, abs_of_nonneg hκ0]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    nlinarith [norm_nonneg S]
  have h2 : (1 + |ω|) ^ (d + n) ≤ (1 + |R|) ^ (d + n) :=
    pow_le_pow_left₀ (by positivity) (by linarith [le_abs_self R]) _
  have h3 : Real.exp (-(⟪S a, a⟫ * ω ^ 2 / 2)) ≤ Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
    rw [Real.exp_le_exp]
    have : r ^ 2 ≤ ω ^ 2 := by
      rw [← sq_abs ω]
      exact pow_le_pow_left₀ hr hrω 2
    nlinarith
  calc (d + n + 1) * ((d + n + |⟪S a, a⟫|) ^ n * (C * (1 + ‖a‖) ^ d)) * (1 + |ω|) ^ (d + n) *
        Real.exp (-(⟪S a, a⟫ * ω ^ 2 / 2))
      ≤ (d + n + 1) * (((d + n + ‖S‖) ^ n * (1 + ‖a‖) ^ (2 * n)) * (C * (1 + ‖a‖) ^ d)) *
          (1 + |R|) ^ (d + n) * Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
        gcongr
    _ = (d + n + 1) * (d + n + ‖S‖) ^ n * C * (1 + |R|) ^ (d + n) * (1 + ‖a‖) ^ (d + 2 * n) *
          Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
        rw [pow_add (1 + ‖a‖) d (2 * n)]
        ring

/-- The ray-derivative bound `rayDerivBound I G m a` of a Gaussian-type density is dominated by
`C (1 + ‖a‖)^p e^{-t κ(a)}` for some `t > 0` depending only on the frequency window `I`. -/
theorem exists_rayDerivBound_gaussianTypeDensity_le (S : H →L[ℝ] H) (hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫)
    {k : ℕ} (ℓ : Fin k → (H →L[ℝ] ℝ)) (q : MvPolynomial (Option (Fin k)) ℂ) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) (m : ℕ) :
    ∃ (t C : ℝ) (p : ℕ), 0 < t ∧ 0 ≤ C ∧ ∀ a : H,
      rayDerivBound I (gaussianTypeDensity S ℓ q) m a ≤
        ENNReal.ofReal (C * (1 + ‖a‖) ^ p * Real.exp (-t * ⟪S a, a⟫)) := by
  obtain ⟨r, R, hr, hrR⟩ := hI.exists_pos_le_abs_le hI0
  choose C p hC hCp using fun n : ℕ =>
    exists_norm_iteratedDeriv_gaussianTypeDensity_smul_le S hS0 ℓ q hr.le R n
  refine ⟨r ^ 2 / 2, ∑ n ∈ Finset.range (m + 1), C n, ∑ n ∈ Finset.range (m + 1), p n,
    by positivity, Finset.sum_nonneg fun n _ => hC n, fun a => ?_⟩
  unfold rayDerivBound
  refine iSup_le fun n => iSup₂_le fun ω hω => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨h1, h2⟩ := hrR ω hω
  have hn : (n : ℕ) < m + 1 := n.2
  refine (hCp n a ω h1 h2).trans ?_
  have hC' : C n ≤ ∑ i ∈ Finset.range (m + 1), C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr hn)
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), C i := Finset.sum_nonneg fun i _ => hC i
  have hp' : (1 + ‖a‖) ^ p n ≤ (1 + ‖a‖) ^ ∑ i ∈ Finset.range (m + 1), p i :=
    pow_le_pow_right₀ (by linarith [norm_nonneg a])
      (Finset.single_le_sum (fun i _ => Nat.zero_le (p i)) (Finset.mem_range.mpr hn))
  exact mul_le_mul_of_nonneg_right (mul_le_mul hC' hp' (by positivity) hsum)
    (Real.exp_pos _).le

variable [MeasurableSpace H]

/-- The ray moments of a Gaussian-type density are finite, given the Gaussian-decay
integrability `∫ ‖ξ‖^{2m} e^{-t⟪Qξ,ξ⟫} dν < ∞` of Lemma `lem:gaussian-decay` and `S ≥ θQ`. -/
theorem rayMoment_gaussianTypeDensity_lt_top (ν : Measure H) {Q : H →L[ℝ] H}
    (hQ0 : ∀ ξ, 0 ≤ ⟪Q ξ, ξ⟫)
    (hdecay : ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν)
    (S : H →L[ℝ] H) {θ : ℝ} (hθ : 0 < θ) (hSQ : ∀ ξ, θ * ⟪Q ξ, ξ⟫ ≤ ⟪S ξ, ξ⟫) {k : ℕ}
    (ℓ : Fin k → (H →L[ℝ] ℝ)) (q : MvPolynomial (Option (Fin k)) ℂ) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) (m : ℕ) :
    rayMoment ν I (gaussianTypeDensity S ℓ q) m < ⊤ := by
  have hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫ := fun ξ => (mul_nonneg hθ.le (hQ0 ξ)).trans (hSQ ξ)
  obtain ⟨t, C, p, ht, hC, hbound⟩ :=
    exists_rayDerivBound_gaussianTypeDensity_le S hS0 ℓ q hI hI0 m
  set N := m + 2 + p with hN_def
  have hint : Integrable (fun a : H =>
      C * 2 ^ N * (2 + ‖a‖ ^ (2 * N)) * Real.exp (-(t * θ) * ⟪Q a, a⟫)) ν := by
    have h0 := hdecay (t * θ) (by positivity) 0
    have hN := hdecay (t * θ) (by positivity) N
    simp only [mul_zero, pow_zero, one_mul] at h0
    refine (((h0.const_mul 2).add hN).const_mul (C * 2 ^ N)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply]
    ring
  refine lt_of_le_of_lt (lintegral_mono fun a => ?_) hint.lintegral_lt_top
  refine (mul_le_mul' le_rfl (hbound a)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : Real.exp (-t * ⟪S a, a⟫) ≤ Real.exp (-(t * θ) * ⟪Q a, a⟫) := by
    rw [Real.exp_le_exp]
    have := hSQ a
    nlinarith
  have hpow : (1 + ‖a‖) ^ (m + 2) * (1 + ‖a‖) ^ p ≤ 2 ^ N * (2 + ‖a‖ ^ (2 * N)) := by
    rw [← pow_add]
    exact one_add_pow_le_two_pow_mul_two_add_pow N (norm_nonneg a)
  calc (1 + ‖a‖) ^ (m + 2) * (C * (1 + ‖a‖) ^ p * Real.exp (-t * ⟪S a, a⟫))
      = C * ((1 + ‖a‖) ^ (m + 2) * (1 + ‖a‖) ^ p) * Real.exp (-t * ⟪S a, a⟫) := by ring
    _ ≤ C * (2 ^ N * (2 + ‖a‖ ^ (2 * N))) * Real.exp (-(t * θ) * ⟪Q a, a⟫) := by
        gcongr
    _ = C * 2 ^ N * (2 + ‖a‖ ^ (2 * N)) * Real.exp (-(t * θ) * ⟪Q a, a⟫) := by ring

variable [OpensMeasurableSpace H]

/-- **Reduction of Lemma `lem:ray-regular-examples`(a) to Gaussian decay.**  A Gaussian-type
density `G(ξ) = q(κ(ξ), ℓ₁(ξ), …) e^{-κ(ξ)/2}` with `κ(ξ) = ⟪Sξ, ξ⟫ ≥ θ⟪Qξ, ξ⟫`, `θ > 0`, and
functionals dominated by the quadratic form, `ℓ_i(ξ)² ≤ C_i κ(ξ)`, is regular along rays with
respect to any direction measure `ν` satisfying the Gaussian-decay integrability
`∫ ‖ξ‖^{2m} e^{-t⟪Qξ,ξ⟫} dν < ∞` of Lemma `lem:gaussian-decay`, for every compact frequency window
`I ⊆ ℝ ∖ {0}`. -/
theorem isRegularAlongRays_of_gaussian_decay (ν : Measure H) {Q : H →L[ℝ] H}
    (hQ0 : ∀ ξ, 0 ≤ ⟪Q ξ, ξ⟫)
    (hdecay : ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν)
    (S : H →L[ℝ] H) {θ : ℝ} (hθ : 0 < θ) (hSQ : ∀ ξ, θ * ⟪Q ξ, ξ⟫ ≤ ⟪S ξ, ξ⟫) {k : ℕ}
    (ℓ : Fin k → (H →L[ℝ] ℝ)) (hℓ : ∀ i, ∃ C : ℝ, ∀ ξ, (ℓ i ξ) ^ 2 ≤ C * ⟪S ξ, ξ⟫)
    (q : MvPolynomial (Option (Fin k)) ℂ) {I : Set ℝ} (hI : IsCompact I)
    (hI0 : (0 : ℝ) ∉ I) :
    IsRegularAlongRays ν I fun ξ =>
      MvPolynomial.eval (fun o : Option (Fin k) =>
          o.elim ((⟪S ξ, ξ⟫ : ℝ) : ℂ) fun i => ((ℓ i ξ : ℝ) : ℂ)) q *
        Complex.exp (-((⟪S ξ, ξ⟫ / 2 : ℝ) : ℂ)) := by
  have hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫ := fun ξ => (mul_nonneg hθ.le (hQ0 ξ)).trans (hSQ ξ)
  show IsRegularAlongRays ν I (gaussianTypeDensity S ℓ q)
  exact
    { stronglyMeasurable := (continuous_gaussianTypeDensity S ℓ q).stronglyMeasurable
      bounded := exists_norm_gaussianTypeDensity_le S hS0 ℓ hℓ q
      contDiffOn := fun a => ⟨Set.univ, isOpen_univ, Set.subset_univ _,
        (contDiff_gaussianTypeDensity_smul S ℓ q a).contDiffOn⟩
      rayMoment_lt_top := fun m =>
        rayMoment_gaussianTypeDensity_lt_top ν hQ0 hdecay S hθ hSQ ℓ q hI hI0 m }

end GaussianType

/-! ### Densities with bounded support -/

section BoundedSupport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For a density vanishing outside the ball of radius `R₀`, every ray derivative vanishes at a
frequency `ω` with `|ω| ‖a‖ > R₀` (the ray function vanishes near `ω`). -/
theorem iteratedDeriv_smul_eq_zero_of_norm_gt {G : H → ℂ} {R₀ : ℝ}
    (hG0 : ∀ ξ : H, R₀ < ‖ξ‖ → G ξ = 0) {a : H} {ω : ℝ} (hω : R₀ < |ω| * ‖a‖) (k : ℕ) :
    iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω = 0 := by
  have hev : (fun ω : ℝ => G (ω • a)) =ᶠ[𝓝 ω] fun _ => (0 : ℂ) := by
    have hopen : IsOpen {ω' : ℝ | R₀ < |ω'| * ‖a‖} :=
      isOpen_lt continuous_const (continuous_abs.mul continuous_const)
    filter_upwards [hopen.mem_nhds hω] with ω' hω'
    exact hG0 _ (by rw [norm_smul, Real.norm_eq_abs]; exact hω')
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_const]
  simp

/-- For a density vanishing outside the ball of radius `R₀` and a frequency window
`I ⊆ {r ≤ |ω|}`, the ray-derivative bound vanishes once `r ‖a‖ > R₀`. -/
theorem rayDerivBound_eq_zero_of_norm_gt {I : Set ℝ} {r : ℝ} (hr : ∀ ω ∈ I, r ≤ |ω|)
    {G : H → ℂ} {R₀ : ℝ} (hG0 : ∀ ξ : H, R₀ < ‖ξ‖ → G ξ = 0) (m : ℕ) {a : H}
    (ha : R₀ < r * ‖a‖) :
    rayDerivBound I G m a = 0 := by
  unfold rayDerivBound
  refine le_antisymm (iSup_le fun k => iSup₂_le fun ω hω => ?_) bot_le
  rw [iteratedDeriv_smul_eq_zero_of_norm_gt hG0
    (lt_of_lt_of_le ha (mul_le_mul_of_nonneg_right (hr ω hω) (norm_nonneg a))) k]
  simp

/-- A uniform bound `B k` on the `k`-th ray derivatives over `I`, `k ≤ m`, bounds the
ray-derivative bound by `∑_{k ≤ m} B k`. -/
theorem rayDerivBound_le_ofReal_sum {I : Set ℝ} {G : H → ℂ} {m : ℕ} {a : H} {B : ℕ → ℝ}
    (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k ≤ m, ∀ ω ∈ I, ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ ≤ B k) :
    rayDerivBound I G m a ≤ ENNReal.ofReal (∑ k ∈ Finset.range (m + 1), B k) := by
  unfold rayDerivBound
  refine iSup_le fun k => iSup₂_le fun ω hω => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((hB k (Nat.lt_succ_iff.mp k.2) ω hω).trans ?_)
  exact Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_range.mpr k.2)

variable [MeasurableSpace H] [OpensMeasurableSpace H]

/-- **Lemma `lem:ray-regular-examples`(b), general form.**  A bounded Borel density that is
smooth along rays near the compact window `I ⊆ ℝ ∖ {0}`, vanishes outside a bounded set, and
has polynomially bounded ray derivatives on `I` is regular along rays with respect to any
direction measure that is finite on balls: the ray derivatives vanish for `‖a‖ > R₀ / min_I |ω|`
and are bounded on the remaining ball. -/
theorem isRegularAlongRays_of_bounded_support (ν : Measure H)
    (hν : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤) {G : H → ℂ} (hG : Measurable G)
    (hGb : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M) {R₀ : ℝ} (hG0 : ∀ ξ : H, R₀ < ‖ξ‖ → G ξ = 0) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I)
    (hsmooth : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U)
    (hbound : ∀ k : ℕ, ∃ C p : ℝ, ∀ a : H, ∀ ω ∈ I,
      ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ ≤ C * (1 + ‖a‖) ^ p) :
    IsRegularAlongRays ν I G := by
  obtain ⟨r, R, hr, hrR⟩ := hI.exists_pos_le_abs_le hI0
  choose C p hCp using hbound
  refine ⟨hG.stronglyMeasurable, hGb, hsmooth, fun m => ?_⟩
  set Ra := max (R₀ / r) 0 with hRa
  have hRa0 : 0 ≤ Ra := le_max_right _ _
  set B : ℕ → ℝ := fun k => max (C k) 0 * (1 + Ra) ^ |p k| with hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by positivity
  have hBk : ∀ k, ∀ a : H, ‖a‖ ≤ Ra → ∀ ω ∈ I,
      ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ ≤ B k := by
    intro k a ha ω hω
    refine (hCp k a ω hω).trans ?_
    have h1 : (1 + ‖a‖) ^ (p k) ≤ (1 + Ra) ^ |p k| := by
      rcases le_or_gt 0 (p k) with hp | hp
      · rw [abs_of_nonneg hp]
        exact Real.rpow_le_rpow (by linarith [norm_nonneg a]) (by linarith) hp
      · rw [abs_of_neg hp]
        calc (1 + ‖a‖) ^ (p k) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg a]) hp.le
          _ ≤ (1 + Ra) ^ (-p k) := Real.one_le_rpow (by linarith) (by linarith)
    calc C k * (1 + ‖a‖) ^ (p k) ≤ max (C k) 0 * (1 + ‖a‖) ^ (p k) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (C k) 0 * (1 + Ra) ^ |p k| := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  have hzero : ∀ a : H, Ra < ‖a‖ → rayDerivBound I G m a = 0 := by
    intro a ha
    refine rayDerivBound_eq_zero_of_norm_gt (fun ω hω => (hrR ω hω).1) hG0 m ?_
    have h1 : R₀ / r < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) ha
    rwa [div_lt_iff₀ hr, mul_comm] at h1
  have hle : ∀ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I G m a ≤
      (Metric.closedBall (0 : H) Ra).indicator
        (fun _ => ENNReal.ofReal ((1 + Ra) ^ (m + 2) * ∑ k ∈ Finset.range (m + 1), B k)) a := by
    intro a
    by_cases ha : ‖a‖ ≤ Ra
    · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.mpr ha), ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (by linarith [norm_nonneg a]) (by linarith) _)) ?_
      exact rayDerivBound_le_ofReal_sum hB0 fun k _ ω hω => hBk k a ha ω hω
    · rw [Set.indicator_of_notMem (fun h => ha (mem_closedBall_zero_iff.mp h)),
        hzero a (not_le.mp ha), mul_zero]
  unfold rayMoment
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hν Ra)

end BoundedSupport

/-! ### Radial bumps -/

section RadialBump

/-- The quadratic `‖ωa - ξ₀‖² = ‖a‖² ω² - 2⟪a,ξ₀⟫ ω + ‖ξ₀‖²` along the ray through `a`. -/
theorem norm_smul_sub_sq_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ξ₀ a : H) (ω : ℝ) :
    ‖ω • a - ξ₀‖ ^ 2 = ‖a‖ ^ 2 * ω ^ 2 - 2 * ⟪a, ξ₀⟫ * ω + ‖ξ₀‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The derivative of a real quadratic. -/
theorem hasDerivAt_quadratic (A B C ω : ℝ) :
    HasDerivAt (fun ω : ℝ => A * ω ^ 2 - B * ω + C) (2 * A * ω - B) ω := by
  have h := (((hasDerivAt_pow 2 ω).const_mul A).sub ((hasDerivAt_id ω).const_mul B)).add_const C
  exact h.congr_deriv (by norm_num; ring)

/-- `iteratedDeriv 1` of a real quadratic. -/
theorem iteratedDeriv_one_quadratic (A B C : ℝ) :
    iteratedDeriv 1 (fun ω : ℝ => A * ω ^ 2 - B * ω + C) = fun ω => 2 * A * ω - B := by
  rw [iteratedDeriv_one]
  funext ω
  exact (hasDerivAt_quadratic A B C ω).deriv

/-- `iteratedDeriv 2` of a real quadratic. -/
theorem iteratedDeriv_two_quadratic (A B C : ℝ) :
    iteratedDeriv 2 (fun ω : ℝ => A * ω ^ 2 - B * ω + C) = fun _ => 2 * A := by
  rw [iteratedDeriv_succ, iteratedDeriv_one_quadratic]
  funext ω
  have h := (((hasDerivAt_id ω).const_mul (2 * A)).sub_const B).deriv
  simp only [id, mul_one] at h
  exact h

/-- The iterated derivatives of order `≥ 3` of a real quadratic vanish. -/
theorem iteratedDeriv_add_three_quadratic (A B C : ℝ) (i : ℕ) :
    iteratedDeriv (i + 3) (fun ω : ℝ => A * ω ^ 2 - B * ω + C) = 0 := by
  induction i with
  | zero =>
    rw [iteratedDeriv_succ, iteratedDeriv_two_quadratic]
    funext ω
    exact deriv_const ω (2 * A)
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext ω
    exact deriv_const ω (0 : ℝ)

/-- The iterated derivatives of a real quadratic on `|ω| ≤ R` are bounded by `D ^ i` for
`i ≥ 1`, when `D ≥ 1` dominates `2|A|R + |B|` and `2|A|`. -/
theorem norm_iteratedDeriv_quadratic_le {A B C R D : ℝ} (hD1 : 1 ≤ D)
    (hD : 2 * |A| * R + |B| ≤ D) (hD' : 2 * |A| ≤ D) {ω : ℝ} (hω : |ω| ≤ R) {i : ℕ}
    (hi : 1 ≤ i) :
    ‖iteratedDeriv i (fun ω : ℝ => A * ω ^ 2 - B * ω + C) ω‖ ≤ D ^ i := by
  match i, hi with
  | 1, _ =>
    rw [iteratedDeriv_one_quadratic]
    simp only [Real.norm_eq_abs, pow_one]
    calc |2 * A * ω - B| ≤ |2 * A * ω| + |B| := abs_sub _ _
      _ = 2 * |A| * |ω| + |B| := by rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |A| * R + |B| := by gcongr
      _ ≤ D := hD
  | 2, _ =>
    rw [iteratedDeriv_two_quadratic]
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_two]
    calc 2 * |A| ≤ D := hD'
      _ ≤ D ^ 2 := by nlinarith
  | i + 3, _ =>
    rw [iteratedDeriv_add_three_quadratic]
    simp only [Pi.zero_apply, norm_zero]
    positivity

/-- The chain rule bound for a smooth function composed with a real quadratic:
`‖∂^n (φ ∘ q)(ω)‖ ≤ n! C D^n` when `‖∂^i φ‖ ≤ C` for `i ≤ n` and the quadratic's derivatives
are bounded by `D^i`. -/
theorem norm_iteratedDeriv_comp_quadratic_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {n : ℕ}
    {Cφ : ℝ} (hC : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Cφ) (A B C : ℝ) {R D : ℝ}
    (hD1 : 1 ≤ D) (hD : 2 * |A| * R + |B| ≤ D) (hD' : 2 * |A| ≤ D) {ω : ℝ} (hω : |ω| ≤ R) :
    ‖iteratedDeriv n (fun ω : ℝ => φ (A * ω ^ 2 - B * ω + C)) ω‖ ≤
      n.factorial * Cφ * D ^ n := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun ω : ℝ => A * ω ^ 2 - B * ω + C) := by fun_prop
  have h := norm_iteratedFDeriv_comp_le hφ hq (n := n) (by exact_mod_cast le_top) ω
    (C := Cφ) (D := D) (fun i hi => hC i hi _) fun i hi1 _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact norm_iteratedDeriv_quadratic_le hD1 hD hD' hω hi1
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- **Lemma `lem:ray-regular-examples`(b), radial bumps.**  `G(ξ) = φ(‖ξ - ξ₀‖²)` with
`φ ∈ C_c^∞(ℝ)` is regular along rays with respect to any direction measure finite on balls,
for every compact window `I ⊆ ℝ ∖ {0}`. -/
theorem isRegularAlongRays_radialBump (ν : Measure H)
    (hν : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤) (ξ₀ : H) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) {I : Set ℝ} (hI : IsCompact I)
    (hI0 : (0 : ℝ) ∉ I) :
    IsRegularAlongRays ν I fun ξ => φ (‖ξ - ξ₀‖ ^ 2) := by
  have hcont : Continuous fun ξ : H => φ (‖ξ - ξ₀‖ ^ 2) := hφ.continuous.comp (by fun_prop)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨T, hT⟩ := hφc.isBounded.subset_closedBall (0 : ℝ)
  have hG0 : ∀ ξ : H, ‖ξ₀‖ + Real.sqrt (max T 0) < ‖ξ‖ → φ (‖ξ - ξ₀‖ ^ 2) = 0 := by
    intro ξ hξ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hT hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      at h1
    have h2 : Real.sqrt (max T 0) < ‖ξ - ξ₀‖ := by
      have := norm_sub_norm_le ξ ξ₀
      linarith
    have h3 : max T 0 < ‖ξ - ξ₀‖ ^ 2 := by
      have := Real.sq_sqrt (le_max_right T 0)
      nlinarith [Real.sqrt_nonneg (max T 0)]
    linarith [le_max_left T 0]
  have hsmooth : ∀ a : H, ContDiff ℝ (⊤ : ℕ∞) fun ω : ℝ => φ (‖ω • a - ξ₀‖ ^ 2) := fun a =>
    hφ.comp ((contDiff_norm_sq ℝ).comp ((contDiff_id.smul contDiff_const).sub contDiff_const))
  obtain ⟨r, R, hr, hrR⟩ := hI.exists_pos_le_abs_le hI0
  have hφi : ∀ i : ℕ, ContDiff ℝ i φ := fun i => hφ.of_le (by exact_mod_cast le_top)
  choose Cφ hCφ using fun i : ℕ =>
    (hφi i).continuous_iteratedFDeriv'.bounded_above_of_compact_support (hφc.iteratedFDeriv i)
  refine isRegularAlongRays_of_bounded_support ν hν hcont.measurable ⟨M, fun ξ => hM _⟩ hG0 hI hI0
    (fun a => ⟨Set.univ, isOpen_univ, Set.subset_univ _, (hsmooth a).contDiffOn⟩) fun k => ?_
  refine ⟨k.factorial * (∑ i ∈ Finset.range (k + 1), |Cφ i|) *
    (4 * (1 + |R|) * (1 + ‖ξ₀‖)) ^ k, 2 * k, fun a ω hω => ?_⟩
  have hfun : (fun ω : ℝ => φ (‖ω • a - ξ₀‖ ^ 2)) =
      fun ω => φ (‖a‖ ^ 2 * ω ^ 2 - 2 * ⟪a, ξ₀⟫ * ω + ‖ξ₀‖ ^ 2) := by
    funext ω
    rw [norm_smul_sub_sq_eq]
  rw [hfun]
  set P := (1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 with hP
  have ha1 : 1 ≤ (1 + ‖a‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg a])
  have hP1 : 1 ≤ P := by
    rw [hP]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 := by
        gcongr <;> linarith [abs_nonneg R, norm_nonneg ξ₀]
  have hPa : ‖a‖ ^ 2 * |R| ≤ P := by
    rw [hP]
    calc ‖a‖ ^ 2 * |R| ≤ (1 + ‖a‖) ^ 2 * (1 + |R|) := by
          gcongr <;> linarith [norm_nonneg a, abs_nonneg R]
      _ = (1 + |R|) * 1 * (1 + ‖a‖) ^ 2 := by ring
      _ ≤ (1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 := by
          gcongr
          linarith [norm_nonneg ξ₀]
  have hPb : ‖a‖ * ‖ξ₀‖ ≤ P := by
    rw [hP]
    have h1 : ‖a‖ ≤ (1 + ‖a‖) ^ 2 := by nlinarith [norm_nonneg a]
    calc ‖a‖ * ‖ξ₀‖ ≤ (1 + ‖a‖) ^ 2 * (1 + ‖ξ₀‖) := by
          gcongr
          linarith [norm_nonneg ξ₀]
      _ = 1 * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 := by ring
      _ ≤ (1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 := by
          gcongr
          linarith [abs_nonneg R]
  have hD1 : 1 ≤ 4 * P := by linarith
  have hD : 2 * |‖a‖ ^ 2| * |R| + |2 * ⟪a, ξ₀⟫| ≤ 4 * P := by
    rw [abs_of_nonneg (by positivity), abs_mul, abs_two]
    have := abs_real_inner_le_norm a ξ₀
    linarith
  have hD' : 2 * |‖a‖ ^ 2| ≤ 4 * P := by
    rw [abs_of_nonneg (by positivity)]
    have : ‖a‖ ^ 2 ≤ P := by
      rw [hP]
      calc ‖a‖ ^ 2 ≤ (1 + ‖a‖) ^ 2 := by gcongr; linarith [norm_nonneg a]
        _ = 1 * 1 * (1 + ‖a‖) ^ 2 := by ring
        _ ≤ (1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2 := by
            gcongr <;> linarith [abs_nonneg R, norm_nonneg ξ₀]
    linarith
  have hC : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ ∑ i ∈ Finset.range (k + 1), |Cφ i| :=
    fun i hi y => (hCφ i y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (Cφ j))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))))
  have h := norm_iteratedDeriv_comp_quadratic_le hφ hC (‖a‖ ^ 2) (2 * ⟪a, ξ₀⟫) (‖ξ₀‖ ^ 2)
    hD1 hD hD' ((hrR ω hω).2.trans (le_abs_self R))
  refine h.trans (le_of_eq ?_)
  rw [hP, show (4 : ℝ) * ((1 + |R|) * (1 + ‖ξ₀‖) * (1 + ‖a‖) ^ 2) =
    (4 * (1 + |R|) * (1 + ‖ξ₀‖)) * (1 + ‖a‖) ^ 2 by ring, mul_pow, ← pow_mul,
    show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

end RadialBump

/-! ### Measurability of the ray-derivative bound -/

section RayMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- For a Borel density smooth along rays near `I`, the ray derivative at a fixed `ω ∈ I` is a
Borel function of the direction (`OperatorRidgelet.ToMathlib.IteratedDerivMeasurable`). -/
theorem measurable_iteratedDeriv_ray {G : H → ℂ} (hG : Measurable G) {I : Set ℝ}
    (hsmooth : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U)
    (k : ℕ) {ω : ℝ} (hω : ω ∈ I) :
    Measurable fun a : H => iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω :=
  measurable_iteratedDeriv_of_forall_contDiffOn (f := fun a ω => G (ω • a))
    (fun t => hG.comp (measurable_const_smul t))
    (fun a => by
      obtain ⟨U, hU, hIU, hf⟩ := hsmooth a
      exact ⟨U, hU, hIU hω, hf⟩) k

omit [MeasurableSpace H] [BorelSpace H] in
/-- The supremum over `I` in the ray-derivative bound may be taken over a subset dense in `I`
when the ray derivatives are continuous on `I`. -/
theorem rayDerivBound_eq_biSup_dense {G : H → ℂ} {I D : Set ℝ} (hD : D ⊆ I)
    (hdense : I ⊆ closure D) (m : ℕ) (a : H)
    (hcont : ∀ k : ℕ, ContinuousOn (iteratedDeriv k fun ω : ℝ => G (ω • a)) I) :
    rayDerivBound I G m a =
      ⨆ k : Fin (m + 1), ⨆ ω ∈ D, ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ₑ := by
  unfold rayDerivBound
  congr 1
  funext k
  exact biSup_eq_biSup_of_subset_closure hD hdense (hcont k).enorm

/-- **Measurability of the ray-derivative bound.**  For a Borel density smooth along rays on a
neighbourhood of `I`, `a ↦ max_{k ≤ m} sup_{ω ∈ I} ‖∂_ω^k G(ωa)‖` is Borel: the supremum over
`I` is a supremum over a countable dense subset by continuity, and each ray derivative is a
Borel function of the direction. -/
theorem measurable_rayDerivBound {G : H → ℂ} (hG : Measurable G) {I : Set ℝ}
    (hsmooth : ∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U)
    (m : ℕ) :
    Measurable fun a : H => rayDerivBound I G m a := by
  obtain ⟨D, hDI, hDc, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace I).exists_countable_dense_subset
  have heq : (fun a : H => rayDerivBound I G m a) = fun a =>
      ⨆ k : Fin (m + 1), ⨆ ω ∈ D, ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ₑ := by
    funext a
    obtain ⟨U, hU, hIU, hf⟩ := hsmooth a
    exact rayDerivBound_eq_biSup_dense hDI hdense m a fun k =>
      ((hf.iteratedDeriv_of_isOpen hU k).continuousOn).mono hIU
  rw [heq]
  exact Measurable.iSup fun k => Measurable.biSup D hDc fun ω hω =>
    (measurable_iteratedDeriv_ray hG hsmooth k (hDI hω)).enorm

end RayMeasurable

/-! ### Finite linear combinations -/

section FinsetSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A common open neighbourhood of `I` on which finitely many ray functions are smooth. -/
theorem exists_isOpen_forall_contDiffOn {ι : Type*} (s : Finset ι) (G : ι → H → ℂ) {I : Set ℝ}
    (a : H)
    (h : ∀ i ∈ s, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G i (ω • a)) U) :
    ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G i (ω • a)) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s hj ih =>
    obtain ⟨U, hU, hIU, hUs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨V, hV, hIV, hVj⟩ := h j (Finset.mem_insert_self j s)
    refine ⟨U ∩ V, hU.inter hV, Set.subset_inter hIU hIV, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hVj.mono Set.inter_subset_right
    · exact (hUs i hi).mono Set.inter_subset_left

/-- Iterated derivatives of a finite linear combination of functions smooth on an open set. -/
theorem iteratedDeriv_finset_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ)
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) (n : ℕ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (g i) U) :
    iteratedDeriv n (fun ω => ∑ i ∈ s, c i * g i ω) x =
      ∑ i ∈ s, c i * iteratedDeriv n (g i) x := by
  classical
  have hwithin : ∀ f : ℝ → ℂ, iteratedDerivWithin n f U x = iteratedDeriv n f x := fun f =>
    iteratedDerivWithin_of_isOpen hU hx
  simp_rw [← hwithin]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, iteratedDerivWithin_const]
    split_ifs <;> rfl
  | insert j s hj ih =>
    have hgj : ContDiffWithinAt ℝ n (g j) U x :=
      ((hg j (Finset.mem_insert_self j s)) x hx).of_le (by exact_mod_cast le_top)
    have hgs : ∀ i ∈ s, ContDiffWithinAt ℝ n (g i) U x := fun i hi =>
      ((hg i (Finset.mem_insert_of_mem hi)) x hx).of_le (by exact_mod_cast le_top)
    have hsum : ContDiffWithinAt ℝ n (fun ω => ∑ i ∈ s, c i * g i ω) U x :=
      (ContDiffWithinAt.sum fun i hi => contDiffWithinAt_const.mul (hgs i hi))
    simp_rw [Finset.sum_insert hj]
    rw [show (fun ω => c j * g j ω + ∑ i ∈ s, c i * g i ω) =
      (fun ω => c j * g j ω) + fun ω => ∑ i ∈ s, c i * g i ω from rfl,
      iteratedDerivWithin_add hx hU.uniqueDiffOn (contDiffWithinAt_const.mul hgj) hsum,
      iteratedDerivWithin_const_mul hx hU.uniqueDiffOn (c j) hgj,
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- The ray-derivative bound of a finite linear combination is dominated by the linear
combination of the ray-derivative bounds. -/
theorem rayDerivBound_finset_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (G : ι → H → ℂ)
    {I : Set ℝ} (m : ℕ) (a : H)
    (h : ∀ i ∈ s, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G i (ω • a)) U) :
    rayDerivBound I (fun ξ => ∑ i ∈ s, c i * G i ξ) m a ≤
      ∑ i ∈ s, ‖c i‖ₑ * rayDerivBound I (G i) m a := by
  obtain ⟨U, hU, hIU, hUs⟩ := exists_isOpen_forall_contDiffOn s G a h
  unfold rayDerivBound
  refine iSup_le fun k => iSup₂_le fun ω hω => ?_
  rw [iteratedDeriv_finset_sum_mul s c (fun i ω => G i (ω • a)) hU (hIU hω) k hUs]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [enorm_mul]
  exact mul_le_mul' le_rfl (le_iSup_of_le k (le_iSup₂_of_le ω hω le_rfl))

variable [MeasurableSpace H] [BorelSpace H]

/-- **Lemma `lem:ray-regular-examples`(c), finite linear combinations.**  Finite linear
combinations of densities regular along rays are regular along rays: the ray moments are
subadditive, the summands' ray-derivative bounds being Borel. -/
theorem IsRegularAlongRays.finset_sum {ν : Measure H} {I : Set ℝ} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (G : ι → H → ℂ) (hG : ∀ i ∈ s, IsRegularAlongRays ν I (G i)) :
    IsRegularAlongRays ν I fun ξ => ∑ i ∈ s, c i * G i ξ := by
  have hb : ∀ i, ∃ M : ℝ, ∀ ξ, i ∈ s → ‖G i ξ‖ ≤ M := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨M, hM⟩ := (hG i hi).bounded
      exact ⟨M, fun ξ _ => hM ξ⟩
    · exact ⟨0, fun ξ h => absurd h hi⟩
  choose M hM using hb
  refine ⟨Finset.stronglyMeasurable_fun_sum s fun i hi =>
    stronglyMeasurable_const.mul (hG i hi).stronglyMeasurable,
    ⟨∑ i ∈ s, ‖c i‖ * M i, fun ξ => ?_⟩, fun a => ?_, fun m => ?_⟩
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM i ξ hi) (norm_nonneg _)
  · obtain ⟨U, hU, hIU, hUs⟩ := exists_isOpen_forall_contDiffOn s G a fun i hi =>
      (hG i hi).contDiffOn a
    exact ⟨U, hU, hIU, ContDiffOn.sum fun i hi => contDiffOn_const.mul (hUs i hi)⟩
  · have hmeas : ∀ i ∈ s, Measurable fun a : H =>
        ‖c i‖ₑ * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I (G i) m a) := by
      intro i hi
      refine Measurable.const_mul (Measurable.mul ?_ ?_) _
      · exact (ENNReal.continuous_ofReal.comp
          (by fun_prop : Continuous fun a : H => (1 + ‖a‖) ^ (m + 2))).measurable
      · exact measurable_rayDerivBound (hG i hi).stronglyMeasurable.measurable
          (fun a => (hG i hi).contDiffOn a) m
    have hle : ∀ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
        rayDerivBound I (fun ξ => ∑ i ∈ s, c i * G i ξ) m a ≤
        ∑ i ∈ s, ‖c i‖ₑ * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I (G i) m a) := by
      intro a
      calc ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
            rayDerivBound I (fun ξ => ∑ i ∈ s, c i * G i ξ) m a
          ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
              ∑ i ∈ s, ‖c i‖ₑ * rayDerivBound I (G i) m a :=
            mul_le_mul' le_rfl (rayDerivBound_finset_sum_le s c G m a fun i hi =>
              (hG i hi).contDiffOn a)
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    unfold rayMoment
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_finsetSum s hmeas]
    refine ENNReal.sum_lt_top.mpr fun i hi => ?_
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    exact ENNReal.mul_lt_top enorm_lt_top ((hG i hi).rayMoment_lt_top m)

/-! ### Finite combinations with constant weights in a Banach space -/

section FinsetSumSmul

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Iterated derivatives of a finite combination `∑ g_i(ω) • w_i` of scalar functions smooth on
an open set, with constant weights `w_i` in a Banach space. -/
theorem iteratedDeriv_finset_sum_smul {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (w : ι → Y)
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) (n : ℕ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (g i) U) :
    iteratedDeriv n (fun ω => ∑ i ∈ s, g i ω • w i) x =
      ∑ i ∈ s, iteratedDeriv n (g i) x • w i := by
  classical
  have hwithinY : ∀ f : ℝ → Y, iteratedDerivWithin n f U x = iteratedDeriv n f x := fun f =>
    iteratedDerivWithin_of_isOpen hU hx
  have hwithinC : ∀ f : ℝ → ℂ, iteratedDerivWithin n f U x = iteratedDeriv n f x := fun f =>
    iteratedDerivWithin_of_isOpen hU hx
  rw [← hwithinY]
  simp_rw [← hwithinC]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, iteratedDerivWithin_const]
    split_ifs <;> rfl
  | insert j s hj ih =>
    have hgj : ContDiffWithinAt ℝ n (g j) U x :=
      ((hg j (Finset.mem_insert_self j s)) x hx).of_le (by exact_mod_cast le_top)
    have hgs : ∀ i ∈ s, ContDiffWithinAt ℝ n (g i) U x := fun i hi =>
      ((hg i (Finset.mem_insert_of_mem hi)) x hx).of_le (by exact_mod_cast le_top)
    have hsum : ContDiffWithinAt ℝ n (fun ω => ∑ i ∈ s, g i ω • w i) U x :=
      ContDiffWithinAt.sum fun i hi => (hgs i hi).smul_const (w i)
    simp_rw [Finset.sum_insert hj]
    rw [show (fun ω => g j ω • w j + ∑ i ∈ s, g i ω • w i) =
      (fun ω => g j ω • w j) + fun ω => ∑ i ∈ s, g i ω • w i from rfl,
      iteratedDerivWithin_add hx hU.uniqueDiffOn (hgj.smul_const (w j)) hsum,
      iteratedDerivWithin_smul_const hx hU.uniqueDiffOn hgj (w j),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The ray-derivative bound of a finite combination with constant weights in a Banach space is
dominated by the combination of the ray-derivative bounds. -/
theorem rayDerivBound_finset_sum_smul_le {ι : Type*} (s : Finset ι) (G : ι → H → ℂ) (w : ι → Y)
    {I : Set ℝ} (m : ℕ) (a : H)
    (h : ∀ i ∈ s, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G i (ω • a)) U) :
    rayDerivBound I (fun ξ => ∑ i ∈ s, G i ξ • w i) m a ≤
      ∑ i ∈ s, ‖w i‖ₑ * rayDerivBound I (G i) m a := by
  obtain ⟨U, hU, hIU, hUs⟩ := exists_isOpen_forall_contDiffOn s G a h
  unfold rayDerivBound
  refine iSup_le fun k => iSup₂_le fun ω hω => ?_
  rw [iteratedDeriv_finset_sum_smul s (fun i ω => G i (ω • a)) w hU (hIU hω) k hUs]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [enorm_smul, mul_comm]
  exact mul_le_mul' le_rfl (le_iSup_of_le k (le_iSup₂_of_le ω hω le_rfl))

/-- **Lemma `lem:ray-regular-examples`(c) with vector weights.**  A finite combination
`∑ G_i(ξ) • w_i` of scalar densities regular along rays with constant weights in a Banach space
is regular along rays.  The measurability of the ray-derivative bounds stays with the scalar
summands, so no `Y`-valued analogue of `measurable_rayDerivBound` is needed. -/
theorem IsRegularAlongRays.finset_sum_smul {ν : Measure H} {I : Set ℝ} {ι : Type*} (s : Finset ι)
    (G : ι → H → ℂ) (w : ι → Y) (hG : ∀ i ∈ s, IsRegularAlongRays ν I (G i)) :
    IsRegularAlongRays ν I fun ξ => ∑ i ∈ s, G i ξ • w i := by
  have hb : ∀ i, ∃ M : ℝ, ∀ ξ, i ∈ s → ‖G i ξ‖ ≤ M := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨M, hM⟩ := (hG i hi).bounded
      exact ⟨M, fun ξ _ => hM ξ⟩
    · exact ⟨0, fun ξ h => absurd h hi⟩
  choose M hM using hb
  refine ⟨Finset.stronglyMeasurable_fun_sum s fun i hi =>
    (hG i hi).stronglyMeasurable.smul_const (w i),
    ⟨∑ i ∈ s, M i * ‖w i‖, fun ξ => ?_⟩, fun a => ?_, fun m => ?_⟩
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM i ξ hi) (norm_nonneg _)
  · obtain ⟨U, hU, hIU, hUs⟩ := exists_isOpen_forall_contDiffOn s G a fun i hi =>
      (hG i hi).contDiffOn a
    exact ⟨U, hU, hIU, ContDiffOn.sum fun i hi => (hUs i hi).smul_const (w i)⟩
  · have hmeas : ∀ i ∈ s, Measurable fun a : H =>
        ‖w i‖ₑ * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I (G i) m a) := by
      intro i hi
      refine Measurable.const_mul (Measurable.mul ?_ ?_) _
      · exact (ENNReal.continuous_ofReal.comp
          (by fun_prop : Continuous fun a : H => (1 + ‖a‖) ^ (m + 2))).measurable
      · exact measurable_rayDerivBound (hG i hi).stronglyMeasurable.measurable
          (fun a => (hG i hi).contDiffOn a) m
    have hle : ∀ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
        rayDerivBound I (fun ξ => ∑ i ∈ s, G i ξ • w i) m a ≤
        ∑ i ∈ s, ‖w i‖ₑ * (ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) * rayDerivBound I (G i) m a) := by
      intro a
      calc ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
            rayDerivBound I (fun ξ => ∑ i ∈ s, G i ξ • w i) m a
          ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (m + 2)) *
              ∑ i ∈ s, ‖w i‖ₑ * rayDerivBound I (G i) m a :=
            mul_le_mul' le_rfl (rayDerivBound_finset_sum_smul_le s G w m a fun i hi =>
              (hG i hi).contDiffOn a)
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    unfold rayMoment
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_finsetSum s hmeas]
    refine ENNReal.sum_lt_top.mpr fun i hi => ?_
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    exact ENNReal.mul_lt_top enorm_lt_top ((hG i hi).rayMoment_lt_top m)

end FinsetSumSmul

end FinsetSum

/-! ### Bochner integrals of measurable families -/

section BochnerIntegral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The ray-derivative bound dominates every ray derivative of order at most `m` on `I`. -/
theorem enorm_iteratedDeriv_le_rayDerivBound {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (I : Set ℝ) (G : H → Y) {m k : ℕ} (hk : k ≤ m) (a : H) {ω : ℝ} (hω : ω ∈ I) :
    ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ₑ ≤ rayDerivBound I G m a := by
  unfold rayDerivBound
  exact le_iSup_of_le ⟨k, Nat.lt_succ_of_le hk⟩ (le_iSup₂_of_le ω hω le_rfl)

variable [MeasurableSpace H] [BorelSpace H]

omit [BorelSpace H] in
/-- **Bochner integrals of densities regular along rays** (Lemma `lem:ray-regular-examples`(c)):
for a measurable family `G y` of bounded densities over a finite measure `m`, smooth along rays
on a common open neighbourhood `U` of `I` and with a `y`-independent `ν`-integrable majorant of
the ray-derivative bounds on `U`, the Bochner integral `ξ ↦ ∫ G y ξ ∂m` is regular along rays:
differentiation under the integral sign (`contDiffOn_integral_of_dominated`) gives smoothness
along rays and the ray moments. -/
theorem IsRegularAlongRays.integral {ν : Measure H} {I : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) [IsFiniteMeasure m] {G : Ω → H → ℂ} (hGm : Measurable (Function.uncurry G))
    (hGb : ∃ M : ℝ, ∀ y ξ, ‖G y ξ‖ ≤ M) {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ,
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ ENNReal.ofReal (h a)) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  -- measurability of the ray derivatives in the parameter
  have hmeas : ∀ (a : H) (k : ℕ), ∀ t ∈ U,
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m :=
    fun a k t ht => (measurable_iteratedDeriv_of_forall_contDiffOn (f := fun y ω => G y (ω • a))
      (fun t => hGm.comp (measurable_id.prodMk measurable_const))
      (fun y => ⟨U, hU, ht, hsmooth y a⟩) k).aestronglyMeasurable
  -- the uniform bounds are constant in the parameter
  have hbound : ∀ (a : H) (k : ℕ), ∃ B : Ω → ℝ, Integrable B m ∧
      ∀ y, ∀ t ∈ U, ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ ≤ B y := by
    intro a k
    obtain ⟨h, -, hh⟩ := hunif k
    refine ⟨fun _ => max (h a) 0, integrable_const _, fun y t ht => ?_⟩
    have h1 : ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ₑ ≤ ENNReal.ofReal (max (h a) 0) :=
      ((enorm_iteratedDeriv_le_rayDerivBound U (G y) le_rfl a ht).trans (hh y a)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp h1
  refine ⟨hGm.stronglyMeasurable.integral_prod_left', ?_, fun a => ⟨U, hU, hIU, ?_⟩, ?_⟩
  · obtain ⟨M, hM⟩ := hGb
    exact ⟨M * m.real Set.univ, fun ξ =>
      norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => hM y ξ)⟩
  · exact contDiffOn_integral_of_dominated hU (fun y => hsmooth y a) (hmeas a) (hbound a)
  · intro k
    obtain ⟨h, hint, hh⟩ := hunif k
    have hray : ∀ a, rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ≤
        ENNReal.ofReal (h a) * m Set.univ := by
      intro a
      refine iSup_le fun j => iSup₂_le fun ω hω => ?_
      have hωU : ω ∈ U := hIU hω
      change ‖iteratedDeriv (j : ℕ) (fun ω : ℝ => ∫ y, G y (ω • a) ∂m) ω‖ₑ ≤ _
      rw [iteratedDeriv_integral_eq hU (fun y => hsmooth y a) (hmeas a) (hbound a) j hωU,
        ← lintegral_const]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
      exact (enorm_iteratedDeriv_le_rayDerivBound U (G y) (Nat.lt_succ_iff.mp j.2) a hωU).trans
        (hh y a)
    unfold rayMoment
    calc ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) *
          rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ∂ν
        ≤ ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) * m Set.univ ∂ν :=
          lintegral_mono fun a => by
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (hray a)
      _ = (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) *
            m Set.univ := lintegral_mul_const' _ _ (measure_ne_top m _)
      _ < ⊤ := ENNReal.mul_lt_top hint (measure_lt_top m _)

end BochnerIntegral

end OperatorRidgelet
