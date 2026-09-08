import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.ToMathlib.PolynomialGaussianDeriv
import OperatorRidgelet.ToMathlib.PolynomialGrowthBounds
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
Gaussian-decay integrability of Lemma `lem:gaussian-decay`, taken as a hypothesis.  This module
is not imported by `Challenge`.
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

end OperatorRidgelet
