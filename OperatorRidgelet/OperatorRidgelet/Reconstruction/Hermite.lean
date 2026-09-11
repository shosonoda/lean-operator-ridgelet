import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.ToMathlib.HermiteExpansion
import OperatorRidgelet.ToMathlib.EntirePowerSeries

/-!
# The Hermite expansion of the weighted Fourier transform along a ray

For a centred Gaussian `μ = 𝒩(0,Q)` and `ξ ≠ 0`, the coordinate `Y(x) = ⟪x,ξ⟫/τ(ξ)`,
`τ(ξ) = ⟪Qξ,ξ⟫^{1/2}`, is a standard Gaussian coordinate (`isStdGaussianCoord_inner_div`).
Under this identification the objects of Lemma `lem:hermite-totality` are the objects of
`OperatorRidgelet.ToMathlib.HermiteExpansion` at the complex parameter `-i z τ(ξ)`:

* `hermiteCoefficient_eq`: `E_μ[f Heₙ(Y)] = ∫ f Heₙ(Y) dμ`;
* `hermiteExtension_eq`: `G_f(zξ) = ∫ f e^{wY - w²/2} dμ` with `w = -i z τ(ξ)`.

The lemma then follows from the one-dimensional expansion together with
`OperatorRidgelet.ToMathlib.EntirePowerSeries`.
-/

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped RealInnerProductSpace NNReal

noncomputable section

namespace OperatorRidgelet

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- For `μ = 𝒩(0,Q)` and `⟪Qξ,ξ⟫ > 0`, the normalized coordinate `x ↦ ⟪x,ξ⟫/τ(ξ)` is a
standard Gaussian coordinate. -/
theorem isStdGaussianCoord_inner_div {Q : H →L[ℝ] H} {μ : Measure H}
    (hμ : IsCenteredGaussian Q μ) (ξ : H) (hpos : 0 < ⟪Q ξ, ξ⟫) :
    IsStdGaussianCoord μ fun x => ⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫ := by
  haveI := hμ.isProbabilityMeasure
  set τ := Real.sqrt ⟪Q ξ, ξ⟫ with hτ
  have hτpos : 0 < τ := Real.sqrt_pos.mpr hpos
  have hmeas : Measurable fun x : H => ⟪x, ξ⟫ := (continuous_id.inner continuous_const).measurable
  refine ⟨hmeas.div_const _, ?_⟩
  have h1 : μ.map (fun x => ⟪x, ξ⟫) = gaussianReal 0 (Real.toNNReal ⟪Q ξ, ξ⟫) :=
    hμ.map_inner_eq_gaussianReal ξ hpos.le
  have h2 : (fun x : H => ⟪x, ξ⟫ / τ) = (fun y : ℝ => τ⁻¹ * y) ∘ fun x : H => ⟪x, ξ⟫ := by
    funext x
    simp [div_eq_inv_mul]
  have hτ2 : τ ^ 2 = ⟪Q ξ, ξ⟫ := Real.sq_sqrt hpos.le
  rw [h2, ← Measure.map_map (measurable_const_mul _) hmeas, h1,
    show (fun y : ℝ => τ⁻¹ * y) = (τ⁻¹ * ·) from rfl, gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, Real.coe_toNNReal _ hpos.le]
  rw [← hτ2]
  field_simp

omit [OpensMeasurableSpace H] in
/-- The Hermite coefficient `E_μ[f Heₙ(⟪x,ξ⟫/τ(ξ))]` is the coefficient of the
one-dimensional expansion at the standard Gaussian coordinate `⟪x,ξ⟫/τ(ξ)`. -/
theorem hermiteCoefficient_eq {Q : H →L[ℝ] H} (μ : Measure H) (f : H → ℂ) (ξ : H) (n : ℕ) :
    hermiteCoefficient μ Q f ξ n =
      ∫ x, f x * hermiteC n (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) ∂μ := by
  simp only [hermiteCoefficient, hermiteC, Polynomial.aeval_hermite_eq_eval_hermiteR]

omit [OpensMeasurableSpace H] in
/-- The entire extension `G_f(zξ)` is the pairing of `f` with the Gaussian generating function
at the parameter `-i z τ(ξ)`. -/
theorem hermiteExtension_eq {Q : H →L[ℝ] H} (μ : Measure H) (f : H → ℂ) {ξ : H}
    (hpos : 0 < ⟪Q ξ, ξ⟫) (z : ℂ) :
    hermiteExtension μ Q f ξ z =
      ∫ x, f x * gaussGen (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ)))
        (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) ∂μ := by
  set τ := Real.sqrt ⟪Q ξ, ξ⟫ with hτ
  have hτpos : 0 < τ := Real.sqrt_pos.mpr hpos
  have hτ0 : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτpos.ne'
  have hτ2 : ((τ : ℝ) : ℂ) ^ 2 = ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hτ, Real.sq_sqrt hpos.le]
  have key : ∀ x : H,
      f x * gaussGen (-(Complex.I * z * ((τ : ℝ) : ℂ))) (⟪x, ξ⟫ / τ) =
        Complex.exp (z ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) / 2) *
          (f x * Complex.exp (-(z * ((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I))) := by
    intro x
    have hw1 : -(Complex.I * z * ((τ : ℝ) : ℂ)) * (((⟪x, ξ⟫ : ℝ) : ℂ) / ((τ : ℝ) : ℂ)) =
        -(z * ((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← mul_div_assoc, show -(Complex.I * z * ((τ : ℝ) : ℂ)) * ((⟪x, ξ⟫ : ℝ) : ℂ) =
        -(z * ((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * ((τ : ℝ) : ℂ) from by ring,
        mul_div_cancel_right₀ _ hτ0]
    have hw2 : (-(Complex.I * z * ((τ : ℝ) : ℂ))) ^ 2 = -(z ^ 2 * ((τ : ℝ) : ℂ) ^ 2) := by
      rw [show (-(Complex.I * z * ((τ : ℝ) : ℂ))) ^ 2 =
        Complex.I ^ 2 * (z ^ 2 * ((τ : ℝ) : ℂ) ^ 2) from by ring, Complex.I_sq]
      ring
    have hexp : -(z * ((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) -
          -(z ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ)) / 2 =
        z ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) / 2 + -(z * ((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) := by
      ring
    rw [gaussGen, Complex.ofReal_div, hw1, hw2, hτ2, hexp, Complex.exp_add]
    ring
  rw [hermiteExtension, gaussFourierLine,
    integral_congr_ae (Eventually.of_forall key), integral_const_mul]

/-! ### The master expansion -/

variable {Q : H →L[ℝ] H} {μ : Measure H}

/-- The Hermite expansion of `G_f(zξ)` as a power series in `z`:
`G_f(zξ) = ∑ₙ (-i τ(ξ))ⁿ/n! E_μ[f Heₙ(⟪x,ξ⟫/τ(ξ))] zⁿ`. -/
theorem hasSum_hermiteExtension_pow (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (z : ℂ) :
    HasSum (fun n : ℕ =>
        (-(Complex.I * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))) ^ n / (n.factorial : ℂ) *
          hermiteCoefficient μ Q f ξ n * z ^ n)
      (hermiteExtension μ Q f ξ z) := by
  have hY := isStdGaussianCoord_inner_div hμ ξ hpos
  have h := hasSum_integral_mul_gaussGen hY hf
    (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ)))
  rw [← hermiteExtension_eq μ f hpos z] at h
  refine h.congr_fun fun n => ?_
  rw [hermiteCoefficient_eq]
  ring

/-- `z ↦ G_f(zξ)` is entire. -/
theorem differentiable_hermiteExtension (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) :
    Differentiable ℂ (hermiteExtension μ Q f ξ) :=
  differentiable_of_hasSum_pow fun z => hasSum_hermiteExtension_pow hμ hf hpos z

/-- The Hermite series of `G_f(zξ)` in the form of Lemma `lem:hermite-totality`(ii). -/
theorem hasSum_hermiteExtension (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (z : ℂ) :
    HasSum (fun n : ℕ =>
        (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))) ^ n / (n.factorial : ℂ) *
          hermiteCoefficient μ Q f ξ n)
      (hermiteExtension μ Q f ξ z) :=
  (hasSum_hermiteExtension_pow hμ hf hpos z).congr_fun fun n => by ring

/-- The Hermite series converges locally uniformly in `z`. -/
theorem tendstoLocallyUniformly_hermiteExtension (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) :
    TendstoLocallyUniformly
      (fun N : ℕ => fun z : ℂ => ∑ n ∈ Finset.range N,
        (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))) ^ n / (n.factorial : ℂ) *
          hermiteCoefficient μ Q f ξ n)
      (hermiteExtension μ Q f ξ) atTop := by
  have h := tendstoLocallyUniformly_of_hasSum_pow
    (fun z => hasSum_hermiteExtension_pow hμ hf hpos z)
  refine h.congr fun N z => ?_
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The bound `|G_f(zξ)| ≤ ‖f‖_{L²(μ)} e^{|z|²τ(ξ)²/2}`. -/
theorem norm_hermiteExtension_le (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (z : ℂ) :
    ‖hermiteExtension μ Q f ξ z‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.exp (‖z‖ ^ 2 * ⟪Q ξ, ξ⟫ / 2) := by
  have hY := isStdGaussianCoord_inner_div hμ ξ hpos
  have h := norm_integral_mul_gaussGen_le hY hf
    (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ)))
  rw [← hermiteExtension_eq μ f hpos z] at h
  refine h.trans (le_of_eq ?_)
  have hnorm : ‖-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))‖ =
      ‖z‖ * Real.sqrt ⟪Q ξ, ξ⟫ := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm, mul_pow, Real.sq_sqrt hpos.le]

/-- The Hermite inversion formula
`E_μ[f Heₙ(⟪x,ξ⟫/τ(ξ))] = iⁿ τ(ξ)^{-n} (d/dt)ⁿ G_f(tξ)|_{t=0}`. -/
theorem hermiteCoefficient_eq_iteratedDeriv (hμ : IsCenteredGaussian Q μ) {f : H → ℂ}
    (hf : MemLp f 2 μ) {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (n : ℕ) :
    hermiteCoefficient μ Q f ξ n =
      Complex.I ^ n / ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ^ n *
        iteratedDeriv n (fun t : ℝ => hermiteExtension μ Q f ξ t) 0 := by
  have hτ0 : ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  have h := iteratedDeriv_ofReal_of_hasSum_pow
    (fun z => hasSum_hermiteExtension_pow hμ hf hpos z) n
  have key : ∀ A t : ℂ, t ≠ 0 →
      Complex.I ^ n / t ^ n *
          ((n.factorial : ℂ) * ((-(Complex.I * t)) ^ n / (n.factorial : ℂ) * A)) = A := by
    intro A t ht
    have hfac : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hc : Complex.I ^ n * (-(Complex.I * t)) ^ n = t ^ n := by
      rw [← mul_pow, show Complex.I * -(Complex.I * t) = t from by
        linear_combination (-t) * Complex.I_sq]
    field_simp
    linear_combination A * hc
  rw [h, key _ _ hτ0]

end OperatorRidgelet
