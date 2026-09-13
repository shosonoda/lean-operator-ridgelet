import OperatorRidgelet.Sobolev.GaussianFilter
import OperatorRidgelet.Sobolev.Schwartz

/-!
# The rays of the Gaussian-derivative filters

For the filter `ρ_k` of `prop:nonbandpass-sobolev` and the Gaussian target
`g(ξ) = e^{-‖ξ‖²} v`, the ray at direction `a` has the profile
`h_a(ω) = ρ̂_k(-ω) g(ωa) = ω^{2k} e^{-A²ω²} v`, `A = (1+‖a‖²)^{1/2}`, which is the dilate
`A^{-2k} ρ̂_k(Aω) v` of the symbol.  Its coefficient is therefore the dilate
`A^{-2k-1} ρ_k(b/A) v` of the filter, and `lem:sobolev-tools` applies to it at every order `s`
because the filter is a Schwartz function.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The scale `A(a) = (1 + ‖a‖²)^{1/2}` of the ray in direction `a`. -/
def rayScale (a : H) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)

omit [InnerProductSpace ℝ H] in
/-- The scale is at least one. -/
theorem one_le_rayScale (a : H) : 1 ≤ rayScale a := by
  have h : (1 : ℝ) ≤ 1 + ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_le_sqrt h

omit [InnerProductSpace ℝ H] in
/-- The scale is positive. -/
theorem rayScale_pos (a : H) : 0 < rayScale a := lt_of_lt_of_le zero_lt_one (one_le_rayScale a)

omit [InnerProductSpace ℝ H] in
/-- The square of the scale. -/
theorem rayScale_sq (a : H) : rayScale a ^ 2 = 1 + ‖a‖ ^ 2 := by
  rw [rayScale, Real.sq_sqrt (by positivity)]

omit [InnerProductSpace ℝ H] in
/-- The linear weight is dominated by the scale. -/
theorem one_add_norm_le_rayScale (a : H) : 1 + ‖a‖ ≤ Real.sqrt 2 * rayScale a := by
  have h : (1 + ‖a‖) ^ 2 ≤ (Real.sqrt 2 * rayScale a) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), rayScale_sq]
    nlinarith [sq_nonneg (1 - ‖a‖)]
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 * rayScale a :=
    mul_nonneg (Real.sqrt_nonneg 2) (rayScale_pos a).le
  nlinarith [norm_nonneg a]

/-- The Gaussian target `g(ξ) = e^{-‖ξ‖²} v` of `prop:nonbandpass-sobolev`. -/
def gaussTarget (v : Y) (ξ : H) : Y := (Real.exp (-‖ξ‖ ^ 2) : ℝ) • v

/-- The scalar ray `A^{-2k-1} ρ_k(b/A)` of the Gaussian-derivative filter at scale `A`. -/
def gaussRayFun (k : ℕ) (A b : ℝ) : ℂ :=
  (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) • gaussDerivFilterC k (b / A)

/-- The coefficient of the Gaussian-derivative ray: the dilate `A^{-2k-1} ρ_k(b/A) v` of the
filter. -/
def gaussRayCoefficient (k : ℕ) (v : Y) (q : H × ℝ) : Y :=
  gaussRayFun k (rayScale q.1) q.2 • v

omit [InnerProductSpace ℝ H] in
/-- Each scalar ray lies in every Sobolev class. -/
theorem memRaySobolev_gaussRayFun (k : ℕ) {s : ℝ} (hs : 0 ≤ s) (a : H) :
    MemRaySobolev s fun b => gaussRayFun k (rayScale a) b :=
  memRaySobolev_const_smul
    (memRaySobolev_dilate hs (one_le_rayScale a) (memRaySobolev_schwartz s _))

omit [InnerProductSpace ℝ H] in
/-- Each ray lies in every Sobolev class. -/
theorem memRaySobolev_gaussRayCoefficient (k : ℕ) (v : Y) {s : ℝ} (hs : 0 ≤ s) (a : H) :
    MemRaySobolev s fun b => gaussRayCoefficient k v (a, b) :=
  memRaySobolev_smul_const (memRaySobolev_gaussRayFun k hs a) v

omit [InnerProductSpace ℝ H] in
/-- The Sobolev norm of a ray: at most `A^{s-2k-1/2} ‖v‖ ‖ρ_k‖_{H^s}`. -/
theorem raySobolevNorm_gaussRayCoefficient_le (k : ℕ) (v : Y) {s : ℝ} (hs : 0 ≤ s) (a : H) :
    raySobolevNorm s (fun b => gaussRayCoefficient k v (a, b)) ≤
      rayScale a ^ (s - 2 * (k : ℝ) - 1 / 2) *
        (‖v‖ * raySobolevNorm s (gaussDerivFilterC k)) := by
  have hA := one_le_rayScale a
  have hA0 := rayScale_pos a
  set A := rayScale a
  simp only [gaussRayCoefficient, gaussRayFun]
  rw [raySobolevNorm_smul_const, raySobolevNorm_const_smul,
    abs_of_nonneg (Real.rpow_nonneg hA0.le _)]
  have hdil := raySobolevNorm_dilate_le hs hA (memRaySobolev_schwartz s (gaussDerivFilterC k))
  have hmul : ‖v‖ * (A ^ (-(2 * (k : ℝ) + 1)) *
        raySobolevNorm s fun b => gaussDerivFilterC k (b / A)) ≤
      ‖v‖ * (A ^ (-(2 * (k : ℝ) + 1)) *
        (A ^ (s + 1 / 2) * raySobolevNorm s (gaussDerivFilterC k))) := by
    gcongr
  refine hmul.trans (le_of_eq ?_)
  have hexp : A ^ (-(2 * (k : ℝ) + 1)) * A ^ (s + 1 / 2) = A ^ (s - 2 * (k : ℝ) - 1 / 2) := by
    rw [← Real.rpow_add hA0]
    congr 1
    ring
  calc ‖v‖ * (A ^ (-(2 * (k : ℝ) + 1)) *
        (A ^ (s + 1 / 2) * raySobolevNorm s (gaussDerivFilterC k)))
      = (A ^ (-(2 * (k : ℝ) + 1)) * A ^ (s + 1 / 2)) *
          (‖v‖ * raySobolevNorm s (gaussDerivFilterC k)) := by ring
    _ = A ^ (s - 2 * (k : ℝ) - 1 / 2) * (‖v‖ * raySobolevNorm s (gaussDerivFilterC k)) := by
        rw [hexp]

/-! ### Measurability and the profile -/

omit [InnerProductSpace ℝ H] in
/-- The ray scale is continuous. -/
theorem continuous_rayScale : Continuous (rayScale : H → ℝ) :=
  (continuous_const.add (continuous_norm.pow 2)).sqrt

/-- The scalar ray depends continuously on the direction and the bias. -/
theorem continuous_gaussRayFun (k : ℕ) :
    Continuous fun q : H × ℝ => gaussRayFun k (rayScale q.1) q.2 := by
  have hA : Continuous fun q : H × ℝ => rayScale q.1 := continuous_rayScale.comp continuous_fst
  have hne : ∀ q : H × ℝ, rayScale q.1 ≠ 0 := fun q => (rayScale_pos q.1).ne'
  have hc : Continuous fun q : H × ℝ => (rayScale q.1 ^ (-(2 * (k : ℝ) + 1)) : ℝ) :=
    hA.rpow_const fun q => Or.inl (hne q)
  have hdiv : Continuous fun q : H × ℝ => q.2 / rayScale q.1 := continuous_snd.div hA hne
  exact hc.smul ((gaussDerivFilterC k).continuous.comp hdiv)

/-- **The profile of the Gaussian-derivative ray** is `ρ̂_k(-ω) g(ωa)`. -/
theorem rayProfile_gaussRayCoefficient [CompleteSpace Y] (k : ℕ) (v : Y) (a : H) (ω : ℝ) :
    rayProfile (fun b => gaussRayCoefficient k v (a, b)) ω =
      filterFourier (gaussDerivFilter k) (-ω) • gaussTarget v (ω • a) := by
  have hA0 := rayScale_pos a
  set A := rayScale a with hAdef
  have hpow : (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) * (A * A ^ (2 * k)) = 1 := by
    have h1 : A * A ^ (2 * k) = A ^ (1 + ((2 * k : ℕ) : ℝ)) := by
      rw [Real.rpow_add hA0, Real.rpow_one, Real.rpow_natCast]
    rw [h1, ← Real.rpow_add hA0, show -(2 * (k : ℝ) + 1) + (1 + ((2 * k : ℕ) : ℝ)) = 0 by
      push_cast; ring, Real.rpow_zero]
  have hscalar : rayProfile (fun b => gaussRayFun k A b) ω =
      ((ω ^ (2 * k) * Real.exp (-(A ^ 2 * ω ^ 2)) : ℝ) : ℂ) := by
    simp only [gaussRayFun]
    rw [rayProfile_const_smul, rayProfile_dilate hA0, rayProfile_gaussDerivFilterC]
    have hcast : (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) •
        (A • (((A * ω) ^ (2 * k) * Real.exp (-(A * ω) ^ 2) : ℝ) : ℂ)) =
        (((A ^ (-(2 * (k : ℝ) + 1)) : ℝ) *
          (A * ((A * ω) ^ (2 * k) * Real.exp (-(A * ω) ^ 2))) : ℝ) : ℂ) := by
      push_cast [Complex.real_smul]
      ring
    rw [hcast]
    congr 1
    rw [mul_pow A ω (2 * k), show (A * ω) ^ 2 = A ^ 2 * ω ^ 2 from mul_pow A ω 2]
    calc (A ^ (-(2 * (k : ℝ) + 1)) : ℝ) *
          (A * (A ^ (2 * k) * ω ^ (2 * k) * Real.exp (-(A ^ 2 * ω ^ 2))))
        = ((A ^ (-(2 * (k : ℝ) + 1)) : ℝ) * (A * A ^ (2 * k))) *
            (ω ^ (2 * k) * Real.exp (-(A ^ 2 * ω ^ 2))) := by ring
      _ = ω ^ (2 * k) * Real.exp (-(A ^ 2 * ω ^ 2)) := by rw [hpow, one_mul]
  have hnorm : ‖ω • a‖ ^ 2 = ω ^ 2 * ‖a‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hrhs : filterFourier (gaussDerivFilter k) (-ω) • gaussTarget v (ω • a) =
      ((ω ^ (2 * k) * Real.exp (-(A ^ 2 * ω ^ 2)) : ℝ) : ℂ) • v := by
    rw [filterFourier_gaussDerivFilter, gaussTarget, hnorm]
    rw [show (-ω) ^ (2 * k) = ω ^ (2 * k) by rw [pow_mul, pow_mul, neg_pow]; simp,
      show (-ω) ^ 2 = ω ^ 2 from neg_pow_two ω]
    have hsm : (Real.exp (-(ω ^ 2 * ‖a‖ ^ 2)) : ℝ) • v
        = ((Real.exp (-(ω ^ 2 * ‖a‖ ^ 2)) : ℝ) : ℂ) • v := by
      rw [← IsScalarTower.algebraMap_smul ℂ (Real.exp (-(ω ^ 2 * ‖a‖ ^ 2))) v]
      simp
    rw [hsm, smul_smul, ← Complex.ofReal_mul]
    congr 1
    rw [mul_assoc, ← Real.exp_add, hAdef, rayScale_sq]
    congr 2
    ring_nf
  rw [hrhs]
  simp only [gaussRayCoefficient]
  rw [rayProfile_smul_const, hscalar]

/-! ### Measurability and the Sobolev mass -/

section Measurable

variable [MeasurableSpace H] [BorelSpace H]

/-- The coefficient is jointly strongly measurable. -/
theorem stronglyMeasurable_gaussRayCoefficient (k : ℕ) (v : Y) :
    StronglyMeasurable (gaussRayCoefficient (H := H) k v) := by
  have h : StronglyMeasurable fun q : H × ℝ => gaussRayFun k (rayScale q.1) q.2 :=
    (continuous_gaussRayFun k).stronglyMeasurable
  exact h.smul stronglyMeasurable_const

/-- A power of the ray scale is a power of `1 + ‖a‖²`. -/
theorem rayScale_rpow (a : H) (x : ℝ) : rayScale a ^ x = (1 + ‖a‖ ^ 2) ^ (x / 2) := by
  rw [rayScale, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The pointwise bound behind the finiteness of the Sobolev mass. -/
theorem one_add_norm_rpow_mul_raySobolevNorm_le (k : ℕ) (v : Y) {s : ℝ} (hs : 0 ≤ s) (a : H) :
    (1 + ‖a‖) ^ s * raySobolevNorm s (fun b => gaussRayCoefficient k v (a, b)) ≤
      (Real.sqrt 2 ^ s * (‖v‖ * raySobolevNorm s (gaussDerivFilterC k))) *
        (1 + ‖a‖ ^ 2) ^ ((2 * s - 2 * (k : ℝ) - 1 / 2) / 2) := by
  have hA0 := rayScale_pos a
  have hnn : (0 : ℝ) ≤ 1 + ‖a‖ := by positivity
  have h1 : (1 + ‖a‖) ^ s ≤ Real.sqrt 2 ^ s * rayScale a ^ s := by
    rw [← Real.mul_rpow (Real.sqrt_nonneg 2) hA0.le]
    exact Real.rpow_le_rpow hnn (one_add_norm_le_rayScale a) hs
  have h2 := raySobolevNorm_gaussRayCoefficient_le k v hs a
  have hN : 0 ≤ ‖v‖ * raySobolevNorm s (gaussDerivFilterC k) :=
    mul_nonneg (norm_nonneg v) (raySobolevNorm_nonneg s (⇑(gaussDerivFilterC k)))
  calc (1 + ‖a‖) ^ s * raySobolevNorm s (fun b => gaussRayCoefficient k v (a, b))
      ≤ (Real.sqrt 2 ^ s * rayScale a ^ s) *
          (rayScale a ^ (s - 2 * (k : ℝ) - 1 / 2) *
            (‖v‖ * raySobolevNorm s (gaussDerivFilterC k))) := by
        refine mul_le_mul h1 h2 (raySobolevNorm_nonneg s _) (by positivity)
    _ = (Real.sqrt 2 ^ s * (‖v‖ * raySobolevNorm s (gaussDerivFilterC k))) *
          (rayScale a ^ s * rayScale a ^ (s - 2 * (k : ℝ) - 1 / 2)) := by ring
    _ = (Real.sqrt 2 ^ s * (‖v‖ * raySobolevNorm s (gaussDerivFilterC k))) *
          (1 + ‖a‖ ^ 2) ^ ((2 * s - 2 * (k : ℝ) - 1 / 2) / 2) := by
        rw [← Real.rpow_add hA0, rayScale_rpow]
        congr 2
        ring

/-- **The Sobolev mass of the Gaussian-derivative rays is finite** in the range
`2k > α + 2s - 1/2` of `eq:nonbandpass-order`. -/
theorem lintegral_raySobolevNorm_gaussRayCoefficient_ne_top {k : ℕ} {α s : ℝ} (hα : 0 < α)
    (hs : 0 ≤ s) (hk : α + 2 * s - 1 / 2 < 2 * k) {ν : Measure H} (hν : IsHomogeneous α ν)
    (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (v : Y) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s *
      raySobolevNorm s fun b => gaussRayCoefficient k v (a, b)) ∂ν ≠ ⊤ := by
  set C : ℝ := Real.sqrt 2 ^ s * (‖v‖ * raySobolevNorm s (gaussDerivFilterC k)) with hC
  have hCnn : 0 ≤ C :=
    mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg 2) s)
      (mul_nonneg (norm_nonneg v) (raySobolevNorm_nonneg s (⇑(gaussDerivFilterC k))))
  set e : ℝ := (2 * s - 2 * (k : ℝ) - 1 / 2) / 2 with he
  have hbound : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s *
      raySobolevNorm s fun b => gaussRayCoefficient k v (a, b)) ∂ν ≤
      ENNReal.ofReal C * ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖ ^ 2) ^ e) ∂ν := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun a => ?_
    rw [← ENNReal.ofReal_mul hCnn]
    exact ENNReal.ofReal_le_ofReal (one_add_norm_rpow_mul_raySobolevNorm_le k v hs a)
  refine ne_top_of_le_ne_top ?_ hbound
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  refine (hν.lintegral_one_add_norm_sq_rpow_lt_top hα hB ?_).ne
  rw [he]
  linarith

end Measurable

end OperatorRidgelet
