import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.Reconstruction.Basic

/-!
# Ray regularity of the transform of a neural-operator layer

The transform of the scalar observable of a neural-operator layer with Gaussian activation is a
Bochner integral
`𝒢_Q F_φ(ξ) = ∫ w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2} m(dy)`
of Gaussian-type densities whose covariances `S_y` obey the two-sided bound
`θ Q ≤ S_y`, `‖S_y‖ ≤ ‖Q‖ (1 + ‖Q‖ ‖A‖_∞²)` uniformly in `y`.  The weight `w_φ` is only
integrable, not bounded, so Lemma `lem:ray-regular-examples`(c) (`IsRegularAlongRays.integral`)
is applied here in the weighted form `IsRegularAlongRays.integral_weighted`, in which the
family is dominated by `W y` with `W ∈ L¹(m)` — the manuscript's device of running the argument
for the finite measure `|w_φ| m` and the family `(w_φ/|w_φ|) G_y`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace Polynomial

/-! ### The weighted form of Lemma `lem:ray-regular-examples`(c) -/

section Weighted

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

omit [OpensMeasurableSpace H] in
/-- **Lemma `lem:ray-regular-examples`(c), weighted form.**  For a measurable family `G y` of
densities dominated by an integrable weight `W ∈ L¹(m)`, smooth along rays on a common open
neighbourhood `U` of `I`, and with ray-derivative bounds of the product form `h(a) W(y)` whose
`h` is `ν`-integrable against `(1+‖a‖)^{k+2}`, the Bochner integral `ξ ↦ ∫ G y ξ ∂m` is regular
along rays. -/
theorem IsRegularAlongRays.integral_weighted {ν : Measure H} {I : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] {G : Ω → H → ℂ}
    (hGm : Measurable (Function.uncurry G)) {W : Ω → ℝ} (hW : Integrable W m)
    (hW0 : ∀ y, 0 ≤ W y) (hGb : ∀ y ξ, ‖G y ξ‖ ≤ W y) {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ, (∀ a, 0 ≤ h a) ∧
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ ENNReal.ofReal (h a * W y)) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  have hc : (∫⁻ y, ENNReal.ofReal (W y) ∂m) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hW.hasFiniteIntegral.ne (lintegral_mono fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hmeas : ∀ (a : H) (k : ℕ), ∀ t ∈ U,
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m :=
    fun a k t ht => (measurable_iteratedDeriv_of_forall_contDiffOn (f := fun y ω => G y (ω • a))
      (fun t => hGm.comp (measurable_id.prodMk measurable_const))
      (fun y => ⟨U, hU, ht, hsmooth y a⟩) k).aestronglyMeasurable
  have hbound : ∀ (a : H) (k : ℕ), ∃ B : Ω → ℝ, Integrable B m ∧
      ∀ y, ∀ t ∈ U, ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ ≤ B y := by
    intro a k
    obtain ⟨h, hh0, -, hh⟩ := hunif k
    refine ⟨fun y => h a * W y, hW.const_mul _, fun y t ht => ?_⟩
    have h1 : ‖iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t‖ₑ ≤
        ENNReal.ofReal (h a * W y) :=
      (enorm_iteratedDeriv_le_rayDerivBound U (G y) le_rfl a ht).trans (hh y a)
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hh0 a) (hW0 y))).mp h1
  refine ⟨hGm.stronglyMeasurable.integral_prod_left', ⟨∫ y, W y ∂m, fun ξ => ?_⟩,
    fun a => ⟨U, hU, hIU, ?_⟩, ?_⟩
  · exact norm_integral_le_of_norm_le hW (Eventually.of_forall fun y => hGb y ξ)
  · exact contDiffOn_integral_of_dominated hU (fun y => hsmooth y a) (hmeas a) (hbound a)
  · intro k
    obtain ⟨h, hh0, hint, hh⟩ := hunif k
    have hray : ∀ a, rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ≤
        ENNReal.ofReal (h a) * ∫⁻ y, ENNReal.ofReal (W y) ∂m := by
      intro a
      refine iSup_le fun j => iSup₂_le fun ω hω => ?_
      have hωU : ω ∈ U := hIU hω
      change ‖iteratedDeriv (j : ℕ) (fun ω : ℝ => ∫ y, G y (ω • a) ∂m) ω‖ₑ ≤ _
      rw [iteratedDeriv_integral_eq hU (fun y => hsmooth y a) (hmeas a) (hbound a) j hωU,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
      refine ((enorm_iteratedDeriv_le_rayDerivBound U (G y) (Nat.lt_succ_iff.mp j.2) a hωU).trans
        (hh y a)).trans ?_
      rw [ENNReal.ofReal_mul (hh0 a)]
    unfold rayMoment
    calc ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) *
          rayDerivBound I (fun ξ => ∫ y, G y ξ ∂m) k a ∂ν
        ≤ ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) *
            (∫⁻ y, ENNReal.ofReal (W y) ∂m) ∂ν :=
          lintegral_mono fun a => by
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (hray a)
      _ = (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) *
            ∫⁻ y, ENNReal.ofReal (W y) ∂m := lintegral_mul_const' _ _ hc
      _ < ⊤ := ENNReal.mul_lt_top hint (lt_top_iff_ne_top.mpr hc)

end Weighted

/-! ### Uniform ray bounds for the Gaussian densities of a layer -/

section LayerDensity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Along the ray through `a`, the quadratic form is `⟪S(ωa), ωa⟫ = ω² ⟪Sa,a⟫`. -/
theorem inner_map_smul_self (S : H →L[ℝ] H) (a : H) (ω : ℝ) :
    ⟪S (ω • a), ω • a⟫ = ω ^ 2 * ⟪S a, a⟫ := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Along a ray, `e^{-⟪Sξ,ξ⟫/2}` is the Gaussian `e^{-κ(a) ω²/2}` with the trivial polynomial. -/
theorem ofReal_exp_inner_map_smul_self (S : H →L[ℝ] H) (a : H) (ω : ℝ) :
    ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ) =
      (1 : ℂ[X]).eval (ω : ℂ) * Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2)) := by
  rw [Polynomial.eval_one, one_mul, inner_map_smul_self, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Along every ray, `ξ ↦ c e^{-⟪Sξ,ξ⟫/2}` is smooth. -/
theorem contDiff_const_mul_ofReal_exp_inner_map_smul_self (S : H →L[ℝ] H) (c : ℂ) (a : H)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n fun ω : ℝ => c * ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ) := by
  have hfun : (fun ω : ℝ => c * ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ)) =
      fun ω : ℝ => c * ((1 : ℂ[X]).eval (ω : ℂ) *
        Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2))) :=
    funext fun ω => by rw [ofReal_exp_inner_map_smul_self]
  rw [hfun]
  exact contDiff_const.mul (Polynomial.contDiff_eval_ofReal_mul_cexp _ _)

/-- **The uniform ray-derivative bound of Example `ex:operator-layer`(ii).**  For a positive `S`
with `‖S‖ ≤ B`, every ray derivative of `ξ ↦ e^{-⟪Sξ,ξ⟫/2}` on the annulus `r ≤ |ω| ≤ R` is
bounded by `(n+1)(n + B(1+‖a‖)²)^n (1+|R|)^n e^{-r²⟪Sa,a⟫/2}`, with constants depending on `S`
only through the bound `B`. -/
theorem norm_iteratedDeriv_ofReal_exp_inner_map_smul_self_le {S : H →L[ℝ] H}
    (hS0 : ∀ ξ, 0 ≤ ⟪S ξ, ξ⟫) {B : ℝ} (hSB : ‖S‖ ≤ B) {r : ℝ} (hr : 0 ≤ r) {R : ℝ} (n : ℕ)
    (a : H) {ω : ℝ} (hrω : r ≤ |ω|) (hωR : |ω| ≤ R) :
    ‖iteratedDeriv n (fun ω : ℝ => ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ)) ω‖ ≤
      ((n : ℝ) + 1) * ((n : ℝ) + B * (1 + ‖a‖) ^ 2) ^ n * (1 + |R|) ^ n *
        Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
  have hfun : (fun ω : ℝ => ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ)) =
      fun ω : ℝ => (1 : ℂ[X]).eval (ω : ℂ) *
        Complex.exp (-(((⟪S a, a⟫ : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2)) :=
    funext (ofReal_exp_inner_map_smul_self S a)
  rw [hfun]
  have hcoeff : ∀ j, ‖(1 : ℂ[X]).coeff j‖ ≤ 1 := fun j => by
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [Polynomial.coeff_one, hj]
  have hbound := Polynomial.norm_iteratedDeriv_eval_ofReal_mul_cexp_le ⟪S a, a⟫
    (p := (1 : ℂ[X])) (d := 0) (by simp) hcoeff n ω
  refine hbound.trans ?_
  have hκ0 : 0 ≤ ⟪S a, a⟫ := hS0 a
  have hB0 : 0 ≤ B := (norm_nonneg S).trans hSB
  have hκB : |⟪S a, a⟫| ≤ B * (1 + ‖a‖) ^ 2 := by
    rw [abs_of_nonneg hκ0]
    have h1 : ⟪S a, a⟫ ≤ ‖S a‖ * ‖a‖ := real_inner_le_norm _ _
    have h2 : ‖S a‖ ≤ ‖S‖ * ‖a‖ := S.le_opNorm a
    nlinarith [norm_nonneg a, norm_nonneg S, norm_nonneg (S a)]
  have hωle : 1 + |ω| ≤ 1 + |R| := by
    have := hωR.trans (le_abs_self R)
    linarith
  have hexp : Real.exp (-(⟪S a, a⟫ * ω ^ 2 / 2)) ≤ Real.exp (-(r ^ 2 / 2) * ⟪S a, a⟫) := by
    rw [Real.exp_le_exp]
    have hrr : r ^ 2 ≤ ω ^ 2 := by
      rw [← sq_abs ω]
      exact pow_le_pow_left₀ hr hrω 2
    nlinarith
  simp only [Nat.cast_zero, zero_add, mul_one]
  gcongr

end LayerDensity

/-! ### The uniform bound on the layer covariances -/

section LayerCovariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace H] [InnerProductSpace ℂ Y] in
/-- `‖S_y‖ ≤ ‖Q‖ + ‖Q‖² ‖A‖_∞²`, uniformly in the layer parameter `y`. -/
theorem IsLayerData.norm_layerCovariance_le {Q : H →L[ℝ] H} (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {m : Measure Ω} {a : Ω → H} {b : Ω → Y} (hL : IsLayerData m a b) (y : Ω) :
    ‖layerCovariance Q a y‖ ≤ ‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  have hσ : 0 ≤ ⟪Q (a y), a y⟫ := hQ0 (a y)
  have h1σ : (1 : ℝ) ≤ 1 + ⟪Q (a y), a y⟫ := by linarith
  have hc : (1 + ⟪Q (a y), a y⟫)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1σ
  have hc0 : 0 ≤ (1 + ⟪Q (a y), a y⟫)⁻¹ := by positivity
  have hQa : ‖Q (a y)‖ ≤ ‖Q‖ * layerSupNorm a :=
    (Q.le_opNorm (a y)).trans (by
      have := hL.norm_le_layerSupNorm y
      have := norm_nonneg Q
      nlinarith)
  have hstep : layerCovariance Q a y ξ =
      Q ξ - (1 + ⟪Q (a y), a y⟫)⁻¹ • (⟪Q (a y), ξ⟫ • Q (a y)) := by
    simp only [layerCovariance, sub_apply, smul_apply, InnerProductSpace.rankOne_apply]
  rw [hstep]
  have h2 : ‖(1 + ⟪Q (a y), a y⟫)⁻¹ • (⟪Q (a y), ξ⟫ • Q (a y))‖ ≤
      ‖Q (a y)‖ * ‖Q (a y)‖ * ‖ξ‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc0]
    have habs : |⟪Q (a y), ξ⟫| ≤ ‖Q (a y)‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    calc (1 + ⟪Q (a y), a y⟫)⁻¹ * (|⟪Q (a y), ξ⟫| * ‖Q (a y)‖)
        ≤ 1 * ((‖Q (a y)‖ * ‖ξ‖) * ‖Q (a y)‖) := by
          gcongr
      _ = ‖Q (a y)‖ * ‖Q (a y)‖ * ‖ξ‖ := by ring
  have hQ0' : 0 ≤ ‖Q‖ := norm_nonneg Q
  have hA0 : 0 ≤ layerSupNorm a := layerSupNorm_nonneg a
  calc ‖Q ξ - (1 + ⟪Q (a y), a y⟫)⁻¹ • (⟪Q (a y), ξ⟫ • Q (a y))‖
      ≤ ‖Q ξ‖ + ‖(1 + ⟪Q (a y), a y⟫)⁻¹ • (⟪Q (a y), ξ⟫ • Q (a y))‖ := norm_sub_le _ _
    _ ≤ ‖Q‖ * ‖ξ‖ + ‖Q (a y)‖ * ‖Q (a y)‖ * ‖ξ‖ := by
        gcongr
        exact Q.le_opNorm ξ
    _ ≤ ‖Q‖ * ‖ξ‖ + (‖Q‖ * layerSupNorm a) * (‖Q‖ * layerSupNorm a) * ‖ξ‖ := by
        gcongr
    _ = (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * ‖ξ‖ := by ring

end LayerCovariance

end OperatorRidgelet
