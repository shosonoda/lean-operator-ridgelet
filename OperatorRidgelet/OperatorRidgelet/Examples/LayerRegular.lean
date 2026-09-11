import OperatorRidgelet.Examples.OperatorLayer
import OperatorRidgelet.Examples.GaussianMeasurability
import OperatorRidgelet.Transform.Plancherel
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
theorem IsRegularAlongRays.integral_weighted_of_measurable_derivatives {ν : Measure H}
    {I : Set ℝ} {Ω Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] {G : Ω → H → Y}
    (hGm : Measurable (Function.uncurry G)) {W : Ω → ℝ} (hW : Integrable W m)
    (hW0 : ∀ y, 0 ≤ W y) (hGb : ∀ y ξ, ‖G y ξ‖ ≤ W y) {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hmeas : ∀ (a : H) (k : ℕ), ∀ t ∈ U,
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ, (∀ a, 0 ≤ h a) ∧
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ ENNReal.ofReal (h a * W y)) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  have hc : (∫⁻ y, ENNReal.ofReal (W y) ∂m) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hW.hasFiniteIntegral.ne (lintegral_mono fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
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

/-- Scalar specialization with automatically measurable ray derivatives. -/
theorem IsRegularAlongRays.integral_weighted {ν : Measure H} {I : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] {G : Ω → H → ℂ}
    (hGm : Measurable (Function.uncurry G)) {W : Ω → ℝ} (hW : Integrable W m)
    (hW0 : ∀ y, 0 ≤ W y) (hGb : ∀ y ξ, ‖G y ξ‖ ≤ W y) {U : Set ℝ} (hU : IsOpen U) (hIU : I ⊆ U)
    (hsmooth : ∀ y a, ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G y (ω • a)) U)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ, (∀ a, 0 ≤ h a) ∧
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * ENNReal.ofReal (h a) ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound U (G y) k a ≤ ENNReal.ofReal (h a * W y)) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  have hmeas : ∀ (a : H) (k : ℕ), ∀ t ∈ U,
      AEStronglyMeasurable (fun y => iteratedDeriv k (fun ω : ℝ => G y (ω • a)) t) m :=
    fun a k t ht => (measurable_iteratedDeriv_of_forall_contDiffOn (f := fun y ω => G y (ω • a))
      (fun t => hGm.comp (measurable_id.prodMk measurable_const))
      (fun y => ⟨U, hU, ht, hsmooth y a⟩) k).aestronglyMeasurable
  exact integral_weighted_of_measurable_derivatives m hGm hW hW0 hGb hU hIU hsmooth hmeas hunif

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

/-! ### Ray regularity of the transform of the scalar observable -/

section RayRegular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} {a : Ω → H} {b : Ω → Y}

/-- The constant factor `w_φ(y) (1+σ_y²)^{-1/2}` of the `y`-th Gaussian density of the layer. -/
def layerDensityConst (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (φ : Y) (y : Ω) : ℂ :=
  layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ : ℝ) : ℂ)

/-- The `y`-th Gaussian density `G_y(ξ) = w_φ(y) (1+σ_y²)^{-1/2} e^{-⟪S_yξ,ξ⟫/2}` whose Bochner
integral over `m` is the transform `𝒢_Q F_φ` of the scalar observable of the layer. -/
def layerDensity (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (φ : Y) (y : Ω) (ξ : H) : ℂ :=
  layerWeight b φ y * (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
    Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ)

/-- The scalar layer density separates into its ray profile and radial exponential factor. -/
theorem layerDensity_eq (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (φ : Y) (y : Ω) (ξ : H) :
    layerDensity Q a b φ y ξ = layerDensityConst Q a b φ y *
      ((Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) := by
  simp only [layerDensity, layerDensityConst, Complex.ofReal_mul]
  ring

/-- `|w_φ(y)(1+σ_y²)^{-1/2}| ≤ |w_φ(y)|`. -/
theorem norm_layerDensityConst_le {Q : H →L[ℝ] H} (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (a : Ω → H)
    (b : Ω → Y) (φ : Y) (y : Ω) : ‖layerDensityConst Q a b φ y‖ ≤ ‖layerWeight b φ y‖ := by
  rw [layerDensityConst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_right (norm_nonneg _) (inv_le_one_of_one_le₀ ?_)
  exact Real.one_le_sqrt.mpr (by linarith [hQ0 (a y)])

/-- `|G_y(ξ)| ≤ |w_φ(y)|`, uniformly in `ξ`. -/
theorem norm_layerDensity_le {Q : H →L[ℝ] H} (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫) (a : Ω → H) (b : Ω → Y)
    (φ : Y) (y : Ω) {ξ : H} (hS0 : 0 ≤ ⟪layerCovariance Q a y ξ, ξ⟫) :
    ‖layerDensity Q a b φ y ξ‖ ≤ ‖layerWeight b φ y‖ := by
  rw [layerDensity_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans
    (norm_layerDensityConst_le hQ0 a b φ y)
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- The family of densities is jointly measurable. -/
theorem IsLayerData.measurable_uncurry_layerDensity {Q : H →L[ℝ] H} (hL : IsLayerData m a b)
    (φ : Y) : Measurable (Function.uncurry (layerDensity Q a b φ)) := by
  have hA : StronglyMeasurable fun p : Ω × H => a p.1 :=
    hL.stronglyMeasurable_a.comp_measurable measurable_fst
  have hx : StronglyMeasurable fun p : Ω × H => p.2 := measurable_snd.stronglyMeasurable
  have hQa : StronglyMeasurable fun p : Ω × H => Q (a p.1) :=
    Q.continuous.comp_stronglyMeasurable hA
  have hQx : StronglyMeasurable fun p : Ω × H => Q p.2 :=
    Q.continuous.comp_stronglyMeasurable hx
  have h1 : Measurable fun p : Ω × H => ⟪Q (a p.1), p.2⟫ := (hQa.inner hx).measurable
  have h2 : Measurable fun p : Ω × H => ⟪Q p.2, p.2⟫ := (hQx.inner hx).measurable
  have h3 : Measurable fun p : Ω × H => ⟪Q (a p.1), a p.1⟫ := (hQa.inner hA).measurable
  have hκ : Measurable fun p : Ω × H => ⟪layerCovariance Q a p.1 p.2, p.2⟫ := by
    have heq : (fun p : Ω × H => ⟪layerCovariance Q a p.1 p.2, p.2⟫) =
        fun p : Ω × H => ⟪Q p.2, p.2⟫ - ⟪Q (a p.1), p.2⟫ ^ 2 / (1 + ⟪Q (a p.1), a p.1⟫) :=
      funext fun p => inner_layerCovariance Q a p.1 p.2
    rw [heq]
    exact h2.sub ((h1.pow_const 2).div (measurable_const.add h3))
  have hconst : Measurable fun p : Ω × H => layerDensityConst Q a b φ p.1 :=
    ((hL.stronglyMeasurable_layerWeight φ).measurable.comp measurable_fst).mul
      (Complex.measurable_ofReal.comp
        ((Real.continuous_sqrt.measurable.comp (measurable_const.add h3)).inv))
  have hexp : Measurable fun p : Ω × H =>
      ((Real.exp (-⟪layerCovariance Q a p.1 p.2, p.2⟫ / 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hκ.neg.div_const 2))
  have huncurry : Function.uncurry (layerDensity Q a b φ) = fun p : Ω × H =>
      layerDensityConst Q a b φ p.1 *
        ((Real.exp (-⟪layerCovariance Q a p.1 p.2, p.2⟫ / 2) : ℝ) : ℂ) :=
    funext fun p => layerDensity_eq Q a b φ p.1 p.2
  rw [huncurry]
  exact hconst.mul hexp

variable [IsFiniteMeasure m]

/-- **Example `ex:operator-layer`(ii)**: the transform `𝒢_Q F_φ` of the scalar observable of a
layer with Gaussian activation is regular along rays, for every compact frequency window away
from the origin.  The densities `G_y` are Gaussian with covariances `S_y` satisfying
`θ Q ≤ S_y` and `‖S_y‖ ≤ ‖Q‖ + ‖Q‖²‖A‖_∞²` uniformly in `y`, so the ray-derivative bounds are
uniform in `y` up to the factor `|w_φ(y)|`, and the weighted form of Lemma
`lem:ray-regular-examples`(c) applies. -/
theorem IsLayerData.isRegularAlongRays_gaussFourier_layerObservable_gaussianFun
    {Q : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y) (ν : Measure H)
    (hdecay : ∀ t : ℝ, 0 < t → ∀ k : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * k) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν)
    {I : Set ℝ} (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) :
    IsRegularAlongRays ν I (gaussFourier μ (layerObservable m a b gaussianFun φ)) := by
  obtain ⟨r, R, hr, hrR⟩ := hI.exists_pos_le_abs_le hI0
  have hθ : (0 : ℝ) < (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ := by positivity
  have ht : (0 : ℝ) < ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) :=
    mul_pos (div_pos (pow_pos (by linarith) 2) two_pos) hθ
  have hSB : ∀ y : Ω, ‖layerCovariance Q a y‖ ≤ (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) :=
    fun y => hL.norm_layerCovariance_le hQ.inner_nonneg y
  have hS0 : ∀ (y : Ω) (ξ : H), 0 ≤ ⟪layerCovariance Q a y ξ, ξ⟫ := fun y ξ =>
    le_trans (mul_nonneg hθ.le (hQ.inner_nonneg ξ)) (hL.inner_layerCovariance_ge hQ y ξ)
  -- the transform is the Bochner integral of the Gaussian densities
  have hGfun : gaussFourier μ (layerObservable m a b gaussianFun φ) =
      fun ξ => ∫ y, layerDensity Q a b φ y ξ ∂m :=
    funext fun ξ =>
      hL.gaussFourier_layerObservable_gaussianFun hQ.isSelfAdjoint hQ.inner_nonneg hμ φ ξ
  rw [hGfun]
  -- an open annulus around the window
  have hU : IsOpen ({ω : ℝ | r / 2 < |ω|} ∩ {ω : ℝ | |ω| < R + 1}) :=
    (isOpen_lt continuous_const continuous_abs).inter (isOpen_lt continuous_abs continuous_const)
  have hIU : I ⊆ {ω : ℝ | r / 2 < |ω|} ∩ {ω : ℝ | |ω| < R + 1} := fun ω hω =>
    ⟨by have := (hrR ω hω).1; simp only [Set.mem_setOf_eq]; linarith,
     by have := (hrR ω hω).2; simp only [Set.mem_setOf_eq]; linarith⟩
  refine IsRegularAlongRays.integral_weighted m (hL.measurable_uncurry_layerDensity (Q := Q) φ)
    (W := fun y => ‖layerWeight b φ y‖) (hL.integrable_layerWeight φ).norm
    (fun y => norm_nonneg _)
    (fun y ξ => norm_layerDensity_le hQ.inner_nonneg a b φ y (hS0 y ξ)) hU hIU
    (fun y a' => ?_) (fun k => ?_)
  · have hfun : (fun ω : ℝ => layerDensity Q a b φ y (ω • a')) =
        fun ω : ℝ => layerDensityConst Q a b φ y *
          ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ) :=
      funext fun ω => layerDensity_eq Q a b φ y (ω • a')
    rw [hfun]
    exact (contDiff_const_mul_ofReal_exp_inner_map_smul_self
      (layerCovariance Q a y) _ a').contDiffOn
  -- the uniform ray-derivative bound
  refine ⟨fun a' => ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
      (1 + ‖a'‖) ^ 2) ^ k *
    (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) *
        ⟪Q a', a'⟫), fun a' => by positivity, ?_, ?_⟩
  · -- integrability of the weight
    have hint : Integrable (fun a' : H =>
        (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
            (1 + |R + 1|) ^ k) * 2 ^ (3 * k + 2) *
          (2 + ‖a'‖ ^ (2 * (3 * k + 2))) *
              Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)) ν := by
      have h0 := hdecay ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) ht 0
      have hN := hdecay ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) ht (3 * k + 2)
      simp only [mul_zero, pow_zero, one_mul] at h0
      refine (((h0.const_mul 2).add hN).const_mul
        ((((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
            (1 + |R + 1|) ^ k) *
          2 ^ (3 * k + 2))).congr (Filter.Eventually.of_forall fun a' => ?_)
      simp only [Pi.add_apply]
      ring
    refine lt_of_le_of_lt (lintegral_mono fun a' => ?_) hint.lintegral_lt_top
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    beta_reduce
    have ha1 : (1 : ℝ) ≤ (1 + ‖a'‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg a'])
    have hstep : ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k ≤
        ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k * (1 + ‖a'‖) ^ (2 * k) := by
      have hnn : (0 : ℝ) ≤
          (k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 := by positivity
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hle : (k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 ≤
          ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) * (1 + ‖a'‖) ^ 2 := by
        nlinarith [ha1, hk0, mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)
          (show (0 : ℝ) ≤ (1 + ‖a'‖) ^ 2 - 1 by linarith)]
      calc ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k
          ≤ (((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) * (1 + ‖a'‖) ^ 2) ^ k :=
            pow_le_pow_left₀ hnn hle k
        _ = ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
              (1 + ‖a'‖) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    have hpow : (1 + ‖a'‖) ^ (k + 2) * (1 + ‖a'‖) ^ (2 * k) ≤
        2 ^ (3 * k + 2) * (2 + ‖a'‖ ^ (2 * (3 * k + 2))) := by
      rw [← pow_add]
      have hidx : k + 2 + 2 * k = 3 * k + 2 := by ring
      rw [hidx]
      exact one_add_pow_le_two_pow_mul_two_add_pow (3 * k + 2) (norm_nonneg a')
    calc (1 + ‖a'‖) ^ (k + 2) *
        (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k *
          (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) *
              ⟪Q a', a'⟫))
        ≤ (1 + ‖a'‖) ^ (k + 2) * (((k : ℝ) + 1) *
            (((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k * (1 + ‖a'‖) ^ (2 * k)) *
            (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹)
                * ⟪Q a', a'⟫)) := by gcongr
      _ = (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) *
            ((1 + ‖a'‖) ^ (k + 2) * (1 + ‖a'‖) ^ (2 * k)) *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) := by ring
      _ ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) *
            (2 ^ (3 * k + 2) * (2 + ‖a'‖ ^ (2 * (3 * k + 2)))) *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)
                := by gcongr
      _ = (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) * 2 ^ (3 * k + 2) *
            (2 + ‖a'‖ ^ (2 * (3 * k + 2))) *
                Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)
                := by ring
  · -- the pointwise bound on the ray derivatives
    intro y a'
    refine iSup_le fun j => iSup₂_le fun ω hω => ?_
    have hωr : r / 2 ≤ |ω| := le_of_lt hω.1
    have hωR : |ω| ≤ R + 1 := le_of_lt hω.2
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
    have hjkR : ((j : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    have hfun : (fun ω : ℝ => layerDensity Q a b φ y (ω • a')) =
        fun ω : ℝ => layerDensityConst Q a b φ y *
          ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ) :=
      funext fun ω => layerDensity_eq Q a b φ y (ω • a')
    rw [← ofReal_norm, hfun]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [iteratedDeriv_const_mul_field, norm_mul]
    have hd := norm_iteratedDeriv_ofReal_exp_inner_map_smul_self_le (hS0 y) (hSB y)
      (r := r / 2) (by positivity) (R := R + 1) (j : ℕ) a' hωr hωR
    have hA1 : ((j : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 1 := by linarith
    have hA2 : (((j : ℕ) : ℝ) + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ (j : ℕ) ≤
        ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k := by
      refine le_trans (pow_le_pow_left₀ (by positivity) (by linarith) (j : ℕ))
        (pow_le_pow_right₀ ?_ hjk)
      have : (0 : ℝ) ≤ (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 := by positivity
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hA3 : (1 + |R + 1|) ^ (j : ℕ) ≤ (1 + |R + 1|) ^ k :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (R + 1)]) hjk
    have hA4 : Real.exp (-((r / 2) ^ 2 / 2) * ⟪layerCovariance Q a y a', a'⟫) ≤
        Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) := by
      rw [Real.exp_le_exp]
      have h1 := hL.inner_layerCovariance_ge hQ y a'
      nlinarith [sq_nonneg (r / 2), hQ.inner_nonneg a', div_nonneg (sq_nonneg (r / 2)) two_pos.le]
    have hstep : ‖iteratedDeriv (j : ℕ) (fun ω : ℝ =>
          ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ)) ω‖ ≤
        ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
            (1 + ‖a'‖) ^ 2) ^ k * (1 + |R + 1|) ^ k *
          Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) :=
      hd.trans (by
        refine mul_le_mul (mul_le_mul (mul_le_mul hA1 hA2 (by positivity) (by positivity)) hA3
          (by positivity) (by positivity)) hA4 (Real.exp_nonneg _) (by positivity))
    calc ‖layerDensityConst Q a b φ y‖ *
          ‖iteratedDeriv (j : ℕ) (fun ω : ℝ =>
            ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ)) ω‖
        ≤ ‖layerWeight b φ y‖ * (((k : ℝ) + 1) *
            ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k *
                (1 + |R + 1|) ^ k *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)) :=
          mul_le_mul (norm_layerDensityConst_le hQ.inner_nonneg a b φ y) hstep
            (norm_nonneg _) (norm_nonneg _)
      _ = ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
          (1 + ‖a'‖) ^ 2) ^ k * (1 + |R + 1|) ^ k *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) *
                ‖layerWeight b φ y‖ := by ring

/-- The transform of the scalar observable is integrable against every direction measure with
the Gaussian decay of Lemma `lem:gaussian-decay`(i). -/
theorem IsLayerData.integrable_gaussFourier_layerObservable_gaussianFun {Q : H →L[ℝ] H}
    (hQ : IsPositiveTraceClass Q) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (φ : Y) {ν : Measure H}
    (hdecay : ∀ t : ℝ, 0 < t → ∀ k : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * k) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν) :
    Integrable (gaussFourier μ (layerObservable m a b gaussianFun φ)) ν := by
  have h0 := hdecay ((1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ / 2) (by positivity) 0
  simp only [mul_zero, pow_zero, one_mul] at h0
  have hcont : Continuous (gaussFourier μ (layerObservable m a b gaussianFun φ)) :=
    continuous_gaussFourier μ (hL.integrable_layerObservable_gaussianFun' hμ φ)
  refine (h0.const_mul (∫ y, ‖layerWeight b φ y‖ ∂m)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have hb := hL.norm_gaussFourier_layerObservable_gaussianFun_le hQ hμ φ ξ
  have harg : -(1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ * ⟪Q ξ, ξ⟫ / 2 =
      -((1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ / 2) * ⟪Q ξ, ξ⟫ := by ring
  rwa [harg] at hb

end RayRegular

end OperatorRidgelet
