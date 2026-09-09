import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Reconstruction.Representation
import OperatorRidgelet.Transform.BiasFourier

/-!
# Backprojection: the ray average of a bias-Fourier representative (Appendix B.4)

Ridgelet-specific lemmas behind Theorem `thm:C`(iv)(a)–(b) and Proposition
`prop:coefficient-projection`(i)–(vi), for the abstract pair `(μ, ν)` of Appendix H.

* **The ray substitution.**  `raySubst (ξ, ω) = (-ξ/ω, ω)` inverts `(a, ω) ↦ (-ωa, ω)`; by
  homogeneity it maps the weighted measure `|ω|^{-α} (ν ⊗ dω)` to `ν ⊗ dω`
  (`IsHomogeneous.map_raySubst_withDensity`, the manuscript's `eq:homogeneous-change`), so it
  preserves null sets and transforms lower Lebesgue and Bochner integrals with the weight
  `|ω|^{-α}` (`IsHomogeneous.lintegral_raySubst`, `IsHomogeneous.integral_raySubst`).
* **Absolute convergence and the bound.**  For a jointly measurable representative `Φ` of
  `γ ∈ L²(λ)` the weighted ray energy `rayEnergy α Φ ξ = ∫ |ω|^{-α} ‖Φ(-ξ/ω, ω)‖² dω` integrates
  over `ξ` to `2π ‖γ‖²` (ray substitution and Plancherel along rays), so it is finite for
  almost every `ξ`; weighted Cauchy–Schwarz then gives the absolute convergence of the ray
  average and `‖Λ_ρ Φ(ξ)‖² ≤ (2π)⁻¹ C rayEnergy α Φ ξ`, hence `‖Λ_ρ γ‖² ≤ C ‖γ‖²`.
* **Independence of the representative.**  Two representatives agree almost everywhere on
  almost every ray, hence on a `ν ⊗ dω`-full set, whose image under the ray substitution is
  again full; the ray averages agree `ν`-almost everywhere.
* **Adjointness and `Λ_ρ W_ρ = C`.**  Parseval along rays turns `⟨γ, W_ρ F⟩_{L²(λ)}` into the
  pairing of the representatives, the ray substitution turns it into
  `⟨Λ_ρ γ, F⟩_{L²(ν)}`; on the representative `ρ̂(ω) F(-ωa)` of `W_ρ F` the ray average is
  `C F(ξ)` pointwise.
* **The projection.**  `Π_ρ = C⁻¹ W_ρ P_𝒦 Λ_ρ` maps into `Ran R_ρ = W_ρ(𝒦)`, and
  `γ - Π_ρ γ ⊥ R_ρ g` for `g ∈ 𝒦` by adjointness, `Λ_ρ W_ρ = C`, and the self-adjointness of
  `P_𝒦`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### Auxiliary real identities -/

section Aux

/-- The enorm of a nonnegative real number as a complex number. -/
theorem enorm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

/-- `|ω|^{-α} |-ω⁻¹|^{-α} = 1` for `ω ≠ 0`. -/
theorem ofReal_rpow_neg_mul_ofReal_rpow_neg_inv {ω α : ℝ} (hω : ω ≠ 0) :
    ENNReal.ofReal (|ω| ^ (-α)) * ENNReal.ofReal (|-ω⁻¹| ^ (-α)) = 1 := by
  rw [abs_neg, abs_inv, Real.inv_rpow (abs_nonneg ω),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
    mul_inv_cancel₀ (Real.rpow_pos_of_pos (abs_pos.mpr hω) _).ne', ENNReal.ofReal_one]

/-- `|ω|^{-α}` is the square of `|ω|^{-α/2}`. -/
theorem rpow_neg_eq_sq {ω : ℝ} (α : ℝ) : |ω| ^ (-α) = (|ω| ^ (-α / 2)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  norm_num

end Aux

/-! ### The ray substitution -/

section RaySubst

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The ray substitution `(ξ, ω) ↦ (-ξ/ω, ω)`, the inverse of `(a, ω) ↦ (-ωa, ω)` for
`ω ≠ 0`. -/
def raySubst (p : H × ℝ) : H × ℝ :=
  (-(p.2⁻¹ • p.1), p.2)

theorem measurable_raySubst : Measurable (raySubst : H × ℝ → H × ℝ) :=
  (measurable_snd.inv.smul measurable_fst).neg.prodMk measurable_snd

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] in
/-- The weight `|ω|^{-α}` of the ray substitution is measurable. -/
theorem measurable_rayWeight (α : ℝ) :
    Measurable fun p : H × ℝ => ENNReal.ofReal (|p.2| ^ (-α)) :=
  ((continuous_abs.measurable.comp measurable_snd).pow_const (-α)).ennreal_ofReal

variable {α : ℝ} {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν)
include hν

/-- **The ray substitution and homogeneity** (`eq:homogeneous-change`): the image of the
weighted measure `|ω|^{-α} (ν ⊗ dω)` under `(ξ, ω) ↦ (-ξ/ω, ω)` is `ν ⊗ dω`. -/
theorem IsHomogeneous.map_raySubst_withDensity :
    Measure.map raySubst ((ν.prod volume).withDensity fun p => ENNReal.ofReal (|p.2| ^ (-α))) =
      ν.prod volume := by
  have hw := measurable_rayWeight (H := H) α
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_raySubst hs, withDensity_apply _ (measurable_raySubst hs),
    ← lintegral_indicator (measurable_raySubst hs)]
  have hind : ∀ p : H × ℝ,
      (raySubst ⁻¹' s).indicator (fun p : H × ℝ => ENNReal.ofReal (|p.2| ^ (-α))) p =
        ENNReal.ofReal (|p.2| ^ (-α)) * s.indicator 1 (raySubst p) := by
    intro p
    by_cases hp : raySubst p ∈ s
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ raySubst ⁻¹' s from hp)]
    · simp [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ raySubst ⁻¹' s from hp)]
  simp_rw [hind]
  have hK : Measurable fun p : H × ℝ => (s.indicator 1 p : ℝ≥0∞) := measurable_one.indicator hs
  rw [lintegral_prod_symm' (fun p : H × ℝ => ENNReal.ofReal (|p.2| ^ (-α)) *
    s.indicator 1 (raySubst p)) (hw.mul (hK.comp measurable_raySubst)),
    ← lintegral_indicator_one hs, lintegral_prod_symm' _ hK]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  refine lintegral_congr_ae ?_
  filter_upwards [h0] with ω hω
  have hKω : Measurable fun a : H => (s.indicator 1 (a, ω) : ℝ≥0∞) :=
    hK.comp (measurable_id.prodMk measurable_const)
  simp only [raySubst]
  have hsmul : ∀ ξ : H, -(ω⁻¹ • ξ) = (-ω⁻¹) • ξ := fun ξ => (neg_smul _ _).symm
  simp_rw [hsmul]
  calc ∫⁻ x, ENNReal.ofReal (|ω| ^ (-α)) * s.indicator 1 ((-ω⁻¹) • x, ω) ∂ν
      = ENNReal.ofReal (|ω| ^ (-α)) * ∫⁻ x, s.indicator 1 ((-ω⁻¹) • x, ω) ∂ν :=
        lintegral_const_mul _ (f := fun x : H => (s.indicator 1 ((-ω⁻¹) • x, ω) : ℝ≥0∞))
          (hKω.comp (measurable_const_smul (-ω⁻¹)))
    _ = ENNReal.ofReal (|ω| ^ (-α)) *
          (ENNReal.ofReal (|-ω⁻¹| ^ (-α)) * ∫⁻ x, s.indicator 1 (x, ω) ∂ν) := by
        rw [hν.lintegral_smul (neg_ne_zero.mpr (inv_ne_zero hω)) hKω]
    _ = ∫⁻ x, s.indicator 1 (x, ω) ∂ν := by
        rw [← mul_assoc, ofReal_rpow_neg_mul_ofReal_rpow_neg_inv hω, one_mul]

/-- The lower Lebesgue integral under the ray substitution:
`∫⁻ |ω|^{-α} K(-ξ/ω, ω) d(ν ⊗ dω)(ξ, ω) = ∫⁻ K d(ν ⊗ dω)`. -/
theorem IsHomogeneous.lintegral_raySubst {K : H × ℝ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p, ENNReal.ofReal (|p.2| ^ (-α)) * K (raySubst p) ∂ν.prod volume =
      ∫⁻ p, K p ∂ν.prod volume := by
  conv_rhs => rw [← hν.map_raySubst_withDensity]
  rw [lintegral_map hK measurable_raySubst,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_rayWeight α)
      (g := fun p => K (raySubst p)) (hK.comp measurable_raySubst)]
  rfl

/-- The ray substitution preserves `ν ⊗ dω`-null sets. -/
theorem IsHomogeneous.quasiMeasurePreserving_raySubst :
    Measure.QuasiMeasurePreserving raySubst (ν.prod volume) (ν.prod volume) := by
  refine ⟨measurable_raySubst, ?_⟩
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have hne : ∀ᵐ p ∂ν.prod volume, ENNReal.ofReal (|p.2| ^ (-α)) ≠ 0 := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h0] with p hp
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hp) _)).ne'
  have hac : ν.prod volume ≪
      (ν.prod volume).withDensity fun p => ENNReal.ofReal (|p.2| ^ (-α)) := by
    intro s hs
    rw [withDensity_apply_eq_zero' (measurable_rayWeight α).aemeasurable] at hs
    have hsub : s ⊆ ({p : H × ℝ | ENNReal.ofReal (|p.2| ^ (-α)) ≠ 0} ∩ s) ∪
        {p : H × ℝ | ¬ ENNReal.ofReal (|p.2| ^ (-α)) ≠ 0} := fun p hp => by
      by_cases h : ENNReal.ofReal (|p.2| ^ (-α)) ≠ 0
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr h
    exact measure_mono_null hsub (measure_union_null hs (ae_iff.mp hne))
  have := hac.map measurable_raySubst
  rwa [hν.map_raySubst_withDensity] at this

/-- The Bochner integral under the ray substitution:
`∫ |ω|^{-α} K(-ξ/ω, ω) d(ν ⊗ dω)(ξ, ω) = ∫ K d(ν ⊗ dω)`. -/
theorem IsHomogeneous.integral_raySubst {K : H × ℝ → ℂ}
    (hK : AEStronglyMeasurable K (ν.prod volume)) :
    ∫ p, ((|p.2| ^ (-α) : ℝ) : ℂ) * K (raySubst p) ∂ν.prod volume = ∫ p, K p ∂ν.prod volume := by
  conv_rhs => rw [← hν.map_raySubst_withDensity]
  rw [integral_map measurable_raySubst.aemeasurable (by rwa [hν.map_raySubst_withDensity])]
  have hden : ((ν.prod volume).withDensity fun p => ENNReal.ofReal (|p.2| ^ (-α))) =
      (ν.prod volume).withDensity fun p => ((|p.2| ^ (-α)).toNNReal : ℝ≥0∞) := rfl
  rw [hden, integral_withDensity_eq_integral_smul (f := fun p : H × ℝ => (|p.2| ^ (-α)).toNNReal)
    ((continuous_abs.measurable.comp measurable_snd).pow_const (-α)).real_toNNReal
    (fun p => K (raySubst p))]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg (abs_nonneg _) _), Complex.real_smul]

/-- Integrability under the ray substitution. -/
theorem IsHomogeneous.integrable_raySubst {K : H × ℝ → ℂ} (hK : Measurable K)
    (hint : Integrable K (ν.prod volume)) :
    Integrable (fun p => ((|p.2| ^ (-α) : ℝ) : ℂ) * K (raySubst p)) (ν.prod volume) := by
  refine ⟨((Complex.measurable_ofReal.comp ((continuous_abs.measurable.comp
    measurable_snd).pow_const (-α))).mul (hK.comp measurable_raySubst)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖((|p.2| ^ (-α) : ℝ) : ℂ) * K (raySubst p)‖ₑ ∂ν.prod volume
      = ∫⁻ p, ENNReal.ofReal (|p.2| ^ (-α)) * ‖K (raySubst p)‖ₑ ∂ν.prod volume := by
        refine lintegral_congr fun p => ?_
        rw [enorm_mul, enorm_ofReal_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    _ = ∫⁻ p, ‖K p‖ₑ ∂ν.prod volume := hν.lintegral_raySubst hK.enorm
    _ < ⊤ := hasFiniteIntegral_iff_enorm.mp hint.2

end RaySubst

/-! ### The ray average of a jointly measurable representative -/

section RayAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- The integrand of the ray average `eq:ray-average` is jointly measurable. -/
theorem measurable_backprojection_integrand (α : ℝ) (ρ : SchwartzMap ℝ ℝ) {Φ : H → ℝ → ℂ}
    (hΦ : Measurable (Function.uncurry Φ)) :
    Measurable fun p : H × ℝ => (starRingEnd ℂ) (filterFourier ρ p.2) *
      ((|p.2| ^ (-α) : ℝ) : ℂ) * Φ (-(p.2⁻¹ • p.1)) p.2 :=
  (((Complex.continuous_conj.comp (continuous_filterFourier ρ)).measurable.comp
    measurable_snd).mul (Complex.measurable_ofReal.comp
      ((continuous_abs.measurable.comp measurable_snd).pow_const (-α)))).mul
    (hΦ.comp measurable_raySubst)

/-- The ray average of a jointly measurable representative is measurable. -/
theorem measurable_backprojectionOf (α : ℝ) (ρ : SchwartzMap ℝ ℝ) {Φ : H → ℝ → ℂ}
    (hΦ : Measurable (Function.uncurry Φ)) : Measurable (backprojectionOf α ρ Φ) := by
  unfold backprojectionOf
  exact measurable_const.mul
    (measurable_backprojection_integrand α ρ hΦ).stronglyMeasurable.integral_prod_right'.measurable

/-- The representative `ρ̂(ω) F(-ωa)` of `W_ρ F` is jointly measurable. -/
theorem measurable_coefficient_representative {ρ : SchwartzMap ℝ ℝ} {F : H → ℂ}
    (hF : Measurable F) :
    Measurable (Function.uncurry fun a ω => filterFourier ρ ω * F (-(ω • a))) :=
  ((continuous_filterFourier ρ).measurable.comp measurable_snd).mul
    (hF.comp (by fun_prop : Continuous fun p : H × ℝ => -(p.2 • p.1)).measurable)

omit [MeasurableSpace H] [BorelSpace H] in
/-- The ray average of the representative `ρ̂(ω) F(-ωa)` of `W_ρ F` is `C^{(α)}_ρ F(ξ)`,
pointwise in `ξ`. -/
theorem backprojectionOf_coefficient_representative (α : ℝ) (ρ : SchwartzMap ℝ ℝ) (F : H → ℂ)
    (ξ : H) :
    backprojectionOf α ρ (fun a ω => filterFourier ρ ω * F (-(ω • a))) ξ =
      admissibilityConst α ρ * F ξ := by
  unfold backprojectionOf admissibilityConst
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  rw [Complex.ofReal_mul, mul_assoc]
  congr 1
  calc ∫ ω, (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) *
        (fun a ω => filterFourier ρ ω * F (-(ω • a))) (-(ω⁻¹ • ξ)) ω
      = ∫ ω, ((‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ) * F ξ := by
        refine integral_congr_ae ?_
        filter_upwards [h0] with ω hω
        have hξ : -(ω • -(ω⁻¹ • ξ)) = ξ := by
          rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
        simp only [hξ]
        rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        ring
    _ = (∫ ω, ((‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ)) * F ξ := integral_mul_const _ _
    _ = ((∫ ω, ‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ) * F ξ := by
        congr 1
        exact integral_ofReal

/-- The weighted ray energy `∫ |ω|^{-α} ‖Φ(-ξ/ω, ω)‖² dω` of a representative at `ξ`. -/
def rayEnergy (α : ℝ) (Φ : H → ℝ → ℂ) (ξ : H) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|ω| ^ (-α)) * ‖Φ (-(ω⁻¹ • ξ)) ω‖ₑ ^ 2

theorem measurable_rayEnergy (α : ℝ) {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) :
    Measurable (rayEnergy α Φ) :=
  ((measurable_rayWeight α).mul ((hΦ.comp measurable_raySubst).enorm.pow_const 2)).lintegral_prod_right'

variable {α : ℝ} {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν)
include hν

/-- The ray energy integrates to the squared `L²(ν ⊗ dω)` norm of the representative. -/
theorem IsHomogeneous.lintegral_rayEnergy {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ξ, rayEnergy α Φ ξ ∂ν = ∫⁻ p, ‖Function.uncurry Φ p‖ₑ ^ 2 ∂ν.prod volume := by
  unfold rayEnergy
  rw [← hν.lintegral_raySubst (hΦ.enorm.pow_const 2), lintegral_prod
    (fun p : H × ℝ => ENNReal.ofReal (|p.2| ^ (-α)) * ‖Function.uncurry Φ (raySubst p)‖ₑ ^ 2)
    ((measurable_rayWeight α).mul ((hΦ.comp measurable_raySubst).enorm.pow_const 2)).aemeasurable]
  rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] hν in
/-- Plancherel on `H × ℝ` for a jointly measurable representative of `γ ∈ L²(ν ⊗ dc)`:
`∫⁻ ‖Φ‖ₑ² d(ν ⊗ dω) = 2π ∫⁻ ‖γ‖ₑ² d(ν ⊗ dc)`. -/
theorem HasBiasFourier.lintegral_uncurry_enorm_sq {γ : H × ℝ → ℂ}
    (hγ : MemLp γ 2 (ν.prod volume)) {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    (h : HasBiasFourier ν γ Φ) :
    ∫⁻ p, ‖Function.uncurry Φ p‖ₑ ^ 2 ∂ν.prod volume =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂ν.prod volume := by
  rw [lintegral_prod _ (hΦ.enorm.pow_const 2).aemeasurable,
    lintegral_prod _ (hγ.1.enorm.pow_const 2), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr_ae (h.lintegral_enorm_sq_ae hγ)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H] hν in
/-- A jointly measurable representative of `γ ∈ L²(ν ⊗ dc)` is in `L²(ν ⊗ dω)`. -/
theorem HasBiasFourier.memLp_uncurry {γ : H × ℝ → ℂ} (hγ : MemLp γ 2 (ν.prod volume))
    {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) (h : HasBiasFourier ν γ Φ) :
    MemLp (Function.uncurry Φ) 2 (ν.prod volume) :=
  memLp_two_of_lintegral_enorm_sq_lt_top hΦ.aestronglyMeasurable (by
    rw [h.lintegral_uncurry_enorm_sq hγ hΦ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγ.lintegral_enorm_sq_lt_top)

/-- The ray energy of a representative of `γ ∈ L²(ν ⊗ dc)` is finite for `ν`-almost every
`ξ`. -/
theorem HasBiasFourier.ae_rayEnergy_lt_top {γ : H × ℝ → ℂ} (hγ : MemLp γ 2 (ν.prod volume))
    {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) (h : HasBiasFourier ν γ Φ) :
    ∀ᵐ ξ ∂ν, rayEnergy α Φ ξ < ⊤ :=
  ae_lt_top (measurable_rayEnergy α hΦ) (by
    rw [hν.lintegral_rayEnergy hΦ, h.lintegral_uncurry_enorm_sq hγ hΦ]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγ.lintegral_enorm_sq_lt_top).ne)

omit hν in
/-- **Absolute convergence of the ray average** at every `ξ` with finite ray energy: weighted
Cauchy–Schwarz against the admissibility integral. -/
theorem integrable_backprojection_integrand {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
    {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) {ξ : H}
    (hξ : rayEnergy α Φ ξ < ⊤) :
    Integrable fun ω : ℝ =>
      (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) * Φ (-(ω⁻¹ • ξ)) ω := by
  have hΦm : Measurable fun ω : ℝ => Φ (-(ω⁻¹ • ξ)) ω :=
    hΦ.comp (measurable_raySubst.comp (measurable_const.prodMk measurable_id))
  have hmeas : Measurable fun ω : ℝ =>
      (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) * Φ (-(ω⁻¹ • ξ)) ω :=
    ((Complex.continuous_conj.comp (continuous_filterFourier ρ)).measurable.mul
      (Complex.measurable_ofReal.comp (continuous_abs.measurable.pow_const (-α)))).mul hΦm
  have h2 : Integrable fun ω : ℝ => |ω| ^ (-α) * ‖Φ (-(ω⁻¹ • ξ)) ω‖ ^ 2 := by
    refine ⟨((continuous_abs.measurable.pow_const (-α)).mul
      (hΦm.norm.pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) hξ
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  refine Integrable.mono' (hρ.integrable.add h2) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hw : 0 ≤ |ω| ^ (-α) := Real.rpow_nonneg (abs_nonneg _) _
  nlinarith [mul_nonneg hw (sq_nonneg (‖filterFourier ρ ω‖ - ‖Φ (-(ω⁻¹ • ξ)) ω‖)),
    mul_nonneg (mul_nonneg (norm_nonneg (filterFourier ρ ω)) hw) (norm_nonneg (Φ (-(ω⁻¹ • ξ)) ω))]

omit hν in
/-- **The bound on the ray average**: `‖Λ_ρ Φ(ξ)‖² ≤ (2π)⁻¹ C_ρ · rayEnergy α Φ ξ` (weighted
Cauchy–Schwarz). -/
theorem enorm_backprojectionOf_sq_le {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
    {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ)) (ξ : H) :
    ‖backprojectionOf α ρ Φ ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergy α Φ ξ := by
  set f : ℝ → ℂ := fun ω => filterFourier ρ ω * ((|ω| ^ (-α / 2) : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun ω => ((|ω| ^ (-α / 2) : ℝ) : ℂ) * Φ (-(ω⁻¹ • ξ)) ω with hg
  have hΦm : Measurable fun ω : ℝ => Φ (-(ω⁻¹ • ξ)) ω :=
    hΦ.comp (measurable_raySubst.comp (measurable_const.prodMk measurable_id))
  have hwm : Measurable fun ω : ℝ => ((|ω| ^ (-α / 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (continuous_abs.measurable.pow_const _)
  have hfm : AEMeasurable f volume := ((continuous_filterFourier ρ).measurable.mul hwm).aemeasurable
  have hgm : AEMeasurable g volume := (hwm.mul hΦm).aemeasurable
  have hw : ∀ ω : ℝ, ‖((|ω| ^ (-α / 2) : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (|ω| ^ (-α)) := by
    intro ω
    rw [enorm_ofReal_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← ENNReal.ofReal_pow
      (Real.rpow_nonneg (abs_nonneg _) _), rpow_neg_eq_sq]
  have hpt : ∀ ω, ‖(starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) *
      Φ (-(ω⁻¹ • ξ)) ω‖ₑ = ‖f ω‖ₑ * ‖g ω‖ₑ := by
    intro ω
    simp only [hf, hg, enorm_mul, RCLike.enorm_conj]
    rw [enorm_ofReal_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← hw ω, sq]
    ring
  have hf2 : ∫⁻ ω, ‖f ω‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi * admissibilityConst α ρ) := by
    rw [← hρ.lintegral_enorm_sq_mul]
    refine lintegral_congr fun ω => ?_
    simp only [hf, enorm_mul, mul_pow, hw]
  have hg2 : ∫⁻ ω, ‖g ω‖ₑ ^ 2 = rayEnergy α Φ ξ := by
    unfold rayEnergy
    refine lintegral_congr fun ω => ?_
    simp only [hg, enorm_mul, mul_pow, hw]
  have hCS := lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two volume hfm hgm
  have h1 : ‖backprojectionOf α ρ Φ ξ‖ₑ ≤
      ENNReal.ofReal (2 * Real.pi)⁻¹ * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by
    unfold backprojectionOf
    rw [enorm_mul, enorm_ofReal_of_nonneg (by positivity)]
    refine mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans ?_)
    simp_rw [hpt]
    exact hCS
  calc ‖backprojectionOf α ρ Φ ξ‖ₑ ^ 2
      ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ * (eLpNorm f 2 volume * eLpNorm g 2 volume)) ^ 2 :=
        ENNReal.pow_le_pow_left h1
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 2 * ((∫⁻ ω, ‖f ω‖ₑ ^ 2) * ∫⁻ ω, ‖g ω‖ₑ ^ 2) := by
        rw [mul_pow, mul_pow, eLpNorm_two_sq_eq_lintegral_enorm_sq',
          eLpNorm_two_sq_eq_lintegral_enorm_sq']
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergy α Φ ξ := by
        rw [hf2, hg2, ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

end RayAverage

/-! ### The backprojection on `L²(λ)` -/

section Backprojection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {α : ℝ} {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν)

omit [BorelSpace H] hν in
/-- The backprojection of `γ ∈ L²(λ)` is the ray average of a jointly measurable representative
of `γ` (the junk value is never taken on `L²(λ)`). -/
theorem backprojection_eq_backprojectionOf (α : ℝ) (ρ : ℝ → ℝ) {γ : H × ℝ → ℂ}
    (hγ : MemLp γ 2 (parameterMeasure ν)) :
    ∃ Φ : H → ℝ → ℂ, Measurable (Function.uncurry Φ) ∧ HasBiasFourier ν γ Φ ∧
      backprojection α ν ρ γ = backprojectionOf α ρ Φ := by
  set γ' := hγ.1.mk γ with hγ'
  have hγ'm : Measurable γ' := hγ.1.stronglyMeasurable_mk.measurable
  have hγ'e : γ =ᵐ[ν.prod volume] γ' := hγ.1.ae_eq_mk
  obtain ⟨Φ, hΦ, hγΦ⟩ := exists_measurable_hasBiasFourier hγ'm (hγ.ae_eq hγ'e)
  have hex : ∃ Φ : H → ℝ → ℂ, Measurable (Function.uncurry Φ) ∧ HasBiasFourier ν γ Φ :=
    ⟨Φ, hΦ, hγΦ.congr_left hγ'e.symm⟩
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold backprojection
  rw [dif_pos hex]

include hν

/-- **Independence of the representative**: the ray averages of two jointly measurable
bias-Fourier representatives of the same coefficient agree `ν`-almost everywhere. -/
theorem IsHomogeneous.backprojectionOf_ae_eq (ρ : ℝ → ℝ) {γ : H × ℝ → ℂ} {Φ Φ' : H → ℝ → ℂ}
    (hΦ : Measurable (Function.uncurry Φ)) (hΦ' : Measurable (Function.uncurry Φ'))
    (h : HasBiasFourier ν γ Φ) (h' : HasBiasFourier ν γ Φ') :
    backprojectionOf α ρ Φ =ᵐ[ν] backprojectionOf α ρ Φ' := by
  have hae : Function.uncurry Φ =ᵐ[ν.prod volume] Function.uncurry Φ' :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hΦ hΦ')).mpr (h.ae_ae_eq h')
  have hae' := hν.quasiMeasurePreserving_raySubst.ae_eq_comp hae
  filter_upwards [Measure.ae_ae_of_ae_prod hae'] with ξ hξ
  unfold backprojectionOf
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hξ] with ω hω
  simp only [Function.comp_apply] at hω
  exact congrArg _ hω

variable (hα : 0 < α) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hα hρ

omit hα in
/-- **Boundedness of the backprojection**: for `γ ∈ L²(λ)`, `Λ_ρ γ ∈ L²(ν)` with
`∫ ‖Λ_ρ γ‖² dν ≤ C^{(α)}_ρ ‖γ‖²` (Proposition `prop:coefficient-projection`(iii)). -/
theorem IsHomogeneous.memLp_backprojection (γ : Lp ℂ 2 (parameterMeasure ν)) :
    MemLp (backprojection α ν ρ γ) 2 ν ∧
      ∫ ξ, ‖backprojection α ν ρ γ ξ‖ ^ 2 ∂ν ≤ admissibilityConst α ρ * ‖γ‖ ^ 2 := by
  obtain ⟨Φ, hΦ, hγΦ, hΛ⟩ := backprojection_eq_backprojectionOf (ν := ν) α ρ (Lp.memLp γ)
  rw [hΛ]
  have hmeas := measurable_backprojectionOf α ρ hΦ
  have hlin : ∫⁻ ξ, ‖backprojectionOf α ρ Φ ξ‖ₑ ^ 2 ∂ν ≤
      ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν := by
    calc ∫⁻ ξ, ‖backprojectionOf α ρ Φ ξ‖ₑ ^ 2 ∂ν
        ≤ ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) * rayEnergy α Φ ξ ∂ν :=
          lintegral_mono fun ξ => enorm_backprojectionOf_sq_le hρ hΦ ξ
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * admissibilityConst α ρ) *
            (ENNReal.ofReal (2 * Real.pi) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν) := by
          rw [lintegral_const_mul _ (measurable_rayEnergy α hΦ), hν.lintegral_rayEnergy hΦ,
            hγΦ.lintegral_uncurry_enorm_sq (Lp.memLp γ) hΦ]
          rfl
      _ = ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hρ.pos.le)]
          congr 2
          field_simp
  have hfin : ENNReal.ofReal (admissibilityConst α ρ) * ∫⁻ p, ‖γ p‖ₑ ^ 2 ∂parameterMeasure ν ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp γ).lintegral_enorm_sq_lt_top).ne
  refine ⟨memLp_two_of_lintegral_enorm_sq_lt_top hmeas.aestronglyMeasurable
    (hlin.trans_lt hfin.lt_top), ?_⟩
  rw [integral_norm_sq_eq_toReal_lintegral' hmeas.aestronglyMeasurable,
    Lp.norm_sq_eq_integral_norm_sq, integral_norm_sq_eq_toReal_lintegral'
    (Lp.aestronglyMeasurable γ), ← ENNReal.toReal_ofReal hρ.pos.le, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin hlin

/-- **`Λ_ρ W_ρ = C^{(α)}_ρ Id`** on measurable `F ∈ L²(ν)` (Theorem `thm:C`(iv)(b),
Proposition `prop:coefficient-projection`(v)). -/
theorem IsHomogeneous.backprojection_spectralCoefficient {F : H → ℂ} (hF : Measurable F)
    (hF₂ : MemLp F 2 ν) :
    backprojection α ν ρ (spectralCoefficient ν ρ F) =ᵐ[ν]
      fun ξ => admissibilityConst α ρ * F ξ := by
  obtain ⟨Φ, hΦ, hγΦ, hΛ⟩ :=
    backprojection_eq_backprojectionOf (ν := ν) α ρ (Lp.memLp (spectralCoefficient ν ρ F))
  rw [hΛ]
  have hΘ : HasBiasFourier ν (spectralCoefficient ν ρ F)
      (fun a ω => filterFourier ρ ω * F (-(ω • a))) :=
    (hasBiasFourier_coefficientFormula hα hν hρ hF hF₂).congr_left (by
      rw [spectralCoefficient_eq_toLp hν hα hρ hF hF₂]
      exact (MemLp.coeFn_toLp _).symm)
  filter_upwards [hν.backprojectionOf_ae_eq ρ hΦ (measurable_coefficient_representative hF) hγΦ hΘ]
    with ξ hξ
  rw [hξ, backprojectionOf_coefficient_representative]

/-- **Adjointness for a representative**: for a jointly measurable representative `Φ` of a
measurable `γ ∈ L²(λ)` and measurable `F ∈ L²(ν)`,
`∫ γ conj(γ_F) dλ = ∫ Λ_ρ Φ conj(F) dν`, by Parseval along rays, the ray substitution, and
Fubini. -/
theorem IsHomogeneous.integral_mul_conj_coefficientFormula {γ : H × ℝ → ℂ}
    (hγ : MemLp γ 2 (ν.prod volume)) {Φ : H → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    (h : HasBiasFourier ν γ Φ) {F : H → ℂ} (hF : Measurable F) (hF₂ : MemLp F 2 ν) :
    ∫ p, γ p * (starRingEnd ℂ) (coefficientFormula ρ F p) ∂ν.prod volume =
      ∫ ξ, backprojectionOf α ρ Φ ξ * (starRingEnd ℂ) (F ξ) ∂ν := by
  set Θ : H → ℝ → ℂ := fun a ω => filterFourier ρ ω * F (-(ω • a)) with hΘdef
  have hΘm : Measurable (Function.uncurry Θ) := measurable_coefficient_representative hF
  have hfin := hρ.lintegral_prod_enorm_sq_lt_top hν hF hF₂
  have hΘ₂ : MemLp (Function.uncurry Θ) 2 (ν.prod volume) :=
    memLp_two_of_lintegral_enorm_sq_lt_top hΘm.aestronglyMeasurable (by
      simpa only [Function.uncurry_def, hΘdef, enorm_mul, mul_pow] using hfin)
  have hΦ₂ : MemLp (Function.uncurry Φ) 2 (ν.prod volume) := h.memLp_uncurry hγ hΦ
  have hγF : HasBiasFourier ν (coefficientFormula ρ F) Θ :=
    hasBiasFourier_coefficientFormula hα hν hρ hF hF₂
  have hcF : MemLp (coefficientFormula ρ F) 2 (ν.prod volume) :=
    memLp_coefficientFormula hα hν hρ hF hF₂
  have hK : Measurable fun p => Function.uncurry Φ p * (starRingEnd ℂ) (Function.uncurry Θ p) :=
    hΦ.mul (Complex.continuous_conj.measurable.comp hΘm)
  have hKint : Integrable (fun p => Function.uncurry Φ p * (starRingEnd ℂ) (Function.uncurry Θ p))
      (ν.prod volume) := hΦ₂.integrable_mul_conj hΘ₂
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have hω0 : ∀ᵐ p ∂ν.prod (volume : Measure ℝ), p.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae h0
  calc ∫ p, γ p * (starRingEnd ℂ) (coefficientFormula ρ F p) ∂ν.prod volume
      = ∫ a, (∫ c, γ (a, c) * (starRingEnd ℂ) (coefficientFormula ρ F (a, c))) ∂ν :=
        integral_prod _ (hγ.integrable_mul_conj hcF)
    _ = ∫ a, (((2 * Real.pi)⁻¹ : ℝ) * ∫ ω, Φ a ω * (starRingEnd ℂ) (Θ a ω)) ∂ν :=
        integral_congr_ae (h.integral_mul_conj_ae hγ hcF hγF)
    _ = ((2 * Real.pi)⁻¹ : ℝ) *
          ∫ p, Function.uncurry Φ p * (starRingEnd ℂ) (Function.uncurry Θ p) ∂ν.prod volume := by
        rw [integral_const_mul, integral_prod _ hKint]
        rfl
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ p, ((|p.2| ^ (-α) : ℝ) : ℂ) *
          (Function.uncurry Φ (raySubst p) * (starRingEnd ℂ) (Function.uncurry Θ (raySubst p)))
            ∂ν.prod volume := by
        rw [hν.integral_raySubst hKint.1]
    _ = ∫ ξ, backprojectionOf α ρ Φ ξ * (starRingEnd ℂ) (F ξ) ∂ν := by
        rw [← integral_const_mul, integral_prod _ ((hν.integrable_raySubst hK hKint).const_mul _)]
        refine integral_congr_ae ?_
        filter_upwards [Measure.ae_ae_of_ae_prod hω0] with ξ hξ
        unfold backprojectionOf
        rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hξ] with ω hω
        have hξω : -(ω • -(ω⁻¹ • ξ)) = ξ := by
          rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
        simp only [hΘdef, Function.uncurry_apply_pair, raySubst, hξω, map_mul]
        ring

/-- **`Λ_ρ` is the adjoint of `W_ρ`** (Proposition `prop:coefficient-projection`(iv)):
`⟨γ, W_ρ F⟩_{L²(λ)} = ⟨Λ_ρ γ, F⟩_{L²(ν)}` in the manuscript's convention. -/
theorem IsHomogeneous.integral_mul_conj_spectralCoefficient (γ : Lp ℂ 2 (parameterMeasure ν))
    {F : H → ℂ} (hF : Measurable F) (hF₂ : MemLp F 2 ν) :
    ∫ p, γ p * (starRingEnd ℂ) ((spectralCoefficient ν ρ F : H × ℝ → ℂ) p) ∂parameterMeasure ν =
      ∫ ξ, backprojection α ν ρ γ ξ * (starRingEnd ℂ) (F ξ) ∂ν := by
  obtain ⟨Φ, hΦ, hγΦ, hΛ⟩ := backprojection_eq_backprojectionOf (ν := ν) α ρ (Lp.memLp γ)
  rw [hΛ]
  set γ' := (Lp.aestronglyMeasurable γ).mk γ with hγ'
  have hγ'e : (γ : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] γ' := (Lp.aestronglyMeasurable γ).ae_eq_mk
  have hγ'₂ : MemLp γ' 2 (parameterMeasure ν) := (Lp.memLp γ).ae_eq hγ'e
  have hcoef : (spectralCoefficient ν ρ F : H × ℝ → ℂ) =ᵐ[parameterMeasure ν]
      coefficientFormula ρ F := by
    rw [spectralCoefficient_eq_toLp hν hα hρ hF hF₂]
    exact MemLp.coeFn_toLp _
  calc ∫ p, γ p * (starRingEnd ℂ) ((spectralCoefficient ν ρ F : H × ℝ → ℂ) p) ∂parameterMeasure ν
      = ∫ p, γ' p * (starRingEnd ℂ) (coefficientFormula ρ F p) ∂ν.prod volume := by
        refine integral_congr_ae ?_
        filter_upwards [hγ'e, hcoef] with p h1 h2
        rw [h1, h2]
    _ = _ := hν.integral_mul_conj_coefficientFormula hα hρ hγ'₂ hΦ (hγΦ.congr_left hγ'e) hF hF₂

/-- **The coefficient projection** `Π_ρ = C⁻¹ W_ρ P_𝒦 Λ_ρ` is the orthogonal projection onto
`Ran R_ρ` (Proposition `prop:coefficient-projection`(vi)): `Π_ρ γ ∈ Ran R_ρ` and
`γ - Π_ρ γ ⊥ Ran R_ρ`. -/
theorem IsHomogeneous.coefficientProjection_mem_and_sub_mem_orthogonal (μ : Measure H)
    [IsProbabilityMeasure μ] (γ : Lp ℂ 2 (parameterMeasure ν)) :
    coefficientProjection α μ ν ρ γ ∈ ridgeletRange μ ν ρ ∧
      γ - coefficientProjection α μ ν ρ γ ∈ (ridgeletRange μ ν ρ)ᗮ := by
  have hC : (admissibilityConst α ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.pos.ne'
  set Λ := backprojectionLp α ν ρ γ with hΛdef
  have hmem := (hν.memLp_backprojection hρ γ).1
  have hΛcoe : (Λ : H → ℂ) =ᵐ[ν] backprojection α ν ρ γ := by
    rw [hΛdef]
    unfold backprojectionLp
    rw [dif_pos hmem]
    exact hmem.coeFn_toLp
  set P : Lp ℂ 2 ν := (spectralRange μ ν).starProjection Λ with hPdef
  have hPmem : P ∈ spectralRange μ ν := (spectralRange μ ν).starProjection_apply_mem Λ
  have hW : ∀ u : spectralRange μ ν,
      ridgeletExtension μ ν ρ u = spectralCoefficient ν ρ ((u : Lp ℂ 2 ν) : H → ℂ) := fun u => by
    rw [ridgeletExtension_eq hν hρ, ridgeletExtensionCLM_eq_spectralCoefficient hν hα hρ μ u]
  have hProj : coefficientProjection α μ ν ρ γ =
      (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • ridgeletExtension μ ν ρ ⟨P, hPmem⟩ := by
    rw [hW ⟨P, hPmem⟩]
    rfl
  -- measurable representatives and the adjointness identity
  have hpair : ∀ (u : spectralRange μ ν) (δ : Lp ℂ 2 (parameterMeasure ν)),
      inner ℂ (ridgeletExtension μ ν ρ u) δ =
        ∫ ξ, (starRingEnd ℂ) ((u : Lp ℂ 2 ν) ξ) * backprojection α ν ρ δ ξ ∂ν := by
    intro u δ
    set u' := (Lp.aestronglyMeasurable (u : Lp ℂ 2 ν)).mk _ with hu'
    have hu'e : ((u : Lp ℂ 2 ν) : H → ℂ) =ᵐ[ν] u' := (Lp.aestronglyMeasurable _).ae_eq_mk
    have hu'm : Measurable u' := (Lp.aestronglyMeasurable _).stronglyMeasurable_mk.measurable
    have hu'₂ : MemLp u' 2 ν := (Lp.memLp _).ae_eq hu'e
    rw [hW u, spectralCoefficient_congr_ae hν ρ hu'e, L2.inner_def]
    have := hν.integral_mul_conj_spectralCoefficient hα hρ δ hu'm hu'₂
    calc ∫ p, inner ℂ ((spectralCoefficient ν ρ u' : H × ℝ → ℂ) p) (δ p) ∂parameterMeasure ν
        = ∫ p, δ p * (starRingEnd ℂ) ((spectralCoefficient ν ρ u' : H × ℝ → ℂ) p)
            ∂parameterMeasure ν := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          beta_reduce
          rw [RCLike.inner_apply, mul_comm]
      _ = ∫ ξ, backprojection α ν ρ δ ξ * (starRingEnd ℂ) (u' ξ) ∂ν := this
      _ = ∫ ξ, (starRingEnd ℂ) ((u : Lp ℂ 2 ν) ξ) * backprojection α ν ρ δ ξ ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hu'e] with ξ hξ
          rw [hξ, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hProj, ← map_smul]
    exact LinearMap.mem_range_self _ _
  · rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hv
    change inner ℂ (ridgeletExtension μ ν ρ g) (γ - coefficientProjection α μ ν ρ γ) = 0
    rw [inner_sub_right, hProj, inner_smul_right, hpair, hpair, sub_eq_zero]
    -- the pairing with `Λ_ρ (R_ρ ⟨P, _⟩)` is `C ⟨g, P⟩`
    have hP' : ∫ ξ, (starRingEnd ℂ) ((g : Lp ℂ 2 ν) ξ) *
        backprojection α ν ρ (ridgeletExtension μ ν ρ ⟨P, hPmem⟩) ξ ∂ν =
        (admissibilityConst α ρ : ℂ) * inner ℂ (g : Lp ℂ 2 ν) P := by
      set P' := (Lp.aestronglyMeasurable P).mk _ with hP'def
      have hP'e : (P : H → ℂ) =ᵐ[ν] P' := (Lp.aestronglyMeasurable _).ae_eq_mk
      have hP'm : Measurable P' := (Lp.aestronglyMeasurable _).stronglyMeasurable_mk.measurable
      have hP'₂ : MemLp P' 2 ν := (Lp.memLp _).ae_eq hP'e
      have hPcoe : spectralCoefficient ν ρ
          ((((⟨P, hPmem⟩ : spectralRange μ ν) : Lp ℂ 2 ν)) : H → ℂ) =
            spectralCoefficient ν ρ P' :=
        spectralCoefficient_congr_ae hν ρ hP'e
      rw [hW ⟨P, hPmem⟩, hPcoe, L2.inner_def, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hν.backprojection_spectralCoefficient hα hρ hP'm hP'₂, hP'e] with ξ hξ hξ'
      rw [hξ, RCLike.inner_apply, hξ']
      ring
    rw [hP', ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hρ.pos.ne', Complex.ofReal_one,
      one_mul]
    -- `⟨g, Λ⟩ = ⟨g, P_𝒦 Λ⟩` for `g ∈ 𝒦`
    have hgΛ : ∫ ξ, (starRingEnd ℂ) ((g : Lp ℂ 2 ν) ξ) * backprojection α ν ρ γ ξ ∂ν =
        inner ℂ (g : Lp ℂ 2 ν) Λ := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hΛcoe] with ξ hξ
      rw [hξ, RCLike.inner_apply, mul_comm]
    rw [hgΛ, hPdef, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr g.2]

end Backprojection

end OperatorRidgelet
