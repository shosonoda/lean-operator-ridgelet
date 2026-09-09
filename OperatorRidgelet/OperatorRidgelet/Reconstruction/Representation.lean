import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Reconstruction.Basic
import OperatorRidgelet.Transform.Plancherel

/-!
# Representation of targets with a spectral density and the frame identity (Section 4)

Ridgelet-specific lemmas behind Theorem `thm:A`(i)–(ii), Theorem `thm:C`(i)–(iii), Lemma
`lem:weak-equals-strong`, and Proposition `prop:coefficient-projection`, for the abstract pair
`(μ, ν)` of Appendix H.

* **Regularity along rays.**  The ray moment `M_0(G)` dominates `∫ ‖G(ω₀ a)‖ ν(da)` for a fixed
  `ω₀ ∈ I`, and homogeneity turns this into `∫ ‖G‖ dν < ∞`; a bounded integrable density is
  square integrable.
* **The target `g_G`.**  `g_G` is continuous (dominated convergence) and determines `G`
  (Fourier uniqueness for densities, `OperatorRidgelet.ToMathlib.CharFunDensity`).
* **Parseval in the bias.**  For a direction `a` whose ray function `ω ↦ ρ̂(ω) G(-ωa)` is
  integrable, `∫ γ_G(a,c) ρ(u+c) dc = (2π)⁻¹ ∫ ρ̂(ω) G(-ωa) ρ̂(-ω) e^{-iωu} dω`
  (`eq:bias-parseval`, a Fubini computation); with `u = ⟪a,x⟫` the right side is
  `(2π)⁻¹ ∫ K(ω) F_x(-ωa) dω` with `K = ρ̂ ρ̂(-·)` and `F_x = G e^{i⟪x,·⟫}`, and the separation
  of variables `IsHomogeneous.integral_prod_neg_smul` gives the spectral synthesis identity
  `∫∫ γ_G ρ = C_ρ g_G(x)`.
* **Integral networks.**  For an integrable coefficient `γ`, `S_ρ[γ λ]` is a bounded Borel
  function and `⟨γ, R_ρ g⟩_{L²(λ)} = ∫ S_ρ[γ λ] conj g dμ` (Fubini).
* **The frame identity.**  `ridgeletExtension` is the extension `ridgeletExtensionCLM`, the
  scaled isometry polarizes to `⟨R g, R f⟩ = C_ρ ⟨g, f⟩` on `𝒦`, hence `S_ρ R_ρ = C_ρ T` and the
  reconstruction formulas; the synthesis operator is linear, `J⁻¹ J = Id`, and `U' G = J G` for
  `G ∈ 𝒦`.
* **Fubini for the frame operator.**  `∫ g_G conj g dμ = ∫ G conj(𝒢_μ g) dν` for
  `G ∈ L¹(ν)`, `g ∈ L¹(μ)`; the pairing of `U' G` with the core through the integral network of
  `γ_G`; the pointwise backprojection `Λ_ρ R_ρ f = C_ρ 𝒢_μ f` of the Fourier-slice
  representative, and the injectivity of `𝒢_μ` on `L²(μ)` behind the inverse `Δ_Q`.
* **Vector-valued targets.**  Fourier uniqueness for `Y`-valued densities (pairing with a
  countable dense subset of `Y`), and the `Y`-valued spectral synthesis identity by the same
  Parseval and homogeneity argument with Bochner integrals.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### Regularity along rays and integrability -/

section RayRegular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The ray-derivative bound dominates the values on the ray: `‖G(ωa)‖ₑ ≤ rayDerivBound I G m a`
for `ω ∈ I`. -/
theorem enorm_le_rayDerivBound (I : Set ℝ) (G : H → Y) (m : ℕ) (a : H) {ω : ℝ} (hω : ω ∈ I) :
    ‖G (ω • a)‖ₑ ≤ rayDerivBound I G m a := by
  unfold rayDerivBound
  have h0 : ‖G (ω • a)‖ₑ = ‖iteratedDeriv ((⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) : ℕ)
      (fun ω : ℝ => G (ω • a)) ω‖ₑ := by
    simp [iteratedDeriv_zero]
  rw [h0]
  exact le_iSup_of_le ⟨0, Nat.succ_pos m⟩ (le_iSup₂_of_le ω hω le_rfl)

/-- The frequency window of a band-pass filter is nonempty: it contains the support of
`ρ̂ ≠ 0`. -/
theorem IsFrequencyWindow.nonempty {ρ : SchwartzMap ℝ ℝ} (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) : I.Nonempty := by
  refine Set.Nonempty.mono hI.tsupport_subset (Set.nonempty_iff_ne_empty.mpr fun h => ?_)
  exact filterFourier_ne_zero hρ.ne_zero (tsupport_eq_empty_iff.mp h)

variable [MeasurableSpace H] [BorelSpace H]

/-- For a density regular along rays, `∫ ‖G‖ dν < ∞`: the ray moment `M_0(G)` dominates
`∫ ‖G(ω₀ a)‖ ν(da)` for a fixed `ω₀ ∈ I`, and homogeneity rescales this to `∫ ‖G‖ dν`. -/
theorem IsRegularAlongRays.lintegral_enorm_lt_top {ν : Measure H} {α : ℝ}
    (hν : IsHomogeneous α ν) {I : Set ℝ} {ω₀ : ℝ} (hω₀ : ω₀ ∈ I) (hω₀' : ω₀ ≠ 0) {G : H → Y}
    (hG : IsRegularAlongRays ν I G) :
    ∫⁻ ξ, ‖G ξ‖ₑ ∂ν < ⊤ := by
  have hmeas : Measurable fun ξ => ‖G ξ‖ₑ := hG.stronglyMeasurable.enorm
  have h0 := hG.rayMoment_lt_top 0
  have hle : ∫⁻ a, ‖G (ω₀ • a)‖ₑ ∂ν ≤ rayMoment ν I G 0 := by
    unfold rayMoment
    refine lintegral_mono fun a => ?_
    calc ‖G (ω₀ • a)‖ₑ = 1 * ‖G (ω₀ • a)‖ₑ := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((1 + ‖a‖) ^ (0 + 2)) * rayDerivBound I G 0 a := by
          gcongr
          · rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg a]))
          · exact enorm_le_rayDerivBound I G 0 a hω₀
  rw [hν.lintegral_smul hω₀' hmeas] at hle
  have hc : ENNReal.ofReal (|ω₀| ^ (-α)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hω₀') _)).ne'
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.mul_top hc] at hle
  exact (lt_irrefl _ (lt_of_le_of_lt hle h0)).elim

/-- A density regular along rays is integrable. -/
theorem IsRegularAlongRays.integrable {ν : Measure H} {α : ℝ} (hν : IsHomogeneous α ν)
    {I : Set ℝ} {ω₀ : ℝ} (hω₀ : ω₀ ∈ I) (hω₀' : ω₀ ≠ 0) {G : H → Y}
    (hG : IsRegularAlongRays ν I G) :
    Integrable G ν :=
  ⟨hG.stronglyMeasurable.aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr (hG.lintegral_enorm_lt_top hν hω₀ hω₀')⟩

/-- A density regular along rays is square integrable (bounded and integrable). -/
theorem IsRegularAlongRays.memLp_two {ν : Measure H} {α : ℝ} (hν : IsHomogeneous α ν)
    {I : Set ℝ} {ω₀ : ℝ} (hω₀ : ω₀ ∈ I) (hω₀' : ω₀ ≠ 0) {G : H → ℂ}
    (hG : IsRegularAlongRays ν I G) :
    MemLp G 2 ν := by
  obtain ⟨M, hM⟩ := hG.bounded
  exact memLp_two_of_integrable_of_bound (hG.integrable hν hω₀ hω₀') hM

end RayRegular

/-! ### The target `g_G` -/

section SpectralTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- `g_G` is continuous for `G ∈ L¹(ν)` (dominated convergence). -/
theorem continuous_spectralTarget (ν : Measure H) {G : H → Y} (hG : Integrable G ν) :
    Continuous (spectralTarget ν G) := by
  unfold spectralTarget
  refine continuous_of_dominated (bound := fun ξ => ‖G ξ‖) ?_ ?_ hG.norm ?_
  · intro x
    exact (by fun_prop : Continuous fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).aestronglyMeasurable.smul hG.aestronglyMeasurable
  · intro x
    filter_upwards with ξ
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · filter_upwards with ξ
    fun_prop

end SpectralTarget

section SpectralTargetUniqueness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Fourier uniqueness: `g_G = 0` forces `G = 0` `ν`-almost everywhere, for `G ∈ L¹(ν)`. -/
theorem ae_eq_zero_of_spectralTarget_eq_zero (ν : Measure H) {G : H → ℂ} (hG : Integrable G ν)
    (h : spectralTarget ν G = 0) : G =ᵐ[ν] 0 := by
  refine hG.ae_eq_zero_of_forall_integral_mul_exp_eq_zero fun t => ?_
  have ht := congrFun h t
  rw [Pi.zero_apply] at ht
  rw [← ht]
  unfold spectralTarget
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [smul_eq_mul, mul_comm, real_inner_comm]

end SpectralTargetUniqueness

/-! ### The Fourier transform of a real filter at `-ω` -/

section FilterFourier

/-- `ρ̂(-ω) = ∫ ρ(t) e^{iωt} dt`. -/
theorem filterFourier_neg_eq_integral (ρ : ℝ → ℝ) (ω : ℝ) :
    filterFourier ρ (-ω) = ∫ t, (ρ t : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I) := by
  unfold filterFourier lineFourier LeanRidgelet.Fourier.angularFourierIntegralInner
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- For a real filter, `ρ̂(-ω) = conj(ρ̂(ω))`. -/
theorem filterFourier_neg (ρ : ℝ → ℝ) (ω : ℝ) :
    filterFourier ρ (-ω) = (starRingEnd ℂ) (filterFourier ρ ω) := by
  rw [filterFourier_neg_eq_integral]
  unfold filterFourier lineFourier LeanRidgelet.Fourier.angularFourierIntegralInner
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [RCLike.inner_apply, conj_trivial, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_neg, Complex.conj_I]
  rw [mul_comm]
  congr 2
  push_cast
  ring

end FilterFourier

/-! ### Parseval in the bias for the explicit coefficient -/

section Parseval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bias integral of `γ_G(a, ·)` against the translated filter `c ↦ ρ(u + c)`
(`eq:bias-parseval`): when the ray function `ω ↦ ρ̂(ω) G(-ωa)` is integrable,
`∫ γ_G(a,c) ρ(u+c) dc = (2π)⁻¹ ∫ ρ̂(ω) G(-ωa) ρ̂(-ω) e^{-iωu} dω`. -/
theorem integral_coefficientFormula_mul_shift (ρ : SchwartzMap ℝ ℝ) (G : H → ℂ) (a : H)
    (u : ℝ) (ha : Integrable fun ω : ℝ => filterFourier ρ ω * G (-(ω • a))) :
    ∫ c, coefficientFormula ρ G (a, c) * (ρ (u + c) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ ω, filterFourier ρ ω * G (-(ω • a)) *
        (filterFourier ρ (-ω) * Complex.exp (-((ω * u : ℝ) * Complex.I))) := by
  set Φ : ℝ → ℂ := fun ω => filterFourier ρ ω * G (-(ω • a)) with hΦ
  have hρu : Integrable fun c : ℝ => (ρ (u + c) : ℂ) := (ρ.integrable.comp_add_left u).ofReal
  have hint : Integrable (fun z : ℝ × ℝ =>
      (ρ (u + z.1) : ℂ) * Φ z.2 * Complex.exp ((z.2 * z.1 : ℝ) * Complex.I))
      (volume.prod volume) := by
    refine (hρu.mul_prod ha).mul_unimodular ?_ (Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ =>
        Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)).aestronglyMeasurable
    · exact (Complex.norm_exp_ofReal_mul_I _).le
  have hL : ∀ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (u + c) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ ω, (ρ (u + c) : ℂ) * Φ ω * Complex.exp ((ω * c : ℝ) * Complex.I) := by
    intro c
    unfold coefficientFormula
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hΦ]
    ring
  simp_rw [hL]
  rw [integral_const_mul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hshift : ∀ c : ℝ, (ρ (u + c) : ℂ) * Φ ω * Complex.exp ((ω * c : ℝ) * Complex.I) =
      Φ ω * Complex.exp (-((ω * u : ℝ) * Complex.I)) *
        (fun t : ℝ => (ρ t : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)) (u + c) := by
    intro c
    have hexp : Complex.exp ((ω * c : ℝ) * Complex.I) =
        Complex.exp (-((ω * u : ℝ) * Complex.I)) *
          Complex.exp ((ω * (u + c) : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hshift]
  rw [integral_const_mul, integral_add_left_eq_self
    (f := fun t : ℝ => (ρ t : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)) u,
    ← filterFourier_neg_eq_integral]
  ring

end Parseval

/-! ### The spectral synthesis identity -/

section Synthesis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {ν : Measure H} [SFinite ν] {α : ℝ} {ρ : SchwartzMap ℝ ℝ} {G : H → ℂ}

/-- The kernel `(a, ω) ↦ ρ̂(ω) ρ̂(-ω) G(-ωa) e^{i⟪x, -ωa⟫}` is integrable on `ν ⊗ dω` for
`G ∈ L¹(ν)`: its norm is `|ρ̂(ω)|² |G(-ωa)|`, and homogeneity separates the variables. -/
theorem integrable_synthesis_kernel (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (x : H) :
    Integrable (fun p : H × ℝ => (filterFourier ρ p.2 * filterFourier ρ (-p.2)) *
      (G (-(p.2 • p.1)) * Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I)))
      (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  refine ⟨?_, ?_⟩
  · exact (((continuous_filterFourier ρ).comp continuous_snd).mul
      ((continuous_filterFourier ρ).comp continuous_snd.neg)).aestronglyMeasurable.mul
      ((hG.comp hc.measurable).aestronglyMeasurable.mul
        (by fun_prop : Continuous fun p : H × ℝ =>
          Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I)).aestronglyMeasurable)
  · rw [HasFiniteIntegral]
    have hnorm : ∀ p : H × ℝ, ‖(filterFourier ρ p.2 * filterFourier ρ (-p.2)) *
        (G (-(p.2 • p.1)) * Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I))‖ₑ =
        ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ := by
      intro p
      rw [enorm_mul, enorm_mul, enorm_mul, filterFourier_neg, RCLike.enorm_conj,
        Complex.enorm_exp_ofReal_mul_I, mul_one, sq]
    simp_rw [hnorm]
    rw [hν.lintegral_prod_neg_smul (K := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2)
      ((continuous_filterFourier ρ).measurable.enorm.pow_const 2) hG.enorm,
      hρ.lintegral_enorm_sq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp hG₁.hasFiniteIntegral)

/-- For `ν`-almost every direction, the bias integral of `γ_G` against the ridge function
`c ↦ ρ(⟪a,x⟫ + c)` is the frequency integral `(2π)⁻¹ ∫ ρ̂(ω) ρ̂(-ω) G(-ωa) e^{i⟪x,-ωa⟫} dω`. -/
theorem ae_integral_coefficientFormula_mul_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) (x : H) :
    ∀ᵐ a ∂ν, ∫ c, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ ω, (filterFourier ρ ω * filterFourier ρ (-ω)) *
        (G (-(ω • a)) * Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I)) := by
  filter_upwards [ae_integrable_ray hα hν hρ hG hG₂] with a ha
  rw [integral_coefficientFormula_mul_shift ρ G a ⟪a, x⟫ ha]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hphase : ((⟪x, -(ω • a)⟫ : ℝ) : ℂ) * Complex.I = -((ω * ⟪a, x⟫ : ℝ) * Complex.I) := by
    rw [inner_neg_right, inner_smul_right, real_inner_comm]
    push_cast
    ring
  beta_reduce
  rw [hphase]
  ring

/-- For `ν`-almost every direction, `c ↦ γ_G(a,c) ρ(⟪a,x⟫ + c)` is integrable: `γ_G(a, ·)` is
bounded by `(2π)⁻¹ ∫ |ρ̂(ω) G(-ωa)| dω` and the ridge function is integrable. -/
theorem ae_integrable_coefficientFormula_mul_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₂ : MemLp G 2 ν) (x : H) :
    ∀ᵐ a ∂ν, Integrable fun c : ℝ => coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ) := by
  filter_upwards [ae_integrable_ray hα hν hρ hG hG₂] with a ha
  have hρx : Integrable fun c : ℝ => (ρ (⟪a, x⟫ + c) : ℂ) :=
    (ρ.integrable.comp_add_left ⟪a, x⟫).ofReal
  have hmeas : AEStronglyMeasurable (fun c : ℝ => coefficientFormula ρ G (a, c)) volume :=
    ((stronglyMeasurable_coefficientFormula ρ hG).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine hρx.bdd_mul (c := (2 * Real.pi)⁻¹ * ∫ ω, ‖filterFourier ρ ω * G (-(ω • a))‖) hmeas
    (Eventually.of_forall fun c => ?_)
  unfold coefficientFormula
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The outer integrand `a ↦ ∫ γ_G(a,c) ρ(⟪a,x⟫ + c) dc` is `ν`-integrable for
`G ∈ L¹(ν) ∩ L²(ν)`. -/
theorem integrable_integral_coefficientFormula_mul_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν)
    (x : H) :
    Integrable (fun a : H => ∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ν := by
  have hint := (integrable_synthesis_kernel hν hρ hG hG₁ x).integral_prod_left
  refine (hint.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)).congr ?_
  filter_upwards [ae_integral_coefficientFormula_mul_ridge hα hν hρ hG hG₂ x] with a ha
  rw [ha]

/-- **Spectral synthesis identity** (`eq:spectral-synthesis`): for `G ∈ L¹(ν) ∩ L²(ν)`,
`∫ [∫ γ_G(a,c) ρ(⟪a,x⟫+c) dc] ν(da) = C^{(α)}_ρ g_G(x)`. -/
theorem integral_integral_coefficientFormula_mul_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν)
    (x : H) :
    ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∂ν =
      admissibilityConst α ρ * spectralTarget ν G x := by
  have hint := integrable_synthesis_kernel hν hρ hG hG₁ x
  have hFmeas : Measurable fun ξ : H => G ξ * Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) :=
    hG.mul (by fun_prop : Continuous fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).measurable
  calc ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∂ν
      = ∫ a : H, (((2 * Real.pi)⁻¹ : ℝ) * ∫ ω : ℝ, (filterFourier ρ ω * filterFourier ρ (-ω)) *
          (G (-(ω • a)) * Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I))) ∂ν :=
        integral_congr_ae (ae_integral_coefficientFormula_mul_ridge hα hν hρ hG hG₂ x)
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ p : H × ℝ, (filterFourier ρ p.2 * filterFourier ρ (-p.2)) *
          (G (-(p.2 • p.1)) * Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I))
          ∂ν.prod volume := by
        rw [integral_const_mul, integral_prod _ hint]
    _ = ((2 * Real.pi)⁻¹ : ℝ) *
          ((∫ ω : ℝ, filterFourier ρ ω * filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) *
            ∫ ξ : H, G ξ * Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) ∂ν) := by
        rw [hν.integral_prod_neg_smul (K := fun ω => filterFourier ρ ω * filterFourier ρ (-ω))
          (F := fun ξ => G ξ * Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)) hFmeas hint]
    _ = admissibilityConst α ρ * spectralTarget ν G x := by
        have hC := crossAdmissibilityConst_self α ρ
        unfold crossAdmissibilityConst at hC
        simp_rw [← filterFourier_neg] at hC
        rw [← mul_assoc, hC]
        congr 1
        unfold spectralTarget
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        beta_reduce
        rw [smul_eq_mul, mul_comm]

/-- When `γ_G ∈ L¹(λ)`, the iterated integral is the integral network `S_ρ[γ_G λ](x)`. -/
theorem integral_integral_coefficientFormula_eq_integralNetworkDensity
    (hγ : Integrable (coefficientFormula ρ G) (parameterMeasure ν)) (x : H) :
    ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∂ν =
      integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
        (coefficientFormula ρ G) x := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  have hint : Integrable (fun θ : H × ℝ => (ρ (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ)
      (parameterMeasure ν) := by
    simp_rw [smul_eq_mul]
    refine hγ.bdd_mul (c := C) (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun θ : H × ℝ => ⟪θ.1, x⟫ + θ.2))).aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    rw [Complex.norm_real]
    exact hC.2 _
  unfold integralNetworkDensity parameterMeasure
  rw [integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul, mul_comm]

end Synthesis

/-! ### Integral networks of integrable coefficients -/

section IntegralNetwork

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The integral network of an integrable coefficient is bounded by `‖ρ‖_∞ ‖γ‖_{L¹(λ)}`. -/
theorem norm_integralNetworkDensity_le (ρ : SchwartzMap ℝ ℝ) (lam : Measure (H × ℝ))
    {γ : H × ℝ → ℂ} (hγ : Integrable γ lam) (x : H) {M : ℝ} (hM : ∀ t, ‖ρ t‖ ≤ M) :
    ‖integralNetworkDensity (fun t => (ρ t : ℂ)) lam γ x‖ ≤ M * ∫ θ, ‖γ θ‖ ∂lam := by
  unfold integralNetworkDensity
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _)
    (hγ.norm.const_mul M) (Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

variable [SecondCountableTopology H] [OpensMeasurableSpace H]

/-- The integral network of an (almost everywhere strongly measurable) coefficient is a Borel
function of the input. -/
theorem measurable_integralNetworkDensity (ρ : SchwartzMap ℝ ℝ) (lam : Measure (H × ℝ))
    [SFinite lam] {γ : H × ℝ → ℂ} (hγ : AEStronglyMeasurable γ lam) :
    Measurable (integralNetworkDensity (fun t => (ρ t : ℂ)) lam γ) := by
  set γ' := hγ.mk γ with hγ'_def
  have hγ' : StronglyMeasurable γ' := hγ.stronglyMeasurable_mk
  have heq : integralNetworkDensity (fun t => (ρ t : ℂ)) lam γ =
      integralNetworkDensity (fun t => (ρ t : ℂ)) lam γ' := by
    funext x
    unfold integralNetworkDensity
    refine integral_congr_ae ?_
    filter_upwards [hγ.ae_eq_mk] with θ hθ
    rw [hθ]
  rw [heq]
  have h1 : Measurable fun q : H × (H × ℝ) => (ρ (inner ℝ q.2.1 q.1 + q.2.2) : ℂ) :=
    (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun q : H × (H × ℝ) => inner ℝ q.2.1 q.1 + q.2.2))).measurable
  have hF : StronglyMeasurable fun q : H × (H × ℝ) =>
      (ρ (inner ℝ q.2.1 q.1 + q.2.2) : ℂ) • γ' q.2 :=
    h1.stronglyMeasurable.smul (hγ'.comp_measurable measurable_snd)
  exact hF.integral_prod_right'.measurable

/-- The pairing identity of Lemma `lem:weak-equals-strong`:
`∫ γ conj(R_ρ g) dλ = ∫ S_ρ[γ λ] conj g dμ` for integrable `γ` and `g` (Fubini). -/
theorem integral_mul_conj_ridgelet (μ : Measure H) [IsFiniteMeasure μ] (ν : Measure H)
    [SFinite ν] (ρ : SchwartzMap ℝ ℝ) {γ : H × ℝ → ℂ} (hγ : Integrable γ (parameterMeasure ν))
    {g : H → ℂ} (hg : Integrable g μ) :
    ∫ p, γ p * (starRingEnd ℂ) (ridgelet μ ρ g p) ∂parameterMeasure ν =
      ∫ x, integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν) γ x *
        (starRingEnd ℂ) (g x) ∂μ := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  haveI : SFinite (parameterMeasure ν) := by
    unfold parameterMeasure
    infer_instance
  have hint : Integrable (fun z : (H × ℝ) × H =>
      γ z.1 * (starRingEnd ℂ) (g z.2) * (ρ (⟪z.1.1, z.2⟫ + z.1.2) : ℂ))
      ((parameterMeasure ν).prod μ) := by
    refine (hγ.mul_prod hg.conj_comp).mul_bdd (c := C) (Complex.continuous_ofReal.comp
      (ρ.continuous.comp (by fun_prop : Continuous fun z : (H × ℝ) × H =>
        ⟪z.1.1, z.2⟫ + z.1.2))).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Complex.norm_real]
    exact hC.2 _
  have hL : ∀ p : H × ℝ, γ p * (starRingEnd ℂ) (ridgelet μ ρ g p) =
      ∫ x, γ p * (starRingEnd ℂ) (g x) * (ρ (⟪p.1, x⟫ + p.2) : ℂ) ∂μ := by
    intro p
    unfold ridgelet
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  unfold integralNetworkDensity
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [smul_eq_mul]
  ring

end IntegralNetwork

/-! ### The frame identity on `𝒦` -/

section Frame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SFinite ν] {α : ℝ}
  (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hν hρ

/-- The extension `ridgeletExtension` chosen in the definitions is `ridgeletExtensionCLM`. -/
theorem ridgeletExtension_eq :
    ridgeletExtension μ ν ρ = ridgeletExtensionCLM hν hρ := by
  have hex : ∃ R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f :=
    ⟨_, coeFn_ridgeletExtensionCLM_embed hν hρ⟩
  unfold ridgeletExtension
  rw [dif_pos hex]
  exact eq_ridgeletExtensionCLM hν hρ _ hex.choose_spec

/-- The polarized Plancherel identity on `𝒦`: `⟪R g, R f⟫_{L²(λ)} = C^{(α)}_ρ ⟪g, f⟫`. -/
theorem inner_ridgeletExtensionCLM (f g : spectralRange μ ν) :
    inner ℂ (ridgeletExtensionCLM hν hρ g) (ridgeletExtensionCLM hν hρ f) =
      (admissibilityConst α ρ : ℂ) * inner ℂ g f := by
  set T : spectralRange μ ν →L[ℂ] spectralRange μ ν :=
    (ContinuousLinearMap.adjoint (ridgeletExtensionCLM hν hρ)).comp (ridgeletExtensionCLM hν hρ) -
      (admissibilityConst α ρ : ℂ) • ContinuousLinearMap.id ℂ (spectralRange μ ν) with hT
  have hT0 : ∀ u, inner ℂ (T u) u = 0 := by
    intro u
    have hnorm := norm_ridgeletExtensionCLM_sq hν hρ u
    simp only [hT, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
    rw [Submodule.coe_inner (spectralRange μ ν) _ u, Submodule.coe_smul, inner_smul_left,
      ← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      Complex.conj_ofReal]
    show ((‖ridgeletExtensionCLM hν hρ u‖ : ℝ) : ℂ) ^ 2 -
      ((admissibilityConst α ρ : ℝ) : ℂ) * ((‖u‖ : ℝ) : ℂ) ^ 2 = 0
    rw [← Complex.ofReal_pow, hnorm]
    push_cast
    ring
  have hzero : T = 0 := by
    have h := (inner_map_self_eq_zero (T : spectralRange μ ν →ₗ[ℂ] spectralRange μ ν)).mp hT0
    refine ContinuousLinearMap.ext fun u => ?_
    exact congrArg (fun S : spectralRange μ ν →ₗ[ℂ] spectralRange μ ν => S u) h
  have h := congrArg (fun S : spectralRange μ ν →L[ℂ] spectralRange μ ν => inner ℂ (S g) f) hzero
  simp only [hT, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    _root_.zero_apply, inner_zero_left] at h
  rw [Submodule.coe_inner (spectralRange μ ν) _ f, Submodule.coe_smul, inner_smul_left,
    ← Submodule.coe_inner, Complex.conj_ofReal] at h
  exact sub_eq_zero.mp h

/-- The frame identity `S_ρ R_ρ f = C^{(α)}_ρ T f` on `𝒦`, for an `α`-admissible filter. -/
theorem synthesis_ridgeletExtension (f : spectralRange μ ν) :
    synthesis μ ν ρ (ridgeletExtension μ ν ρ f) =
      (admissibilityConst α ρ : ℂ) • frameOperator μ ν f := by
  ext g
  simp only [synthesis, frameOperator, transposeEmbed, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, innerSLFlip_apply_apply, Submodule.subtypeL_apply,
    ridgeletExtension_eq hν hρ, smul_eq_mul]
  rw [inner_ridgeletExtensionCLM hν hρ, Submodule.coe_inner]

/-- The minimum-norm solution of `S_ρ γ = F`: `S_ρ (C⁻¹ R_ρ J⁻¹ F) = F`. -/
theorem synthesis_smul_ridgeletExtension_rieszInv (F : SpectralAntiDual μ ν) :
    synthesis μ ν ρ
      ((((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • ridgeletExtension μ ν ρ (rieszInv μ ν F)) = F := by
  have hC : (admissibilityConst α ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.pos.ne'
  have hlin : synthesis μ ν ρ ((((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
      ridgeletExtension μ ν ρ (rieszInv μ ν F)) = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
      synthesis μ ν ρ (ridgeletExtension μ ν ρ (rieszInv μ ν F)) := by
    ext g
    simp only [synthesis, ContinuousLinearMap.comp_apply, innerSLFlip_apply_apply,
      _root_.smul_apply, inner_smul_right, smul_eq_mul]
  rw [hlin, synthesis_ridgeletExtension hν hρ]
  change (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • (admissibilityConst α ρ : ℂ) •
    rieszMap μ ν (rieszInv μ ν F) = F
  rw [rieszMap_rieszInv, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hC, one_smul]

end Frame

/-! ### The synthesis operator and the Riesz maps -/

section SynthesisAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

variable (μ ν : Measure H) [IsFiniteMeasure μ] (ρ : ℝ → ℝ)

/-- `(S_ρ γ)[g] = ⟪R_ρ g, γ⟫_{L²(λ)}` (Mathlib's inner product is conjugate linear in the
first argument). -/
theorem synthesis_apply (γ : Lp ℂ 2 (parameterMeasure ν)) (g : spectralRange μ ν) :
    synthesis μ ν ρ γ g = inner ℂ (ridgeletExtension μ ν ρ g) γ := rfl

/-- The synthesis operator is homogeneous. -/
theorem synthesis_smul (c : ℂ) (γ : Lp ℂ 2 (parameterMeasure ν)) :
    synthesis μ ν ρ (c • γ) = c • synthesis μ ν ρ γ := by
  ext g
  simp only [synthesis_apply, _root_.smul_apply, inner_smul_right, smul_eq_mul]

/-- The synthesis operator is additive on differences. -/
theorem synthesis_sub (γ γ' : Lp ℂ 2 (parameterMeasure ν)) :
    synthesis μ ν ρ (γ - γ') = synthesis μ ν ρ γ - synthesis μ ν ρ γ' := by
  ext g
  simp only [synthesis_apply, _root_.sub_apply, inner_sub_right]

/-- `S_ρ γ = 0` if and only if `γ ⊥ Ran R_ρ`. -/
theorem synthesis_eq_zero_iff (γ : Lp ℂ 2 (parameterMeasure ν)) :
    synthesis μ ν ρ γ = 0 ↔ γ ∈ (ridgeletRange μ ν ρ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hu
    have := congrArg (fun F : SpectralAntiDual μ ν => F g) h
    simpa [synthesis_apply] using this
  · intro h
    ext g
    rw [synthesis_apply, _root_.zero_apply]
    exact h _ (LinearMap.mem_range.mpr ⟨g, rfl⟩)

/-- `J⁻¹ (J f) = f`. -/
theorem rieszInv_rieszMap (f : spectralRange μ ν) : rieszInv μ ν (rieszMap μ ν f) = f := by
  have h : antiDualConj (rieszMap μ ν f) = InnerProductSpace.toDual ℂ (spectralRange μ ν) f := by
    ext g
    simp only [rieszMap, antiDualConj_apply, innerSLFlip_apply_apply,
      InnerProductSpace.toDual_apply_apply, inner_conj_symm]
  unfold rieszInv
  rw [h, LinearIsometryEquiv.symm_apply_apply]

/-- `U' G = J G` for `G ∈ 𝒦`: the transpose of the embedding restricted to `𝒦` is the Riesz
map. -/
theorem transposeEmbed_coe (G : spectralRange μ ν) :
    transposeEmbed μ ν (G : Lp ℂ 2 ν) = rieszMap μ ν G := by
  ext g
  simp only [transposeEmbed, rieszMap, ContinuousLinearMap.comp_apply, innerSLFlip_apply_apply,
    Submodule.subtypeL_apply, Submodule.coe_inner]

/-- `J⁻¹ (U' G) = G` for `G ∈ 𝒦`. -/
theorem rieszInv_transposeEmbed_coe (G : spectralRange μ ν) :
    rieszInv μ ν (transposeEmbed μ ν (G : Lp ℂ 2 ν)) = G := by
  rw [transposeEmbed_coe, rieszInv_rieszMap]

end SynthesisAlgebra

/-! ### Fubini for the frame operator -/

section FrameFubini

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
  [MeasurableSpace H] [OpensMeasurableSpace H]

/-- `∫ g_G(x) conj(g(x)) μ(dx) = ∫ G(ξ) conj(𝒢_μ g(ξ)) ν(dξ)` for `G ∈ L¹(ν)` and `g ∈ L¹(μ)`
(Fubini). -/
theorem integral_spectralTarget_mul_conj (μ : Measure H) [SFinite μ] (ν : Measure H)
    [SFinite ν] {G : H → ℂ} (hG : Integrable G ν) {g : H → ℂ} (hg : Integrable g μ) :
    ∫ x, spectralTarget ν G x * (starRingEnd ℂ) (g x) ∂μ =
      ∫ ξ, G ξ * (starRingEnd ℂ) (gaussFourier μ g ξ) ∂ν := by
  have hint : Integrable (fun z : H × H =>
      (starRingEnd ℂ) (g z.1) * G z.2 * Complex.exp ((⟪z.1, z.2⟫ : ℝ) * Complex.I))
      (μ.prod ν) := by
    refine (hg.conj_comp.mul_prod hG).mul_unimodular ?_ (Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : H × H =>
        Complex.exp ((⟪z.1, z.2⟫ : ℝ) * Complex.I)).aestronglyMeasurable
    · exact (Complex.norm_exp_ofReal_mul_I _).le
  have hL : ∀ x : H, spectralTarget ν G x * (starRingEnd ℂ) (g x) =
      ∫ ξ, (starRingEnd ℂ) (g x) * G ξ * Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) ∂ν := by
    intro x
    unfold spectralTarget
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [smul_eq_mul]
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  unfold gaussFourier character
  rw [← integral_conj, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring_nf

end FrameFubini

/-! ### The pairing of `U' G` with the core through the integral network -/

section Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

variable {μ ν : Measure H} [IsProbabilityMeasure μ] [SFinite ν] {α : ℝ}
  (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ} (hρ : IsAdmissible α ρ)
include hν hρ

omit [SecondCountableTopology H] hρ in
/-- The explicit coefficient depends only on the `ν`-class of the density, `λ`-almost
everywhere. -/
theorem coefficientFormula_congr_ae {G G' : H → ℂ} (h : G =ᵐ[ν] G') :
    coefficientFormula ρ G =ᵐ[parameterMeasure ν] coefficientFormula ρ G' := by
  have hae := hν.ae_ae_eq_neg_smul' h
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with p hp
  unfold coefficientFormula
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hp] with ω hω
  rw [hω]

omit [SecondCountableTopology H] in
/-- `W_ρ G` is the class of `γ_G` for `G ∈ L²(ν)` given as an `L²` class. -/
theorem coeFn_spectralCoefficient_coe (hα : 0 < α) (G : Lp ℂ 2 ν) :
    (spectralCoefficient ν ρ G : H × ℝ → ℂ) =ᵐ[parameterMeasure ν]
      coefficientFormula ρ (G : H → ℂ) := by
  set G' := (Lp.aestronglyMeasurable G).mk G with hG'
  have hGG' : (G : H → ℂ) =ᵐ[ν] G' := (Lp.aestronglyMeasurable G).ae_eq_mk
  have hG'm : Measurable G' := (Lp.aestronglyMeasurable G).stronglyMeasurable_mk.measurable
  have hG'₂ : MemLp G' 2 ν := (Lp.memLp G).ae_eq hGG'
  rw [spectralCoefficient_congr_ae hν ρ hGG', spectralCoefficient_eq_toLp hν hα hρ hG'm hG'₂]
  exact (MemLp.coeFn_toLp _).trans (coefficientFormula_congr_ae hν hGG'.symm)

/-- Theorem `thm:C`(iii), last part: for `G ∈ 𝒦` with `γ_G ∈ L¹(λ)`, the functional `U' G`
paired with `g ∈ 𝒟` is `C⁻¹ ∫ S_ρ[γ_G λ] conj g dμ`. -/
theorem transposeEmbed_apply_eq_integral_integralNetworkDensity (hα : 0 < α)
    (G : spectralRange μ ν)
    (hγ : Integrable (coefficientFormula ρ ((G : Lp ℂ 2 ν) : H → ℂ)) (parameterMeasure ν))
    (g : spectralCore μ ν) :
    transposeEmbed μ ν G (spectralEmbed μ ν g) =
      (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) *
        ∫ x, integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
            (coefficientFormula ρ ((G : Lp ℂ 2 ν) : H → ℂ)) x *
          (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  have hC : (admissibilityConst α ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.pos.ne'
  have hg : Integrable ((g : Lp ℂ 2 μ) : H → ℂ) μ := (Lp.memLp _).integrable one_le_two
  have h1 : transposeEmbed μ ν G = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
      synthesis μ ν ρ (spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ)) := by
    rw [← ridgeletExtensionCLM_eq_spectralCoefficient hν hα hρ μ G, ← ridgeletExtension_eq hν hρ,
      synthesis_ridgeletExtension hν hρ G, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hC,
      one_smul]
    rfl
  rw [h1, _root_.smul_apply, smul_eq_mul]
  congr 1
  rw [synthesis_apply, L2.inner_def, ← integral_mul_conj_ridgelet μ ν ρ hγ hg]
  have hR : (ridgeletExtension μ ν ρ (spectralEmbed μ ν g) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν]
      ridgelet μ ρ g := by
    rw [ridgeletExtension_eq hν hρ]
    exact coeFn_ridgeletExtensionCLM_embed hν hρ g
  refine integral_congr_ae ?_
  filter_upwards [hR, coeFn_spectralCoefficient_coe hν hρ hα (G : Lp ℂ 2 ν)] with p hp hw
  rw [RCLike.inner_apply, hp, hw]

end Pairing

/-! ### Backprojection of the Fourier-slice representative -/

section Backprojection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- `Λ_ρ` applied to the continuous Fourier-slice representative `(a, ω) ↦ ρ̂(ω) 𝒢_μ f(-ωa)` of
`R_ρ f` gives `C^{(α)}_ρ 𝒢_μ f(ξ)` pointwise: along `a = -ξ/ω` the slice is `ρ̂(ω) 𝒢_μ f(ξ)`. -/
theorem backprojectionOf_biasFourier_ridgelet (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ)
    (ρ : SchwartzMap ℝ ℝ) {f : H → ℂ} (hf : Integrable f μ) (ξ : H) :
    backprojectionOf α ρ (biasFourier (ridgelet μ ρ f)) ξ =
      admissibilityConst α ρ * gaussFourier μ f ξ := by
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have key : ∀ᵐ ω : ℝ ∂volume,
      (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) *
          biasFourier (ridgelet μ ρ f) (-(ω⁻¹ • ξ)) ω =
        ((‖filterFourier ρ ω‖ ^ 2 * |ω| ^ (-α) : ℝ) : ℂ) * gaussFourier μ f ξ := by
    filter_upwards [h0] with ω hω
    rw [biasFourier_ridgelet μ ρ hf]
    have hξ : -(ω • -(ω⁻¹ • ξ)) = ξ := by
      rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hω, one_smul]
    rw [hξ]
    push_cast
    rw [← Complex.conj_mul']
    ring
  unfold backprojectionOf admissibilityConst
  rw [integral_congr_ae key, integral_mul_const, integral_complex_ofReal]
  push_cast
  ring

end Backprojection

/-! ### Injectivity of `𝒢_μ` on `L²(μ)` and the inverse `Δ_Q` -/

section Inverse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- `𝒢_μ` is additive on differences of `L²(μ)` classes. -/
theorem gaussFourier_coe_sub (μ : Measure H) [IsFiniteMeasure μ] (f g : Lp ℂ 2 μ) :
    gaussFourier μ ((f - g : Lp ℂ 2 μ) : H → ℂ) = gaussFourier μ f - gaussFourier μ g := by
  funext ξ
  simp only [gaussFourier, Pi.sub_apply]
  rw [← integral_sub (integrable_mul_character μ f ξ) (integrable_mul_character μ g ξ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx, Pi.sub_apply, sub_mul]

/-- `𝒢_μ` is injective on `L²(μ)` (Fourier uniqueness). -/
theorem Lp.eq_of_gaussFourier_eq (μ : Measure H) [IsFiniteMeasure μ] {f g : Lp ℂ 2 μ}
    (h : gaussFourier μ f = gaussFourier μ g) : f = g := by
  have hint : Integrable ((f - g : Lp ℂ 2 μ) : H → ℂ) μ := (Lp.memLp _).integrable one_le_two
  have hzero : ∀ ξ, gaussFourier μ ((f - g : Lp ℂ 2 μ) : H → ℂ) ξ = 0 := by
    intro ξ
    rw [gaussFourier_coe_sub, Pi.sub_apply, h, sub_self]
  have hae := ae_eq_zero_of_gaussFourier_eq_zero μ hint hzero
  rw [← sub_eq_zero]
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 2 μ).symm)

/-- `Δ_Q (𝒢_μ f) = f` for `f ∈ 𝒟`. -/
theorem gaussFourierInv_gaussFourier (μ ν : Measure H) [IsFiniteMeasure μ]
    (f : spectralCore μ ν) : gaussFourierInv μ ν (gaussFourier μ f) = f := by
  have hex : ∃ f' : Lp ℂ 2 μ, f' ∈ spectralCore μ ν ∧ gaussFourier μ f' = gaussFourier μ f :=
    ⟨f, f.2, rfl⟩
  unfold gaussFourierInv
  rw [dif_pos hex]
  exact Lp.eq_of_gaussFourier_eq μ hex.choose_spec.2

end Inverse

/-! ### Fourier uniqueness for vector-valued densities -/

section VectorUniqueness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

omit [CompleteSpace H] [SecondCountableTopology H] [SecondCountableTopology Y] in
/-- Pairing the `Y`-valued target with a vector `y`: `⟪y, g_G(x)⟫ = g_{⟪y, G⟫}(x)`. -/
theorem inner_spectralTarget (ν : Measure H) {G : H → Y} (hG : Integrable G ν) (y : Y) (x : H) :
    inner ℂ y (spectralTarget ν G x) = spectralTarget ν (fun ξ => inner ℂ y (G ξ)) x := by
  unfold spectralTarget
  have hint : Integrable (fun ξ => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) ν := by
    refine hG.smul_of_top_right (memLp_top_of_bound ?_ 1 (Eventually.of_forall fun ξ => ?_))
    · exact (by fun_prop : Continuous fun ξ : H =>
        Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).aestronglyMeasurable
    · exact (Complex.norm_exp_ofReal_mul_I _).le
  have h := ((innerSL ℂ y).integral_comp_comm hint).symm
  simp only [innerSL_apply_apply] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [inner_smul_right, smul_eq_mul]

/-- Fourier uniqueness for `Y`-valued densities: `g_G = 0` forces `G = 0` `ν`-almost
everywhere.  Pairing with the vectors of a countable dense subset of `Y` reduces to the scalar
case. -/
theorem ae_eq_zero_of_spectralTarget_eq_zero_vec (ν : Measure H) {G : H → Y}
    (hG : Integrable G ν) (h : spectralTarget ν G = 0) : G =ᵐ[ν] 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  have hy : ∀ y : Y, (fun ξ => inner ℂ y (G ξ)) =ᵐ[ν] 0 := by
    intro y
    refine ae_eq_zero_of_spectralTarget_eq_zero ν (hG.const_inner y) ?_
    funext x
    rw [Pi.zero_apply, ← inner_spectralTarget ν hG y x, h, Pi.zero_apply, inner_zero_right]
  have hD : ∀ᵐ ξ ∂ν, ∀ y ∈ D, inner ℂ y (G ξ) = 0 := (ae_ball_iff hDc).mpr fun y _ => hy y
  filter_upwards [hD] with ξ hξ
  have hfun : (fun y : Y => inner ℂ y (G ξ)) = fun _ => (0 : ℂ) :=
    Continuous.ext_on hDd (continuous_id.inner continuous_const) continuous_const fun y hy =>
      hξ y hy
  have h0 : inner ℂ (G ξ) (G ξ) = 0 := congrFun hfun (G ξ)
  simpa using inner_self_eq_zero.mp h0

end VectorUniqueness

/-! ### Vector-valued targets: Theorem `thm:A`(ii) -/

section VectorSynthesis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The bias integral of the translated filter against the phase:
`∫ ρ(u+c) e^{iωc} dc = e^{-iωu} ρ̂(-ω)`. -/
theorem integral_shift_mul_exp (ρ : SchwartzMap ℝ ℝ) (u ω : ℝ) :
    ∫ c, (ρ (u + c) : ℂ) * Complex.exp ((ω * c : ℝ) * Complex.I) =
      Complex.exp (-((ω * u : ℝ) * Complex.I)) * filterFourier ρ (-ω) := by
  have hshift : ∀ c : ℝ, (ρ (u + c) : ℂ) * Complex.exp ((ω * c : ℝ) * Complex.I) =
      Complex.exp (-((ω * u : ℝ) * Complex.I)) *
        (fun t : ℝ => (ρ t : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)) (u + c) := by
    intro c
    have hexp : Complex.exp ((ω * c : ℝ) * Complex.I) =
        Complex.exp (-((ω * u : ℝ) * Complex.I)) *
          Complex.exp ((ω * (u + c) : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hshift]
  rw [integral_const_mul, integral_add_left_eq_self
    (f := fun t : ℝ => (ρ t : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)) u,
    ← filterFourier_neg_eq_integral]

/-- Fubini and homogeneity separate a product-type Bochner integrand:
`∫ K(ω) • F(-ωa) d(ν ⊗ dω) = (∫ K(ω) |ω|^{-α} dω) • ∫ F dν`. -/
theorem IsHomogeneous.integral_prod_neg_smul_vec {α : ℝ} {ν : Measure H} [SFinite ν]
    (hν : IsHomogeneous α ν) {K : ℝ → ℂ} {F : H → Y} (hF : StronglyMeasurable F)
    (hint : Integrable (fun p : H × ℝ => K p.2 • F (-(p.2 • p.1))) (ν.prod volume)) :
    ∫ p : H × ℝ, K p.2 • F (-(p.2 • p.1)) ∂ν.prod volume =
      (∫ ω, K ω * ((|ω| ^ (-α) : ℝ) : ℂ)) • ∫ ξ, F ξ ∂ν := by
  rw [integral_prod_symm _ hint]
  have h0 : ∀ᵐ ω : ℝ ∂volume, ω ≠ 0 := by
    rw [ae_iff]
    simp
  have key : ∀ᵐ ω : ℝ ∂volume, ∫ a, K ω • F (-(ω • a)) ∂ν =
      (K ω * ((|ω| ^ (-α) : ℝ) : ℂ)) • ∫ ξ, F ξ ∂ν := by
    filter_upwards [h0] with ω hω
    rw [integral_smul]
    have : (fun a : H => F (-(ω • a))) = fun a => F ((-ω) • a) := by
      funext a
      rw [neg_smul]
    rw [this, ← integral_map (measurable_const_smul (-ω)).aemeasurable
      hF.aestronglyMeasurable, hν (-ω) (neg_ne_zero.mpr hω), integral_smul_measure, abs_neg,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg ω) _),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rfl
  rw [integral_congr_ae key, integral_smul_const]

variable {ν : Measure H} [SFinite ν] {α : ℝ} {ρ : SchwartzMap ℝ ℝ} {G : H → Y}

omit [CompleteSpace Y] in
/-- For `G ∈ L²(ν; Y)` and admissible `ρ`, the ray function `ω ↦ ρ̂(ω) • G(-ωa)` is integrable
for `ν`-almost every direction (the scalar statement applied to `‖G‖`). -/
theorem ae_integrable_ray_vec (hα : 0 < α) (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) :
    ∀ᵐ a ∂ν, Integrable fun ω : ℝ => filterFourier ρ ω • G (-(ω • a)) := by
  have hN : Measurable fun ξ => ((‖G ξ‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp hG.norm.measurable
  have hN₂ : MemLp (fun ξ => ((‖G ξ‖ : ℝ) : ℂ)) 2 ν := by
    refine (memLp_two_iff_integrable_sq_norm hN.aestronglyMeasurable).mpr
      (hG₂.integrable_norm_sq.congr (Eventually.of_forall fun ξ => ?_))
    simp only [Complex.norm_real, norm_norm]
  filter_upwards [ae_integrable_ray hα hν hρ hN hN₂] with a ha
  have hmeas : AEStronglyMeasurable (fun ω : ℝ => filterFourier ρ ω • G (-(ω • a))) volume :=
    ((continuous_filterFourier ρ).measurable.stronglyMeasurable.smul
      (hG.comp_measurable (by fun_prop : Continuous fun ω : ℝ => -(ω • a)).measurable))
        |>.aestronglyMeasurable
  refine (integrable_norm_iff hmeas).mp (ha.norm.congr (Eventually.of_forall fun ω => ?_))
  simp only [norm_mul, Complex.norm_real, norm_norm, norm_smul]

omit [CompleteSpace Y] in
/-- The explicit `Y`-valued coefficient `γ_G` is strongly measurable on `H × ℝ`. -/
theorem stronglyMeasurable_coefficientFormulaVec (ρ : SchwartzMap ℝ ℝ)
    (hG : StronglyMeasurable G) :
    StronglyMeasurable (coefficientFormulaVec ρ G) := by
  have hF : StronglyMeasurable fun q : (H × ℝ) × ℝ =>
      (filterFourier ρ q.2 * Complex.exp ((q.2 * q.1.2 : ℝ) * Complex.I)) •
        G (-(q.2 • q.1.1)) := by
    refine (Measurable.stronglyMeasurable ?_).smul (hG.comp_measurable
      (by fun_prop : Continuous fun q : (H × ℝ) × ℝ => -(q.2 • q.1.1)).measurable)
    exact ((continuous_filterFourier ρ).comp continuous_snd).measurable.mul
      (by fun_prop : Continuous fun q : (H × ℝ) × ℝ =>
        Complex.exp ((q.2 * q.1.2 : ℝ) * Complex.I)).measurable
  exact hF.integral_prod_right'.const_smul _

omit [MeasurableSpace H] [BorelSpace H] in
/-- Parseval in the bias for the `Y`-valued coefficient: when the ray function is integrable,
`∫ ρ(u+c) • γ_G(a,c) dc = (2π)⁻¹ • ∫ (ρ̂(ω) ρ̂(-ω) e^{-iωu}) • G(-ωa) dω`. -/
theorem integral_smul_coefficientFormulaVec (ρ : SchwartzMap ℝ ℝ) (G : H → Y) (a : H) (u : ℝ)
    (ha : Integrable fun ω : ℝ => filterFourier ρ ω • G (-(ω • a))) :
    ∫ c, (ρ (u + c) : ℂ) • coefficientFormulaVec ρ G (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω, (filterFourier ρ ω *
        (filterFourier ρ (-ω) * Complex.exp (-((ω * u : ℝ) * Complex.I)))) • G (-(ω • a)) := by
  set Φ : ℝ → Y := fun ω => filterFourier ρ ω • G (-(ω • a)) with hΦ
  have hρu : Integrable fun c : ℝ => (ρ (u + c) : ℂ) := (ρ.integrable.comp_add_left u).ofReal
  have hint : Integrable (fun z : ℝ × ℝ =>
      ((ρ (u + z.1) : ℂ) * Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)) • Φ z.2)
      (volume.prod volume) := by
    have h1 := (hρu.smul_prod ha).smul_of_top_right (memLp_top_of_bound
      (by fun_prop : Continuous fun z : ℝ × ℝ =>
        Complex.exp ((z.2 * z.1 : ℝ) * Complex.I)).aestronglyMeasurable 1
      (Eventually.of_forall fun z => (Complex.norm_exp_ofReal_mul_I _).le))
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply', smul_smul, hΦ]
    congr 1
    ring
  have hL : ∀ c : ℝ, (ρ (u + c) : ℂ) • coefficientFormulaVec ρ G (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ ω, ((ρ (u + c) : ℂ) * Complex.exp ((ω * c : ℝ) * Complex.I)) • Φ ω := by
    intro c
    unfold coefficientFormulaVec
    rw [smul_comm, ← integral_smul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hΦ, smul_smul]
    congr 1
    ring
  simp_rw [hL]
  rw [integral_smul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [integral_smul_const, integral_shift_mul_exp, hΦ]
  beta_reduce
  rw [smul_smul]
  congr 1
  ring

/-- For `ν`-almost every direction, the bias integral of `γ_G` against the ridge function is
`(2π)⁻¹ • ∫ (ρ̂(ω) ρ̂(-ω) e^{i⟪x,-ωa⟫}) • G(-ωa) dω`. -/
theorem ae_integral_smul_coefficientFormulaVec_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) (x : H) :
    ∀ᵐ a ∂ν, ∫ c, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω, (filterFourier ρ ω * filterFourier ρ (-ω) *
        Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I)) • G (-(ω • a)) := by
  filter_upwards [ae_integrable_ray_vec hα hν hρ hG hG₂] with a ha
  rw [integral_smul_coefficientFormulaVec ρ G a ⟪a, x⟫ ha]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hphase : ((⟪x, -(ω • a)⟫ : ℝ) : ℂ) * Complex.I = -((ω * ⟪a, x⟫ : ℝ) * Complex.I) := by
    rw [inner_neg_right, inner_smul_right, real_inner_comm]
    push_cast
    ring
  beta_reduce
  rw [hphase]
  congr 1
  ring

omit [CompleteSpace Y] in
/-- The `Y`-valued synthesis kernel `(a, ω) ↦ (ρ̂(ω) ρ̂(-ω) e^{i⟪x,-ωa⟫}) • G(-ωa)` is integrable
on `ν ⊗ dω` for `G ∈ L¹(ν; Y)`. -/
theorem integrable_synthesis_kernel_vec (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ)
    (hG : StronglyMeasurable G) (hG₁ : Integrable G ν) (x : H) :
    Integrable (fun p : H × ℝ => (filterFourier ρ p.2 * filterFourier ρ (-p.2) *
      Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I)) • G (-(p.2 • p.1))) (ν.prod volume) := by
  have hc : Continuous fun p : H × ℝ => -(p.2 • p.1) := by fun_prop
  refine ⟨?_, ?_⟩
  · exact ((((continuous_filterFourier ρ).comp continuous_snd).mul
      ((continuous_filterFourier ρ).comp continuous_snd.neg)).mul
      (by fun_prop : Continuous fun p : H × ℝ =>
        Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I))).measurable.stronglyMeasurable.smul
      (hG.comp_measurable hc.measurable) |>.aestronglyMeasurable
  · rw [HasFiniteIntegral]
    have hnorm : ∀ p : H × ℝ, ‖(filterFourier ρ p.2 * filterFourier ρ (-p.2) *
        Complex.exp ((⟪x, -(p.2 • p.1)⟫ : ℝ) * Complex.I)) • G (-(p.2 • p.1))‖ₑ =
        ‖filterFourier ρ p.2‖ₑ ^ 2 * ‖G (-(p.2 • p.1))‖ₑ := by
      intro p
      rw [enorm_smul, enorm_mul, enorm_mul, filterFourier_neg, RCLike.enorm_conj,
        Complex.enorm_exp_ofReal_mul_I, mul_one, sq]
    simp_rw [hnorm]
    rw [hν.lintegral_prod_neg_smul (K := fun ω => ‖filterFourier ρ ω‖ₑ ^ 2)
      ((continuous_filterFourier ρ).measurable.enorm.pow_const 2) hG.enorm,
      hρ.lintegral_enorm_sq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp hG₁.hasFiniteIntegral)

omit [CompleteSpace Y] in
/-- For `ν`-almost every direction, `c ↦ ρ(⟪a,x⟫ + c) • γ_G(a,c)` is integrable. -/
theorem ae_integrable_smul_coefficientFormulaVec_ridge (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G) (hG₂ : MemLp G 2 ν) (x : H) :
    ∀ᵐ a ∂ν, Integrable fun c : ℝ => (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c) := by
  filter_upwards [ae_integrable_ray_vec hα hν hρ hG hG₂] with a ha
  have hρx : Integrable fun c : ℝ => (ρ (⟪a, x⟫ + c) : ℂ) :=
    (ρ.integrable.comp_add_left ⟪a, x⟫).ofReal
  have hmeas : AEStronglyMeasurable (fun c : ℝ => coefficientFormulaVec ρ G (a, c)) volume :=
    ((stronglyMeasurable_coefficientFormulaVec ρ hG).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine hρx.smul_of_top_left (memLp_top_of_bound hmeas
    ((2 * Real.pi)⁻¹ * ∫ ω, ‖filterFourier ρ ω • G (-(ω • a))‖)
    (Eventually.of_forall fun c => ?_))
  unfold coefficientFormulaVec
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The outer integrand `a ↦ ∫ ρ(⟪a,x⟫ + c) • γ_G(a,c) dc` is `ν`-integrable. -/
theorem integrable_integral_smul_coefficientFormulaVec_ridge (hα : 0 < α)
    (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G)
    (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) (x : H) :
    Integrable (fun a : H =>
      ∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ν := by
  have hint := (integrable_synthesis_kernel_vec hν hρ hG hG₁ x).integral_prod_left
  refine (hint.smul ((2 * Real.pi)⁻¹ : ℝ)).congr ?_
  filter_upwards [ae_integral_smul_coefficientFormulaVec_ridge hα hν hρ hG hG₂ x] with a ha
  rw [Pi.smul_apply, ha]

/-- **Spectral synthesis identity for `Y`-valued densities**: for `G ∈ L¹(ν; Y) ∩ L²(ν; Y)`,
`∫ [∫ ρ(⟪a,x⟫+c) • γ_G(a,c) dc] ν(da) = C^{(α)}_ρ • g_G(x)`. -/
theorem integral_integral_smul_coefficientFormulaVec_ridge (hα : 0 < α)
    (hν : IsHomogeneous α ν) (hρ : IsAdmissible α ρ) (hG : StronglyMeasurable G)
    (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) (x : H) :
    ∫ a, (∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
      (admissibilityConst α ρ : ℂ) • spectralTarget ν G x := by
  have hint := integrable_synthesis_kernel_vec hν hρ hG hG₁ x
  have hFmeas : StronglyMeasurable fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ :=
    (by fun_prop : Continuous fun ξ : H =>
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).measurable.stronglyMeasurable.smul hG
  have hint' : Integrable (fun p : H × ℝ => (filterFourier ρ p.2 * filterFourier ρ (-p.2)) •
      (fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) (-(p.2 • p.1)))
      (ν.prod volume) := by
    refine hint.congr (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [smul_smul]
  have hsep := hν.integral_prod_neg_smul_vec
    (K := fun ω => filterFourier ρ ω * filterFourier ρ (-ω))
    (F := fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) hFmeas hint'
  calc ∫ a, (∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν
      = ∫ a : H, (((2 * Real.pi)⁻¹ : ℝ) • ∫ ω : ℝ, (filterFourier ρ ω * filterFourier ρ (-ω) *
          Complex.exp ((⟪x, -(ω • a)⟫ : ℝ) * Complex.I)) • G (-(ω • a))) ∂ν :=
        integral_congr_ae (ae_integral_smul_coefficientFormulaVec_ridge hα hν hρ hG hG₂ x)
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ p : H × ℝ, (filterFourier ρ p.2 * filterFourier ρ (-p.2)) •
          (fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) (-(p.2 • p.1))
          ∂ν.prod volume := by
        rw [integral_smul, integral_prod _ hint']
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun a => ?_)
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        beta_reduce
        rw [smul_smul]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ((∫ ω : ℝ, filterFourier ρ ω * filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ)) •
            ∫ ξ : H, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ ∂ν) := by
        rw [hsep]
    _ = (admissibilityConst α ρ : ℂ) • spectralTarget ν G x := by
        have hC := crossAdmissibilityConst_self α ρ
        unfold crossAdmissibilityConst at hC
        simp_rw [← filterFourier_neg] at hC
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
        congr 1

omit [CompleteSpace Y] in
/-- When `γ_G ∈ L¹(λ; Y)`, the iterated integral is the `Y`-valued integral network. -/
theorem integral_integral_coefficientFormulaVec_eq_integralNetworkDensity
    (hγ : Integrable (coefficientFormulaVec ρ G) (parameterMeasure ν)) (x : H) :
    ∫ a, (∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
      integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
        (coefficientFormulaVec ρ G) x := by
  obtain ⟨C, hC⟩ := ρ.decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC
  have hint : Integrable (fun θ : H × ℝ => (ρ (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G θ)
      (parameterMeasure ν) :=
    hγ.smul_of_top_right (memLp_top_of_bound (Complex.continuous_ofReal.comp (ρ.continuous.comp
      (by fun_prop : Continuous fun θ : H × ℝ => ⟪θ.1, x⟫ + θ.2))).aestronglyMeasurable C
      (Eventually.of_forall fun θ => by rw [Complex.norm_real]; exact hC.2 _))
  unfold integralNetworkDensity parameterMeasure
  rw [integral_prod _ hint]

end VectorSynthesis

end OperatorRidgelet
