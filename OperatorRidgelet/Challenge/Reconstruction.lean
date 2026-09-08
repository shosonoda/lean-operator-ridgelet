import OperatorRidgelet.Reconstruction.Defs

/-!
# comparator challenge: Section 4 (representation and reconstruction) and Appendix B

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Reconstruction`.  This
module imports only definition modules, never `OperatorRidgelet.Paper`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Definition `def:ray-regular` -/

/-- **Definition [def:ray-regular]** Regularity along rays.  A density that is regular along
rays belongs to `L¹(ν_α) ∩ L²(ν_α)` (homogeneity with a fixed `ω ∈ I`). -/
theorem def_ray_regular (ν : Measure H) [SigmaFinite ν] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    Integrable G ν ∧ MemLp G 2 ν := by
  sorry

/-! ### Theorem `thm:A` -/

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For
`G ∈ L¹(ν_α)` the target `g_G` is bounded by `‖G‖_{L¹(ν_α)}`. -/
theorem thm_A_i_a (ν : Measure H) (G : H → ℂ) (hG : Measurable G) (hG₁ : Integrable G ν) :
    ∀ x : H, ‖spectralTarget ν G x‖ ≤ ∫ ξ, ‖G ξ‖ ∂ν := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For
`G ∈ L¹(ν_α)` the target `g_G` is continuous. -/
theorem thm_A_i_b (ν : Measure H) (G : H → ℂ) (hG : Measurable G) (hG₁ : Integrable G ν) :
    Continuous (spectralTarget ν G) := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For
`G ∈ L¹(ν_α)`, `g_G = 0` only if `G = 0` `ν_α`-almost everywhere. -/
theorem thm_A_i_c (ν : Measure H) (G : H → ℂ) (hG : Measurable G) (hG₁ : Integrable G ν)
    (h : spectralTarget ν G = 0) :
    G =ᵐ[ν] 0 := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For
`G ∈ L¹(ν_α) ∩ L²(ν_α)` and every `x`, the iterated integral
`∫ [∫ γ_G(a,c) ρ(⟨a,x⟩+c) dc] ν_α(da)` converges absolutely: the inner integral converges
absolutely for `ν_α`-almost every `a`, and the outer integrand is `ν_α`-integrable. -/
theorem thm_A_ii_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    ∀ x : H,
      (∀ᵐ a ∂ν, Integrable fun c : ℝ => coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∧
        Integrable
          (fun a : H => ∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ν := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For
`G ∈ L¹(ν_α) ∩ L²(ν_α)` the spectral synthesis identity
`∫ [∫ γ_G(a,c) ρ(⟨a,x⟩+c) dc] ν_α(da) = C^{(α)}_ρ g_G(x)` holds for every `x`. -/
theorem thm_A_ii_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∂ν =
        admissibilityConst α ρ * spectralTarget ν G x := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  If moreover
`γ_G ∈ L¹(λ_α)`, the left side of the spectral synthesis identity is the integral network
`S_ρ[γ_G λ_α](x)`. -/
theorem thm_A_ii_c (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν)
    (hγ : Integrable (coefficientFormula ρ G) (parameterMeasure ν)) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (ρ (⟪a, x⟫ + c) : ℂ)) ∂ν =
        integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
          (coefficientFormula ρ G) x := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For a
tempered `β` that is a continuous function `b` of polynomial growth and not a polynomial, and
`G` regular along rays, the inner integral `∫ γ_G(a,c) β(⟨a,x⟩+c) dc` converges absolutely for
`ν_α`-almost every `a`. -/
theorem thm_A_iii_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → ℂ)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H, ∀ᵐ a ∂ν,
      Integrable fun c : ℝ => coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ) := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For a
tempered `β` that is a continuous function `b` of polynomial growth and not a polynomial, and
`G` regular along rays, the `ν_α`-integral of the inner integral converges absolutely. -/
theorem thm_A_iii_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → ℂ)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H,
      Integrable
        (fun a : H => ∫ c : ℝ, coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ)) ν := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For a
tempered `β` that is a continuous function `b` of polynomial growth and not a polynomial, and
`G` regular along rays, the tempered spectral synthesis identity
`∫ [∫ γ_G(a,c) β(⟨a,x⟩+c) dc] ν_α(da) = C^{(α)}_{β,ρ} g_G(x)` holds. -/
theorem thm_A_iii_c (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → ℂ)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ)) ∂ν =
        temperedAdmissibilityConst α β ρ * spectralTarget ν G x := by
  sorry

/-- **Theorem [thm:A]** Integral representation of targets with a spectral density.  For every
tempered `β` that is a continuous function of polynomial growth and not a polynomial, there is a
band-pass filter `ρ` with `C^{(α)}_{β,ρ} ≠ 0`. -/
theorem thm_A_iii_d {α : ℝ} (hα : 0 < α) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α β ρ ≠ 0 := by
  sorry

/-! ### Theorem `thm:C` -/

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The frame operator
`T_α = U_α' U_α` equals the Riesz map `J_α`. -/
theorem thm_C_i_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRange μ ν, frameOperator μ ν f = rieszMap μ ν f := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The Riesz map `J_α` (hence the
frame operator) is an isometry `𝓔_α → 𝓔_α'`. -/
theorem thm_C_i_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    Isometry (rieszMap μ ν) := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The Riesz map `J_α` (hence the
frame operator) is a bijection `𝓔_α → 𝓔_α'`. -/
theorem thm_C_i_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    Function.Bijective (rieszMap μ ν) := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The frame identity
`S_ρ R_ρ f = C^{(α)}_ρ T_α f` for `f ∈ 𝓔_α`. -/
theorem thm_C_i_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRange μ ν,
      synthesis μ ν ρ (ridgeletExtension μ ν ρ f) =
        (admissibilityConst α ρ : ℂ) • frameOperator μ ν f := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The first reconstruction
formula `f = (C^{(α)}_ρ)⁻¹ T_α⁻¹ S_ρ R_ρ f` for `f ∈ 𝓔_α` (`T_α⁻¹ = J_α⁻¹` by part (i)). -/
theorem thm_C_ii_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRange μ ν,
      f = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        rieszInv μ ν (synthesis μ ν ρ (ridgeletExtension μ ν ρ f)) := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The second reconstruction
formula `g = (C^{(α)}_ρ)⁻¹ S_ρ (R_ρ T_α⁻¹ g)` for `g ∈ 𝓔_α'`. -/
theorem thm_C_ii_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ g : SpectralAntiDual μ ν,
      g = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        synthesis μ ν ρ (ridgeletExtension μ ν ρ (rieszInv μ ν g)) := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  If `f ∈ 𝒟_α` and
`𝒢_Q f ∈ L¹(ν_α)`, then `T_α f` is represented by the bounded continuous function
`g_{𝒢_Q f}`: `T_α f [g] = ∫ g_{𝒢_Q f}(x) conj(g(x)) μ_Q(dx)` for `g ∈ 𝒟_α`. -/
theorem thm_C_iii_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (f : spectralCore μ ν) (hG : Integrable (gaussFourier μ f) ν) :
    ∀ g : spectralCore μ ν,
      frameOperator μ ν (spectralEmbed μ ν f) (spectralEmbed μ ν g) =
        ∫ x, spectralTarget ν (gaussFourier μ f) x * (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  Conversely, for `G ∈ 𝒦_α` the
functional `U_α' G ∈ 𝓔_α'` satisfies `R_ρ T_α⁻¹ U_α' G = W_ρ G`. -/
theorem thm_C_iii_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRange μ ν,
      ridgeletExtension μ ν ρ (rieszInv μ ν (transposeEmbed μ ν G)) =
        spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ) := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  When `G ∈ 𝒦_α ∩ L¹(ν_α)`, the
functional `U_α' G` is represented by `g_G`: `U_α' G [g] = ∫ g_G(x) conj(g(x)) μ_Q(dx)` for
`g ∈ 𝒟_α`. -/
theorem thm_C_iii_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRange μ ν, Integrable ((G : Lp ℂ 2 ν) : H → ℂ) ν →
      ∀ g : spectralCore μ ν,
        transposeEmbed μ ν G (spectralEmbed μ ν g) =
          ∫ x, spectralTarget ν ((G : Lp ℂ 2 ν) : H → ℂ) x * (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x)
            ∂μ := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  For `G ∈ 𝒦_α` the second
reconstruction formula applied to `U_α' G` reads `U_α' G = (C^{(α)}_ρ)⁻¹ S_ρ W_ρ G`. -/
theorem thm_C_iii_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRange μ ν,
      transposeEmbed μ ν G = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        synthesis μ ν ρ (spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ)) := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  When `G ∈ 𝒦_α ∩ L¹(ν_α)` and
`γ_G ∈ L¹(λ_α)`, the second reconstruction formula for `U_α' G` is the spectral synthesis
identity: paired with `g ∈ 𝒟_α`, `U_α' G [g] = (C^{(α)}_ρ)⁻¹ ∫ S_ρ[γ_G λ_α](x) conj(g(x)) μ_Q(dx)`
(Lemma `lem:weak-equals-strong`). -/
theorem thm_C_iii_e (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRange μ ν, Integrable ((G : Lp ℂ 2 ν) : H → ℂ) ν →
      Integrable (coefficientFormula ρ ((G : Lp ℂ 2 ν) : H → ℂ)) (parameterMeasure ν) →
      ∀ g : spectralCore μ ν,
        transposeEmbed μ ν G (spectralEmbed μ ν g) =
          (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) *
            ∫ x, integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ ((G : Lp ℂ 2 ν) : H → ℂ)) x *
              (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The backprojection `Λ_ρ` is a
bounded operator `L²(λ_α) → L²(ν_α)`: `Λ_ρ γ` is square integrable with
`‖Λ_ρ γ‖²_{L²(ν_α)} ≤ M ‖γ‖²_{L²(λ_α)}` for a constant `M`. -/
theorem thm_C_iv_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∃ M : ℝ, ∀ γ : Lp ℂ 2 (parameterMeasure ν),
      MemLp (backprojection α ν ρ γ) 2 ν ∧
        ∫ ξ, ‖backprojection α ν ρ γ ξ‖ ^ 2 ∂ν ≤ M * ‖γ‖ ^ 2 := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  `Λ_ρ W_ρ = C^{(α)}_ρ Id` on
`L²(ν_α)`. -/
theorem thm_C_iv_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α)
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ F : H → ℂ, Measurable F → MemLp F 2 ν →
      backprojection α ν ρ (spectralCoefficient ν ρ F) =ᵐ[ν]
        fun ξ => admissibilityConst α ρ * F ξ := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  For `f ∈ 𝒟_α` the identity
`Λ_ρ R_ρ f = C^{(α)}_ρ 𝒢_Q f` holds pointwise in `ξ`, with `Λ_ρ` computed from the continuous
Fourier-slice representative `(a,ω) ↦ \widehat{R_ρ f}(a,ω)` of the transform. -/
theorem thm_C_iv_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (f : spectralCore μ ν) :
    ∀ ξ : H,
      backprojectionOf α ρ (biasFourier (ridgelet μ ρ f)) ξ =
        admissibilityConst α ρ * gaussFourier μ f ξ := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The Hermite inversion formula
`E_{μ_Q}[f He_n(⟨x,ξ⟩/τ(ξ))] = i^n τ(ξ)^{-n} (d/dt)^n (e^{t²τ(ξ)²/2} 𝒢_Q f(tξ))|_{t=0}`,
`τ(ξ) = ⟨Qξ,ξ⟩^{1/2}`, for `f ∈ 𝒟_α` and `ξ ≠ 0`. -/
theorem thm_C_iv_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) (f : spectralCore μ ν) :
    ∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ,
      hermiteCoefficient μ Q f ξ n =
        Complex.I ^ n / ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ^ n *
          iteratedDeriv n (fun t : ℝ => hermiteExtension μ Q f ξ t) 0 := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  The Hermite coefficients over all
`ξ ≠ 0` and `n` determine `f ∈ 𝒟_α` in `L²(μ_Q)`. -/
theorem thm_C_iv_e (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) :
    ∀ f g : spectralCore μ ν,
      (∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ, hermiteCoefficient μ Q f ξ n = hermiteCoefficient μ Q g ξ n) →
        f = g := by
  sorry

/-- **Theorem [thm:C]** Reconstruction and the frame operator.  Reconstruction by
backprojection: `f = Δ_Q[(C^{(α)}_ρ)⁻¹ Λ_ρ R_ρ f]` for `f ∈ 𝒟_α`, with `Δ_Q` the inverse of
`𝒢_Q` on its range on `𝒟_α`. -/
theorem thm_C_iv_f (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) (f : spectralCore μ ν) :
    gaussFourierInv μ ν
        (fun ξ => (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) *
          backprojectionOf α ρ (biasFourier (ridgelet μ ρ f)) ξ) =
      (f : Lp ℂ 2 μ) := by
  sorry

/-! ### Lemma `lem:weak-equals-strong` -/

/-- **Lemma [lem:weak-equals-strong]** Synthesis of an integrable coefficient is the integral
network.  For real Schwartz `ρ` and `γ ∈ L¹(λ_α) ∩ L²(λ_α)`, the integral network
`S_ρ[γ λ_α]` is a bounded Borel function on `H`. -/
theorem lem_weak_equals_strong_i (ν : Measure H) [SigmaFinite ν] (ρ : SchwartzMap ℝ ℝ)
    (γ : Lp ℂ 2 (parameterMeasure ν)) (hγ : Integrable γ (parameterMeasure ν)) :
    Measurable (integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν) γ) ∧
      ∃ M : ℝ, ∀ x : H,
        ‖integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν) γ x‖ ≤ M := by
  sorry

/-- **Lemma [lem:weak-equals-strong]** Synthesis of an integrable coefficient is the integral
network.  For every `g ∈ 𝒟_α`, the synthesis functional `(S_ρ γ)[g] = ⟨γ, R_ρ g⟩_{L²(λ_α)}`
of `eq:weak-synthesis` equals `∫ S_ρ[γ λ_α](x) conj(g(x)) μ_Q(dx)`. -/
theorem lem_weak_equals_strong_ii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    (ρ : SchwartzMap ℝ ℝ) (γ : Lp ℂ 2 (parameterMeasure ν))
    (hγ : Integrable γ (parameterMeasure ν)) :
    ∀ g : spectralCore μ ν,
      ∫ p, γ p * (starRingEnd ℂ) (ridgelet μ ρ g p) ∂parameterMeasure ν =
        ∫ x, integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν) γ x *
          (starRingEnd ℂ) ((g : Lp ℂ 2 μ) x) ∂μ := by
  sorry

/-! ### Lemma `lem:hermite-totality` -/

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
For `f ∈ L²(μ_Q)` and `ξ ≠ 0`, `z ↦ G_f(zξ) = e^{z²τ(ξ)²/2} 𝒢_Q f(zξ)` is entire. -/
theorem lem_hermite_totality_i {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (ξ : H) (hξ : ξ ≠ 0) :
    Differentiable ℂ (hermiteExtension μ Q f ξ) := by
  sorry

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
The Hermite series `G_f(zξ) = ∑ₙ (-izτ(ξ))^n/n! E_{μ_Q}[f He_n(⟨x,ξ⟩/τ(ξ))]` converges for every
`z`. -/
theorem lem_hermite_totality_ii {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∀ z : ℂ,
      HasSum
        (fun n : ℕ => (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))) ^ n / (n.factorial : ℂ) *
          hermiteCoefficient μ Q f ξ n)
        (hermiteExtension μ Q f ξ z) := by
  sorry

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
The Hermite series converges locally uniformly in `z`. -/
theorem lem_hermite_totality_iii {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (ξ : H) (hξ : ξ ≠ 0) :
    TendstoLocallyUniformly
      (fun N : ℕ => fun z : ℂ => ∑ n ∈ Finset.range N,
        (-(Complex.I * z * ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ))) ^ n / (n.factorial : ℂ) *
          hermiteCoefficient μ Q f ξ n)
      (hermiteExtension μ Q f ξ) atTop := by
  sorry

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
The bound `|G_f(zξ)| ≤ ‖f‖_{L²(μ_Q)} e^{|z|²τ(ξ)²/2}`. -/
theorem lem_hermite_totality_iv {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∀ z : ℂ,
      ‖hermiteExtension μ Q f ξ z‖ ≤
        Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.exp (‖z‖ ^ 2 * ⟪Q ξ, ξ⟫ / 2) := by
  sorry

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
The Hermite inversion formula `eq:hermite-inversion` holds for `f ∈ L²(μ_Q)` and `ξ ≠ 0`. -/
theorem lem_hermite_totality_v {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∀ n : ℕ,
      hermiteCoefficient μ Q f ξ n =
        Complex.I ^ n / ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ^ n *
          iteratedDeriv n (fun t : ℝ => hermiteExtension μ Q f ξ t) 0 := by
  sorry

/-- **Lemma [lem:hermite-totality]** Entire extension and totality of the Hermite coefficients.
The Hermite coefficients over all `ξ ≠ 0` and `n` determine `f` in `L²(μ_Q)`. -/
theorem lem_hermite_totality_vi {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : H → ℂ) (hf : MemLp f 2 μ) :
    ∀ g : H → ℂ, MemLp g 2 μ →
      (∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ, hermiteCoefficient μ Q f ξ n = hermiteCoefficient μ Q g ξ n) →
        f =ᵐ[μ] g := by
  sorry

/-! ### Proposition `prop:coefficient-projection` -/

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  For `γ ∈ L²(λ_α)` and a jointly measurable partial bias-Fourier representative
`Φ` of `γ`, the ray-average integral `eq:ray-average` converges absolutely for `ν_α`-almost
every `ξ`. -/
theorem prop_coefficient_projection_i (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (γ : Lp ℂ 2 (parameterMeasure ν)) (Φ : H → ℝ → ℂ) (hΦ : Measurable (Function.uncurry Φ))
    (hγΦ : HasBiasFourier ν γ Φ) :
    ∀ᵐ ξ ∂ν,
      Integrable fun ω : ℝ =>
        (starRingEnd ℂ) (filterFourier ρ ω) * ((|ω| ^ (-α) : ℝ) : ℂ) * Φ (-(ω⁻¹ • ξ)) ω := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  As an `L²(ν_α)` class, `Λ_ρ γ` does not depend on the jointly measurable
Fourier representative of `γ`. -/
theorem prop_coefficient_projection_ii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (γ : Lp ℂ 2 (parameterMeasure ν)) (Φ Φ' : H → ℝ → ℂ) (hΦ : Measurable (Function.uncurry Φ))
    (hΦ' : Measurable (Function.uncurry Φ')) (hγΦ : HasBiasFourier ν γ Φ)
    (hγΦ' : HasBiasFourier ν γ Φ') :
    backprojectionOf α ρ Φ =ᵐ[ν] backprojectionOf α ρ Φ' := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  `Λ_ρ γ ∈ L²(ν_α)` with `‖Λ_ρ γ‖_{L²(ν_α)} ≤ √C ‖γ‖_𝒴`, `C = C^{(α)}_ρ`. -/
theorem prop_coefficient_projection_iii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∀ γ : Lp ℂ 2 (parameterMeasure ν),
      MemLp (backprojection α ν ρ γ) 2 ν ∧
        ∫ ξ, ‖backprojection α ν ρ γ ξ‖ ^ 2 ∂ν ≤ admissibilityConst α ρ * ‖γ‖ ^ 2 := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  `Λ_ρ` is the Hilbert adjoint of `W_ρ : L²(ν_α) → 𝒴`:
`⟨γ, W_ρ F⟩_{L²(λ_α)} = ⟨Λ_ρ γ, F⟩_{L²(ν_α)}`. -/
theorem prop_coefficient_projection_iv (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∀ (γ : Lp ℂ 2 (parameterMeasure ν)) (F : H → ℂ), Measurable F → MemLp F 2 ν →
      ∫ p, γ p * (starRingEnd ℂ) ((spectralCoefficient ν ρ F : H × ℝ → ℂ) p)
          ∂parameterMeasure ν =
        ∫ ξ, backprojection α ν ρ γ ξ * (starRingEnd ℂ) (F ξ) ∂ν := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  `Λ_ρ W_ρ = C Id`. -/
theorem prop_coefficient_projection_v (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∀ F : H → ℂ, Measurable F → MemLp F 2 ν →
      backprojection α ν ρ (spectralCoefficient ν ρ F) =ᵐ[ν]
        fun ξ => admissibilityConst α ρ * F ξ := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  `Π_ρ = C⁻¹ W_ρ P_{𝒦_α} Λ_ρ` is the orthogonal projection onto `Ran R_ρ`:
`Π_ρ γ ∈ Ran R_ρ` and `γ - Π_ρ γ ⊥ Ran R_ρ`. -/
theorem prop_coefficient_projection_vi (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∀ γ : Lp ℂ 2 (parameterMeasure ν),
      coefficientProjection α μ ν ρ γ ∈ ridgeletRange μ ν ρ ∧
        γ - coefficientProjection α μ ν ρ γ ∈ (ridgeletRange μ ν ρ)ᗮ := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  The minimum-norm solution of `S_ρ γ = F ∈ 𝓔_α'` is `C⁻¹ R_ρ J_α⁻¹ F`: it solves
the equation, and every solution has at least its norm. -/
theorem prop_coefficient_projection_vii (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∀ F : SpectralAntiDual μ ν,
      synthesis μ ν ρ
          ((((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • ridgeletExtension μ ν ρ (rieszInv μ ν F)) =
        F ∧
      ∀ γ : Lp ℂ 2 (parameterMeasure ν), synthesis μ ν ρ γ = F →
        ‖(((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • ridgeletExtension μ ν ρ (rieszInv μ ν F)‖ ≤
          ‖γ‖ := by
  sorry

/-- **Proposition [prop:coefficient-projection]** Bounded backprojection and orthogonal range
projection.  The solutions of `S_ρ γ = F` are exactly the coefficients that differ from the
minimum-norm solution by an element of `(Ran R_ρ)^⊥`. -/
theorem prop_coefficient_projection_viii (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∀ (F : SpectralAntiDual μ ν) (γ : Lp ℂ 2 (parameterMeasure ν)),
      synthesis μ ν ρ γ = F ↔
        γ - (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) • ridgeletExtension μ ν ρ (rieszInv μ ν F) ∈
          (ridgeletRange μ ν ρ)ᗮ := by
  sorry

/-! ### Lemma `lem:ray-regular-examples` -/

/-- **Lemma [lem:ray-regular-examples]** Densities that are regular along rays.  Gaussian-type
densities `G(ξ) = q(ξ) e^{-κ(ξ)/2}`, `κ(ξ) = ⟨Sξ,ξ⟩` with `S` a bounded positive operator with
`S ≥ θQ`, `θ > 0`, and `q` a polynomial in `κ(ξ)` and in finitely many bounded linear
functionals `ℓ_i` of `ξ` dominated by the quadratic form, `|ℓ_i(ξ)|² ≤ C_i κ(ξ)`, are regular
along rays for every band-pass `ρ` (and every frequency window of `ρ`). -/
theorem lem_ray_regular_examples_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (S : H →L[ℝ] H)
    (hS : IsSelfAdjoint S) {θ : ℝ} (hθ : 0 < θ) (hSQ : ∀ ξ, θ * ⟪Q ξ, ξ⟫ ≤ ⟪S ξ, ξ⟫) {k : ℕ}
    (ℓ : Fin k → (H →L[ℝ] ℝ)) (hℓ : ∀ i, ∃ C : ℝ, ∀ ξ, (ℓ i ξ) ^ 2 ≤ C * ⟪S ξ, ξ⟫)
    (q : MvPolynomial (Option (Fin k)) ℂ) :
    ∀ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ → ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      IsRegularAlongRays (gaussianMixture N α) I fun ξ =>
        MvPolynomial.eval (fun o : Option (Fin k) =>
            o.elim ((⟪S ξ, ξ⟫ : ℝ) : ℂ) fun i => ((ℓ i ξ : ℝ) : ℂ)) q *
          Complex.exp (-((⟪S ξ, ξ⟫ / 2 : ℝ) : ℂ)) := by
  sorry

/-- **Lemma [lem:ray-regular-examples]** Densities that are regular along rays.  Radial bumps
`G(ξ) = φ(‖ξ - ξ₀‖²)` with `φ ∈ C_c^∞(ℝ)` are regular along rays for every band-pass `ρ`. -/
theorem lem_ray_regular_examples_b_i (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) (ξ₀ : H) (φ : ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∀ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ → ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      IsRegularAlongRays (gaussianMixture N α) I fun ξ => φ (‖ξ - ξ₀‖ ^ 2) := by
  sorry

/-- **Lemma [lem:ray-regular-examples]** Densities that are regular along rays.  More generally,
a bounded Borel `G` that is `C^∞` along rays (on a neighbourhood of the frequency window),
vanishes outside a bounded set, and satisfies `sup_{ω ∈ I} |∂_ω^k G(ωa)| ≤ C_k (1+‖a‖)^{p_k}`
for all `k`, is regular along rays for every band-pass `ρ`. -/
theorem lem_ray_regular_examples_b_ii (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) (G : H → ℂ) (hG : Measurable G) (hGb : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M)
    (hG0 : ∃ R₀ : ℝ, ∀ ξ : H, R₀ < ‖ξ‖ → G ξ = 0) :
    ∀ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ → ∀ I : Set ℝ, IsFrequencyWindow ρ I →
      (∀ a : H, ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun ω : ℝ => G (ω • a)) U) →
      (∀ k : ℕ, ∃ C p : ℝ, ∀ a : H, ∀ ω ∈ I,
        ‖iteratedDeriv k (fun ω : ℝ => G (ω • a)) ω‖ ≤ C * (1 + ‖a‖) ^ p) →
      IsRegularAlongRays (gaussianMixture N α) I G := by
  sorry

/-- **Lemma [lem:ray-regular-examples]** Densities that are regular along rays.  Finite linear
combinations of densities that are regular along rays are regular along rays. -/
theorem lem_ray_regular_examples_c_i (ν : Measure H) (I : Set ℝ) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (G : ι → H → ℂ) (hG : ∀ i ∈ s, IsRegularAlongRays ν I (G i)) :
    IsRegularAlongRays ν I fun ξ => ∑ i ∈ s, c i * G i ξ := by
  sorry

/-- **Lemma [lem:ray-regular-examples]** Densities that are regular along rays.  Bochner
integrals `∫ G_y m(dy)` of a measurable family of densities that are regular along rays, over
a finite measure `m`, are regular along rays when the densities are uniformly bounded and the
weights of `eq:ray-regularity` have a `ν_α`-integrable majorant that is uniform in `y`. -/
theorem lem_ray_regular_examples_c_ii (ν : Measure H) (I : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m] (G : Ω → H → ℂ)
    (hGm : Measurable (Function.uncurry G)) (hG : ∀ y, IsRegularAlongRays ν I (G y))
    (hGb : ∃ M : ℝ, ∀ y ξ, ‖G y ξ‖ ≤ M)
    (hunif : ∀ k : ℕ, ∃ h : H → ℝ≥0∞,
      (∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ (k + 2)) * h a ∂ν) < ⊤ ∧
        ∀ y a, rayDerivBound I (G y) k a ≤ h a) :
    IsRegularAlongRays ν I fun ξ => ∫ y, G y ξ ∂m := by
  sorry

/-! ### Theorem `thm:vector-valued` -/

section VectorValued

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] [CompleteSpace Y]
  [SecondCountableTopology Y] in
/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(i) for `Y`-valued
densities: `‖g_G(x)‖_Y ≤ ‖G‖_{L¹(ν_α;Y)}`. -/
theorem thm_vector_valued_A_i_a (ν : Measure H) (G : H → Y) (hG : StronglyMeasurable G)
    (hG₁ : Integrable G ν) :
    ∀ x : H, ‖spectralTarget ν G x‖ ≤ ∫ ξ, ‖G ξ‖ ∂ν := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(i) for `Y`-valued
densities: `g_G` is continuous. -/
theorem thm_vector_valued_A_i_b (ν : Measure H) (G : H → Y) (hG : StronglyMeasurable G)
    (hG₁ : Integrable G ν) :
    Continuous (spectralTarget ν G) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(i) for `Y`-valued
densities: `g_G = 0` only if `G = 0` `ν_α`-almost everywhere. -/
theorem thm_vector_valued_A_i_c (ν : Measure H) (G : H → Y) (hG : StronglyMeasurable G)
    (hG₁ : Integrable G ν) (h : spectralTarget ν G = 0) :
    G =ᵐ[ν] 0 := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(ii) for `Y`-valued
densities: the iterated integral `∫ [∫ ρ(⟨a,x⟩+c) γ_G(a,c) dc] ν_α(da)` converges absolutely. -/
theorem thm_vector_valued_A_ii_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → Y)
    (hG : StronglyMeasurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    ∀ x : H,
      (∀ᵐ a ∂ν, Integrable fun c : ℝ =>
        (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∧
        Integrable
          (fun a : H => ∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ν := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(ii) for `Y`-valued
densities: the spectral synthesis identity with the same constant `C^{(α)}_ρ`. -/
theorem thm_vector_valued_A_ii_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → Y)
    (hG : StronglyMeasurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
        (admissibilityConst α ρ : ℂ) • spectralTarget ν G x := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(ii) for `Y`-valued
densities: if `γ_G ∈ L¹(λ_α; Y)`, the left side is the `Y`-valued integral network
`S_ρ[γ_G λ_α](x)`. -/
theorem thm_vector_valued_A_ii_c (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (G : H → Y)
    (hG : StronglyMeasurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν)
    (hγ : Integrable (coefficientFormulaVec ρ G) (parameterMeasure ν)) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, (ρ (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
        integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
          (coefficientFormulaVec ρ G) x := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(iii) for
`Y`-valued densities regular along rays (with `‖·‖_Y` in place of the absolute value): the
inner integral converges absolutely for `ν_α`-almost every `a`. -/
theorem thm_vector_valued_A_iii_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → Y)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H, ∀ᵐ a ∂ν,
      Integrable fun c : ℝ => (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(iii) for
`Y`-valued densities regular along rays: the outer integral converges absolutely. -/
theorem thm_vector_valued_A_iii_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → Y)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H,
      Integrable
        (fun a : H => ∫ c : ℝ, (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ν := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:A`(iii) for
`Y`-valued densities regular along rays: the tempered spectral synthesis identity with the
same constant `C^{(α)}_{β,ρ}`. -/
theorem thm_vector_valued_A_iii_c (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hb : ¬ IsPolynomialFun b) (G : H → Y)
    (hG : IsRegularAlongRays ν I G) :
    ∀ x : H,
      ∫ a, (∫ c : ℝ, (b (⟪a, x⟫ + c) : ℂ) • coefficientFormulaVec ρ G (a, c)) ∂ν =
        temperedAdmissibilityConst α β ρ • spectralTarget ν G x := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(i) for `Y`-valued
targets: `R_ρ f ∈ L²(λ_α; Y)` for `f ∈ 𝒟_α(Y)` and `α`-admissible `ρ`. -/
theorem thm_vector_valued_B_i_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : Lp Y 2 μ) (hf : f ∈ spectralCoreVec Y μ ν) :
    MemLp (ridgeletVec μ ρ f) 2 (parameterMeasure ν) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(i) for `Y`-valued
targets: the Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ_α;Y)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_α(Y)}`. -/
theorem thm_vector_valued_B_i_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂)
    (f g : Lp Y 2 μ) (hf : f ∈ spectralCoreVec Y μ ν) (hg : g ∈ spectralCoreVec Y μ ν) :
    ∫ p, inner ℂ (ridgeletVec μ ρ₂ g p) (ridgeletVec μ ρ₁ f p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInnerVec μ ν f g := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(ii) for
`Y`-valued targets: an `α`-admissible `ρ` determines a unique bounded extension
`R_ρ : 𝓔_α(Y) → L²(λ_α; Y)`. -/
theorem thm_vector_valued_B_ii_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRangeVec Y μ ν →L[ℂ] Lp Y 2 (parameterMeasure ν),
      ∀ f : spectralCoreVec Y μ ν,
        (R (spectralEmbedVec μ ν f) : H × ℝ → Y) =ᵐ[parameterMeasure ν] ridgeletVec μ ρ f := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(ii) for
`Y`-valued targets: `‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_α(Y)}`. -/
theorem thm_vector_valued_B_ii_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∀ G : spectralRangeVec Y μ ν,
      ‖ridgeletExtensionVec Y μ ν ρ G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(ii) for
`Y`-valued targets: the range of `R_ρ` is closed. -/
theorem thm_vector_valued_B_ii_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    IsClosed (Set.range (ridgeletExtensionVec Y μ ν ρ)) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(ii) for
`Y`-valued targets: `R_ρ = W_ρ U_α`. -/
theorem thm_vector_valued_B_ii_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∀ G : spectralRangeVec Y μ ν,
      ridgeletExtensionVec Y μ ν ρ G = spectralCoefficientVec ν ρ ((G : Lp Y 2 ν) : H → Y) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:B`(iii) for
`Y`-valued targets: `R_ρ f = 0` `λ_α`-a.e. implies `f = 0` `μ_Q`-a.e. for `f ∈ L²(μ_Q; Y)`. -/
theorem thm_vector_valued_B_iii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : H → Y) (hf : MemLp f 2 μ)
    (h : ridgeletVec μ ρ f =ᵐ[parameterMeasure ν] 0) :
    f =ᵐ[μ] 0 := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y] [SecondCountableTopology Y]
  in
/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(i) for `Y`-valued
targets: the frame operator `T_α = U_α' U_α` equals the Riesz map `J_α` of `𝓔_α(Y)`. -/
theorem thm_vector_valued_C_i_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRangeVec Y μ ν, frameOperatorVec μ ν f = rieszMapVec Y μ ν f := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] [CompleteSpace Y] [SecondCountableTopology Y]
  in
/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(i) for `Y`-valued
targets: the Riesz map of `𝓔_α(Y)` is an isometry. -/
theorem thm_vector_valued_C_i_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    Isometry (rieszMapVec Y μ ν) := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] [SecondCountableTopology Y] in
/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(i) for `Y`-valued
targets: the Riesz map of `𝓔_α(Y)` is a bijection onto `𝓔_α(Y)'`. -/
theorem thm_vector_valued_C_i_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    Function.Bijective (rieszMapVec Y μ ν) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(i) for `Y`-valued
targets: the frame identity `S_ρ R_ρ f = C^{(α)}_ρ T_α f`. -/
theorem thm_vector_valued_C_i_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRangeVec Y μ ν,
      synthesisVec μ ν ρ (ridgeletExtensionVec Y μ ν ρ f) =
        (admissibilityConst α ρ : ℂ) • frameOperatorVec μ ν f := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(ii) for
`Y`-valued targets: `f = (C^{(α)}_ρ)⁻¹ T_α⁻¹ S_ρ R_ρ f`. -/
theorem thm_vector_valued_C_ii_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ f : spectralRangeVec Y μ ν,
      f = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        rieszInvVec μ ν (synthesisVec μ ν ρ (ridgeletExtensionVec Y μ ν ρ f)) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(ii) for
`Y`-valued targets: `g = (C^{(α)}_ρ)⁻¹ S_ρ (R_ρ T_α⁻¹ g)` for `g ∈ 𝓔_α(Y)'`. -/
theorem thm_vector_valued_C_ii_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ g : SpectralAntiDualVec Y μ ν,
      g = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        synthesisVec μ ν ρ (ridgeletExtensionVec Y μ ν ρ (rieszInvVec μ ν g)) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iii) for
`Y`-valued targets: for `f ∈ 𝒟_α(Y)` with `𝒢_Q f ∈ L¹(ν_α; Y)`, `T_α f` is represented by
`g_{𝒢_Q f}`: `T_α f [g] = ∫ ⟨g_{𝒢_Q f}(x), g(x)⟩_Y μ_Q(dx)`. -/
theorem thm_vector_valued_C_iii_a (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (f : spectralCoreVec Y μ ν)
    (hG : Integrable (gaussFourierVec μ ((f : Lp Y 2 μ) : H → Y)) ν) :
    ∀ g : spectralCoreVec Y μ ν,
      frameOperatorVec μ ν (spectralEmbedVec μ ν f) (spectralEmbedVec μ ν g) =
        ∫ x, inner ℂ ((g : Lp Y 2 μ) x)
          (spectralTarget ν (gaussFourierVec μ ((f : Lp Y 2 μ) : H → Y)) x) ∂μ := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iii) for
`Y`-valued targets: `R_ρ T_α⁻¹ U_α' G = W_ρ G` for `G ∈ 𝒦_α(Y)`. -/
theorem thm_vector_valued_C_iii_b (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRangeVec Y μ ν,
      ridgeletExtensionVec Y μ ν ρ (rieszInvVec μ ν (transposeEmbedVec μ ν G)) =
        spectralCoefficientVec ν ρ ((G : Lp Y 2 ν) : H → Y) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iii) for
`Y`-valued targets: when `G ∈ 𝒦_α(Y) ∩ L¹(ν_α; Y)`, `U_α' G` is represented by `g_G`. -/
theorem thm_vector_valued_C_iii_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRangeVec Y μ ν, Integrable ((G : Lp Y 2 ν) : H → Y) ν →
      ∀ g : spectralCoreVec Y μ ν,
        transposeEmbedVec μ ν G (spectralEmbedVec μ ν g) =
          ∫ x, inner ℂ ((g : Lp Y 2 μ) x) (spectralTarget ν ((G : Lp Y 2 ν) : H → Y) x) ∂μ := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iii) for
`Y`-valued targets: `U_α' G = (C^{(α)}_ρ)⁻¹ S_ρ W_ρ G` for `G ∈ 𝒦_α(Y)`. -/
theorem thm_vector_valued_C_iii_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRangeVec Y μ ν,
      transposeEmbedVec μ ν G = (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
        synthesisVec μ ν ρ (spectralCoefficientVec ν ρ ((G : Lp Y 2 ν) : H → Y)) := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iii) for
`Y`-valued targets: when `G ∈ 𝒦_α(Y) ∩ L¹(ν_α; Y)` and `γ_G ∈ L¹(λ_α; Y)`, the second
reconstruction formula for `U_α' G` is the spectral synthesis identity paired with
`g ∈ 𝒟_α(Y)`. -/
theorem thm_vector_valued_C_iii_e (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) :
    ∀ G : spectralRangeVec Y μ ν, Integrable ((G : Lp Y 2 ν) : H → Y) ν →
      Integrable (coefficientFormulaVec ρ ((G : Lp Y 2 ν) : H → Y)) (parameterMeasure ν) →
      ∀ g : spectralCoreVec Y μ ν,
        transposeEmbedVec μ ν G (spectralEmbedVec μ ν g) =
          (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) *
            ∫ x, inner ℂ ((g : Lp Y 2 μ) x)
              (integralNetworkDensity (fun t => (ρ t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ ((G : Lp Y 2 ν) : H → Y)) x) ∂μ := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: the backprojection `Λ_ρ` is a bounded operator
`L²(λ_α; Y) → L²(ν_α; Y)`. -/
theorem thm_vector_valued_C_iv_a (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∃ M : ℝ, ∀ γ : Lp Y 2 (parameterMeasure ν),
      MemLp (backprojectionVec α ν ρ γ) 2 ν ∧
        ∫ ξ, ‖backprojectionVec α ν ρ γ ξ‖ ^ 2 ∂ν ≤ M * ‖γ‖ ^ 2 := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: `Λ_ρ W_ρ = C^{(α)}_ρ Id` on `L²(ν_α; Y)`. -/
theorem thm_vector_valued_C_iv_b (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ F : H → Y, StronglyMeasurable F → MemLp F 2 ν →
      backprojectionVec α ν ρ (spectralCoefficientVec ν ρ F) =ᵐ[ν]
        fun ξ => (admissibilityConst α ρ : ℂ) • F ξ := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: `Λ_ρ R_ρ f = C^{(α)}_ρ 𝒢_Q f` pointwise for `f ∈ 𝒟_α(Y)`, with `Λ_ρ`
computed from the Fourier-slice representative of `R_ρ f`. -/
theorem thm_vector_valued_C_iv_c (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (f : spectralCoreVec Y μ ν) :
    ∀ ξ : H,
      backprojectionOfVec α ρ (biasFourierVec (ridgeletVec μ ρ ((f : Lp Y 2 μ) : H → Y))) ξ =
        (admissibilityConst α ρ : ℂ) • gaussFourierVec μ ((f : Lp Y 2 μ) : H → Y) ξ := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: the Hermite inversion formula, applied componentwise, for `f ∈ 𝒟_α(Y)` and
`ξ ≠ 0`. -/
theorem thm_vector_valued_C_iv_d (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) (f : spectralCoreVec Y μ ν) :
    ∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ,
      hermiteCoefficientVec μ Q ((f : Lp Y 2 μ) : H → Y) ξ n =
        (Complex.I ^ n / ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ^ n) •
          iteratedDeriv n
            (fun t : ℝ => hermiteExtensionVec μ Q ((f : Lp Y 2 μ) : H → Y) ξ t) 0 := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: the Hermite coefficients over all `ξ ≠ 0` and `n` determine
`f ∈ 𝒟_α(Y)` in `L²(μ_Q; Y)`. -/
theorem thm_vector_valued_C_iv_e (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) :
    ∀ f g : spectralCoreVec Y μ ν,
      (∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ,
        hermiteCoefficientVec μ Q ((f : Lp Y 2 μ) : H → Y) ξ n =
          hermiteCoefficientVec μ Q ((g : Lp Y 2 μ) : H → Y) ξ n) →
        f = g := by
  sorry

/-- **Theorem [thm:vector-valued]** Vector-valued extension.  Theorem `thm:C`(iv) for
`Y`-valued targets: `f = Δ_Q[(C^{(α)}_ρ)⁻¹ Λ_ρ R_ρ f]` for `f ∈ 𝒟_α(Y)`. -/
theorem thm_vector_valued_C_iv_f (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) (f : spectralCoreVec Y μ ν) :
    gaussFourierInvVec μ ν
        (fun ξ => (((admissibilityConst α ρ)⁻¹ : ℝ) : ℂ) •
          backprojectionOfVec α ρ (biasFourierVec (ridgeletVec μ ρ ((f : Lp Y 2 μ) : H → Y))) ξ) =
      (f : Lp Y 2 μ) := by
  sorry

end VectorValued

end OperatorRidgelet.Paper
