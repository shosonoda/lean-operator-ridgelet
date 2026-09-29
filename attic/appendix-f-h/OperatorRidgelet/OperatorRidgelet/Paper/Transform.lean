/-! Historical fragments; see the archive README for their original context. -/

/-! ### Theorem `thm:H.1` -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(i) for the
abstract pair: `R_ρ f ∈ L²(λ)` for `f ∈ 𝒟_{μ,ν}` and `α`-admissible `ρ`. -/
theorem thm_H_1_plancherel_memLp (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure ν) :=
  memLp_ridgelet μ hν hρ ((Lp.memLp f).integrable one_le_two) (Lp.memLp f) hf

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(i) for the
abstract pair: the Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_{μ,ν}}`. -/
theorem thm_H_1_plancherel (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂)
    (f g : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) (hg : g ∈ spectralCore μ ν) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ ν f g :=
  integral_ridgelet_mul_conj μ hν hρ₁ hρ₂ ((Lp.memLp f).integrable one_le_two) (Lp.memLp f)
    ((Lp.memLp g).integrable one_le_two) (Lp.memLp g) hf hg

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(ii) for the
abstract pair: the unique bounded extension `R_ρ : 𝓔_{μ,ν} → L²(λ)`. -/
theorem thm_H_1_extension (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f :=
  existsUnique_ridgeletExtensionCLM hν hρ

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(ii) for the
abstract pair: `‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_{μ,ν}}`. -/
theorem thm_H_1_extension_norm (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, ‖R G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  intro G
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact norm_ridgeletExtensionCLM_sq hν hρ G

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(ii) for the
abstract pair: the extension has closed range. -/
theorem thm_H_1_extension_closed_range (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    IsClosed (Set.range R) := by
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact isClosed_range_ridgeletExtensionCLM hν hρ

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(ii) for the
abstract pair: `R_ρ = W_ρ U`. -/
theorem thm_H_1_extension_coefficient (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, R G = spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ) := by
  intro G
  rw [eq_ridgeletExtensionCLM hν hρ R hR]
  exact ridgeletExtensionCLM_eq_spectralCoefficient hν hα hρ μ G

/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  Theorem
`thm:3.11`(iii) for the
abstract pair: `R_ρ f = 0` `λ`-a.e. implies `f = 0` `μ`-a.e. for `f ∈ L²(μ)`. -/
theorem thm_H_1_injective (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure ν] 0) :
    f =ᵐ[μ] 0 :=
  ae_eq_zero_of_ridgelet_ae_eq_zero μ hα hν hρ (hf.integrable one_le_two) h

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Theorem [thm:H.1]** Extension to general input and direction measures.  `1 ∈
𝒟_{μ,ν}` if and only if
`∫ |μ̂(ξ)|² ν(dξ) < ∞`. -/
theorem thm_H_1_one_mem_iff (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) :
    MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) ∈ spectralCore μ ν ↔
      Integrable (fun ξ : H => ‖charFun μ ξ‖ ^ 2) ν := by
  rw [mem_spectralCore_iff]
  have h1 : gaussFourier μ
      ((MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) : Lp ℂ 2 μ) : H → ℂ) =
      fun ξ => charFun μ (-ξ) := by
    funext ξ
    rw [← gaussFourier_one]
    simp only [gaussFourier]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := μ) (p := 2))] with x hx
    rw [hx]
  have h2 : (fun ξ : H => ‖charFun μ (-ξ)‖ ^ 2) = fun ξ => ‖charFun μ ξ‖ ^ 2 := by
    funext ξ
    rw [charFun_neg, Complex.norm_conj]
  rw [h1, memLp_two_iff_integrable_sq_norm (f := fun ξ => charFun μ (-ξ))
    (stronglyMeasurable_charFun.comp_measurable measurable_neg).aestronglyMeasurable, h2]
