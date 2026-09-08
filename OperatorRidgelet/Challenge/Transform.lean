import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.FiniteDim.Defs
import OperatorRidgelet.Filters.Defs

/-!
# comparator challenge: Section 3 (the ridgelet transform) and Appendices A, G, H, I

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Transform`.
-/

noncomputable section

namespace OperatorRidgelet.Paper
open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Lemma `lem:homogeneous-mixture` -/

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  In infinite dimension the
mixture `ν_α` is σ-finite. -/
theorem lem_homogeneous_mixture_i (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    SigmaFinite (gaussianMixture N α) := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` is
finite on bounded Borel sets. -/
theorem lem_homogeneous_mixture_ii (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E → Bornology.IsBounded E → gaussianMixture N α E < ⊤ := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` is
infinite on `H`. -/
theorem lem_homogeneous_mixture_iii (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    gaussianMixture N α Set.univ = ⊤ := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The mixture `ν_α` has
full support: it charges every nonempty open set. -/
theorem lem_homogeneous_mixture_iv (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    (gaussianMixture N α).IsOpenPosMeasure := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  Homogeneity:
`(D_ω)_# ν_α = |ω|^{-α} ν_α` for `ω ≠ 0`. -/
theorem lem_homogeneous_mixture_v (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    IsHomogeneous α (gaussianMixture N α) := by
  sorry

/-- **Lemma [lem:homogeneous-mixture]** Homogeneous Gaussian mixture.  The integrated form of
homogeneity: `∫ F(ωa) ν_α(da) = |ω|^{-α} ∫ F dν_α` for every nonnegative Borel `F`. -/
theorem lem_homogeneous_mixture_vi (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) :
    ∀ ω : ℝ, ω ≠ 0 → ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ a, F (ω • a) ∂gaussianMixture N α =
        ENNReal.ofReal (|ω| ^ (-α)) * ∫⁻ ξ, F ξ ∂gaussianMixture N α := by
  sorry

/-! ### Definition `def:admissible-filter` -/

/-- **Definition [def:admissible-filter]** Admissible analysis filter.  A band-pass filter is
`α`-admissible for every `α > 0`. -/
theorem def_admissible_filter (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ α : ℝ, 0 < α → IsAdmissible α ρ := by
  sorry

/-! ### Lemma `lem:fourier-slice` -/

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  `R_ρ f` is bounded on `H × ℝ`. -/
theorem lem_fourier_slice_i (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∃ M : ℝ, ∀ p : H × ℝ, ‖ridgelet μ ρ f p‖ ≤ M := by
  sorry

/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  `R_ρ f` is jointly continuous on
`H × ℝ`. -/
theorem lem_fourier_slice_ii (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    Continuous (ridgelet μ ρ f) := by
  sorry

/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  For every direction `a`, the bias
function `R_ρ f (a, ·)` is integrable with `‖R_ρ f(a,·)‖_{L¹} ≤ ‖f‖_{L¹(μ)} ‖ρ‖_{L¹}`. -/
theorem lem_fourier_slice_iii (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∀ a : H, Integrable (fun c : ℝ => ridgelet μ ρ f (a, c)) ∧
      ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ≤ (∫ x, ‖f x‖ ∂μ) * ∫ t : ℝ, ‖ρ t‖ := by
  sorry

/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  If moreover `f ∈ L²(μ)`, then for every
direction `a` the bias function is square integrable with
`‖R_ρ f(a,·)‖²_{L²} ≤ ‖f‖²_{L²(μ)} ‖ρ‖²_{L²}`. -/
theorem lem_fourier_slice_iv (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    ∀ a : H, MemLp (fun c : ℝ => ridgelet μ ρ f (a, c)) 2 volume ∧
      ∫ c : ℝ, ‖ridgelet μ ρ f (a, c)‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ t : ℝ, ‖ρ t‖ ^ 2 := by
  sorry

/-- **Lemma [lem:fourier-slice]** Fourier-slice identity.  The partial Fourier transform in the
bias is `\widehat{R_ρ f}(a,ω) = ρ̂(ω) 𝒢_μ f(-ωa)`. -/
theorem lem_fourier_slice_v (μ : Measure H) [IsProbabilityMeasure μ] (ρ : SchwartzMap ℝ ℝ)
    (f : H → ℂ) (hf : Integrable f μ) :
    ∀ (a : H) (ω : ℝ),
      biasFourier (ridgelet μ ρ f) a ω = filterFourier ρ ω * gaussFourier μ f (-(ω • a)) := by
  sorry

/-! ### Definition `def:spectral-coefficient` and Lemma `lem:coefficient-isometry` -/

/-- **Definition [def:spectral-coefficient]** The coefficient operator.  For
`G ∈ L¹(ν) ∩ L²(ν)` the coefficient `W_ρ G` is given by the explicit formula
`γ_G(a,c) = (2π)⁻¹ ∫ ρ̂(ω) G(-ωa) e^{iωc} dω`, `λ`-almost everywhere. -/
theorem def_spectral_coefficient {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) (hG₂ : MemLp G 2 ν) :
    (spectralCoefficient ν ρ G : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] coefficientFormula ρ G := by
  sorry

/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  `W_ρ G`
is well defined: there is exactly one element of `L²(λ)` whose partial Fourier transform in the
bias is `ρ̂(ω) G(-ωa)`. -/
theorem lem_coefficient_isometry_i {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∃! γ : Lp ℂ 2 (parameterMeasure ν),
      HasBiasFourier ν γ (fun a ω => filterFourier ρ ω * G (-(ω • a))) := by
  sorry

/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  `W_ρ G`
does not depend on the Borel representative of `G`. -/
theorem lem_coefficient_isometry_ii {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G G' : H → ℂ)
    (hG : Measurable G) (hG' : Measurable G') (hG₂ : MemLp G 2 ν) (hGG' : G =ᵐ[ν] G') :
    spectralCoefficient ν ρ G = spectralCoefficient ν ρ G' := by
  sorry

/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.
`‖W_ρ G‖²_{L²(λ)} = C^{(α)}_ρ ‖G‖²_{L²(ν)}`. -/
theorem lem_coefficient_isometry_iii {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₂ : MemLp G 2 ν) :
    ∫ p, ‖(spectralCoefficient ν ρ G : H × ℝ → ℂ) p‖ ^ 2 ∂parameterMeasure ν =
      admissibilityConst α ρ * ∫ ξ, ‖G ξ‖ ^ 2 ∂ν := by
  sorry

/-- **Lemma [lem:coefficient-isometry]** The coefficient operator is a scaled isometry.  If
`G ∈ L¹(ν)`, then `ω ↦ G(-ωa)` is integrable on compact subsets of `ℝ ∖ {0}` for `ν`-almost
every `a`. -/
theorem lem_coefficient_isometry_iv {α : ℝ} (hα : 0 < α) (ν : Measure H) [SigmaFinite ν]
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (G : H → ℂ)
    (hG : Measurable G) (hG₁ : Integrable G ν) :
    ∀ᵐ a ∂ν, ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I →
      IntegrableOn (fun ω : ℝ => G (-(ω • a))) I := by
  sorry

/-! ### Lemma `lem:spectral-unitary` -/

/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  The spectral form is
positive definite on `𝒟`: `⟨f,f⟩_𝓔 = 0` forces `f = 0` in `L²(μ)`. -/
theorem lem_spectral_unitary_i (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    ∀ f : Lp ℂ 2 μ, f ∈ spectralCore μ ν → spectralInner μ ν f f = 0 → f = 0 := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  `𝒢_μ` is an
isometry from `(𝒟, ⟨·,·⟩_𝓔)` into `𝒦`: the `L²(ν)` inner product of `U f` and `U g` (which in
Mathlib is conjugate linear in the first argument) is `⟨g,f⟩_𝓔`. -/
theorem lem_spectral_unitary_ii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    ∀ f g : spectralCore μ ν,
      inner ℂ (spectralEmbed μ ν f) (spectralEmbed μ ν g) =
        spectralInner μ ν ((g : Lp ℂ 2 μ) : H → ℂ) ((f : Lp ℂ 2 μ) : H → ℂ) := by
  sorry

/-- **Lemma [lem:spectral-unitary]** Positivity and the unitary extension.  The image of `𝒟`
under `𝒢_μ` is dense in `𝒦`, so the isometry extends uniquely to a unitary `U_α : 𝓔_α → 𝒦_α`
(the identity of `𝒦` in this representation). -/
theorem lem_spectral_unitary_iii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] :
    Dense (Set.range (spectralEmbed μ ν)) := by
  sorry

/-! ### Lemma `lem:gaussian-decay` and Example `ex:core-elements` -/

/-- **Lemma [lem:gaussian-decay]** Gaussian decay with polynomial weights.  For `t > 0` and every
integer `m ≥ 0`, `∫ ‖ξ‖^{2m} e^{-t⟨Qξ,ξ⟩} ν_α(dξ) < ∞`. -/
theorem lem_gaussian_decay_i (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * m) * Real.exp (-t * ⟪Q ξ, ξ⟫))
        (gaussianMixture N α) := by
  sorry

/-- **Lemma [lem:gaussian-decay]** Gaussian decay with polynomial weights.  If `f ∈ L²(μ_Q)` and
`|𝒢_Q f(ξ)| ≤ C (1+‖ξ‖)^p e^{-t⟨Qξ,ξ⟩/2}`, then `f ∈ 𝒟_α` for every `α > 0`. -/
theorem lem_gaussian_decay_ii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (f : Lp ℂ 2 μ) (C p t : ℝ)
    (hC : 0 < C) (hp : 0 ≤ p) (ht : 0 < t)
    (hdecay : ∀ ξ : H,
      ‖gaussFourier μ f ξ‖ ≤ C * (1 + ‖ξ‖) ^ p * Real.exp (-t * ⟪Q ξ, ξ⟫ / 2)) :
    f ∈ spectralCore μ (gaussianMixture N α) := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The constant function has
`𝒢_Q 1 (ξ) = e^{-⟨Qξ,ξ⟩/2}`. -/
theorem ex_core_elements_i {Q : H →L[ℝ] H} (μ : Measure H) [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) :
    ∀ ξ : H, gaussFourier μ (fun _ => (1 : ℂ)) ξ = Complex.exp (-((⟪Q ξ, ξ⟫ / 2 : ℝ) : ℂ)) := by
  sorry

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  The constant function belongs to `𝒟_α`
for every `α > 0`. -/
theorem ex_core_elements_ii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) ∈ spectralCore μ (gaussianMixture N α) := by
  sorry

/-- **Example [ex:core-elements]** Elements of `𝒟_α`.  Consequently `𝓔_α ≠ {0}`. -/
theorem ex_core_elements_iii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) :
    spectralRange μ (gaussianMixture N α) ≠ ⊥ := by
  sorry

/-! ### Theorem `thm:B` (Gaussian case) -/

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  For `f ∈ 𝒟_α` and an
`α`-admissible `ρ`, the transform `R_ρ f` belongs to `L²(λ_α)`. -/
theorem thm_B_i_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ (gaussianMixture N α)) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure (gaussianMixture N α)) := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ_α)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_α}` for `f, g ∈ 𝒟_α`. -/
theorem thm_B_i_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ₁ ρ₂ : SchwartzMap ℝ ℝ)
    (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂) (f g : Lp ℂ 2 μ)
    (hf : f ∈ spectralCore μ (gaussianMixture N α))
    (hg : g ∈ spectralCore μ (gaussianMixture N α)) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p)
        ∂parameterMeasure (gaussianMixture N α) =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ (gaussianMixture N α) f g := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  An `α`-admissible `ρ` determines a
unique bounded extension `R_ρ : 𝓔_α → L²(λ_α)` of `f ↦ R_ρ f` from `𝒟_α`. -/
theorem thm_B_ii_a (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRange μ (gaussianMixture N α) →L[ℂ]
        Lp ℂ 2 (parameterMeasure (gaussianMixture N α)),
      ∀ f : spectralCore μ (gaussianMixture N α),
        (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
          =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension satisfies
`‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_α}`. -/
theorem thm_B_ii_b (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    ∀ G : spectralRange μ (gaussianMixture N α), ‖R G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension has closed range. -/
theorem thm_B_ii_c (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    IsClosed (Set.range R) := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  The extension factors as
`R_ρ = W_ρ U_α`: on `𝒦_α` it is the coefficient operator. -/
theorem thm_B_ii_d (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ)
    (R : spectralRange μ (gaussianMixture N α) →L[ℂ]
      Lp ℂ 2 (parameterMeasure (gaussianMixture N α)))
    (hR : ∀ f : spectralCore μ (gaussianMixture N α),
      (R (spectralEmbed μ (gaussianMixture N α) f) : H × ℝ → ℂ)
        =ᵐ[parameterMeasure (gaussianMixture N α)] ridgelet μ ρ f) :
    ∀ G : spectralRange μ (gaussianMixture N α),
      R G = spectralCoefficient (gaussianMixture N α) ρ
        ((G : Lp ℂ 2 (gaussianMixture N α)) : H → ℂ) := by
  sorry

/-- **Theorem [thm:B]** Plancherel identity and injectivity.  Injectivity: if `ρ` is
`α`-admissible and `f ∈ L²(μ_Q)`, then `R_ρ f = 0` `λ_α`-almost everywhere implies `f = 0`
`μ_Q`-almost everywhere. -/
theorem thm_B_iii (hH : ¬ FiniteDimensional ℝ H) {P Q : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) (hQ : IsTraceClassCovariance Q) {N : ℝ → Measure H}
    (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (μ : Measure H)
    [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian Q μ) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure (gaussianMixture N α)] 0) :
    f =ᵐ[μ] 0 := by
  sorry

/-! ### Lemma `lem:mixture-integration` -/

/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For every
Borel set `E`, the map `s ↦ 𝒩(0,2sP)(E)` is Borel measurable on `(0,∞)`. -/
theorem lem_mixture_integration_i {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E → Measurable fun s : Set.Ioi (0 : ℝ) => N s E := by
  sorry

/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  The
mixture is a countably additive Borel measure given on Borel sets by
`ν_α(E) = ∫₀^∞ 𝒩(0,2sP)(E) s^{α/2-1} ds`. -/
theorem lem_mixture_integration_ii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ E : Set H, MeasurableSet E →
      gaussianMixture N α E =
        ∫⁻ s in Set.Ioi (0 : ℝ), N s E * ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  sorry

/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For every
nonnegative Borel `F`, `∫ F dν_α = ∫₀^∞ (∫ F d𝒩(0,2sP)) s^{α/2-1} ds`, both sides possibly
infinite. -/
theorem lem_mixture_integration_iii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ ξ, F ξ ∂gaussianMixture N α =
        ∫⁻ s in Set.Ioi (0 : ℝ), (∫⁻ ξ, F ξ ∂N s) * ENNReal.ofReal (s ^ (α / 2 - 1)) := by
  sorry

/-- **Lemma [lem:mixture-integration]** Measurability and integration of the mixture.  For
complex `F` the integration formula holds when `∫ |F| dν_α < ∞`. -/
theorem lem_mixture_integration_iv {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) :
    ∀ F : H → ℂ, Integrable F (gaussianMixture N α) →
      ∫ ξ, F ξ ∂gaussianMixture N α =
        ∫ s in Set.Ioi (0 : ℝ), (∫ ξ, F ξ ∂N s) * ((s ^ (α / 2 - 1) : ℝ) : ℂ) := by
  sorry

/-! ### Lemma `lem:mixture-character` -/

/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  For `z ≠ 0` the quadratic
form `q = ⟨Pz,z⟩` is positive. -/
theorem lem_mixture_character_i {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) (z : H)
    (hz : z ≠ 0) :
    0 < ⟪P z, z⟫ := by
  sorry

/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  The characteristic
functionals of the truncated mixtures `ν_α^{ε,M} = ∫_ε^M 𝒩(0,2sP) s^{α/2-1} ds` converge, as
`ε ↓ 0` and `M ↑ ∞`, to `Γ(α/2) q^{-α/2}`. -/
theorem lem_mixture_character_ii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P)
    {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N) {α : ℝ} (hα : 0 < α) (z : H)
    (hz : z ≠ 0) :
    Tendsto (fun εM : ℝ × ℝ => charFun (gaussianMixtureOn N α (Set.Ioo εM.1 εM.2)) z)
      ((𝓝[>] (0 : ℝ)) ×ˢ atTop)
      (𝓝 ((Real.Gamma (α / 2) * ⟪P z, z⟫ ^ (-(α / 2)) : ℝ) : ℂ)) := by
  sorry

/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  The limit is the Gamma
integral `∫₀^∞ e^{-sq} s^{α/2-1} ds = Γ(α/2) q^{-α/2}`. -/
theorem lem_mixture_character_iii {P : H →L[ℝ] H} (hP : IsTraceClassCovariance P) {α : ℝ}
    (hα : 0 < α) (z : H) (hz : z ≠ 0) :
    ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * ⟪P z, z⟫) * s ^ (α / 2 - 1) =
      Real.Gamma (α / 2) * ⟪P z, z⟫ ^ (-(α / 2)) := by
  sorry

/-- **Lemma [lem:mixture-character]** Gaussian-layer regularization.  In contrast, the character
`ξ ↦ e^{i⟨z,ξ⟩}` is not integrable against `ν_α`, so the limit is not a Lebesgue integral. -/
theorem lem_mixture_character_iv (hH : ¬ FiniteDimensional ℝ H) {P : H →L[ℝ] H}
    (hP : IsTraceClassCovariance P) {N : ℝ → Measure H} (hN : IsCenteredGaussianLayers P N)
    {α : ℝ} (hα : 0 < α) (z : H) (hz : z ≠ 0) :
    ¬ Integrable (fun ξ : H => Complex.exp ((⟪z, ξ⟫ : ℝ) * Complex.I)) (gaussianMixture N α) := by
  sorry

/-! ### Corollary `cor:finite-backprojection` -/

section FiniteDim

open OperatorRidgelet.FiniteDim

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  If
`f ∈ L²(p dx)` with `g = f p ∈ 𝒮(ℝ^m)`, then `f ∈ 𝒟_α`. -/
theorem cor_finite_backprojection_i {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    hf.toLp f ∈ spectralCore (densityMeasure p) (directionMeasure m α) := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  The
representative of the frame operator against the pivot measure is the Riesz potential
`t_f = ∫ e^{i⟨x,ξ⟩} ĝ(ξ) ν_α(dξ) = k_{m,α} (-Δ)^{-(m-α)/2} g`. -/
theorem cor_finite_backprojection_ii {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    ∀ x, frameRepresentative (directionMeasure m α) g x =
      frameConst m α * fracLaplacian (-((m - α) / 2)) g x := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  For a
band-pass `ρ`, the synthesis `S_ρ R_ρ f`, i.e. the functional `h ↦ ⟨R_ρ f, R_ρ h⟩_{L²(λ_α)}` on
`𝒟_α`, is represented against the pivot measure by `C^{(α)}_ρ t_f`. -/
theorem cor_finite_backprojection_iii {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ h : Lp ℂ 2 (densityMeasure p), h ∈ spectralCore (densityMeasure p) (directionMeasure m α) →
      ∫ q, ridgelet (densityMeasure p) ρ f q * (starRingEnd ℂ) (ridgelet (densityMeasure p) ρ h q)
          ∂parameterMeasure (directionMeasure m α) =
        admissibilityConst α ρ *
          ∫ x, frameRepresentative (directionMeasure m α) g x * (starRingEnd ℂ) (h x)
            ∂densityMeasure p := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  The
distributional reconstruction `f = p^{-1} (k_{m,α} C^{(α)}_ρ)^{-1} (-Δ)^{(m-α)/2} S_ρ R_ρ f`,
with `S_ρ R_ρ f` represented by `C^{(α)}_ρ t_f`: tested against Schwartz functions `φ`,
`∫ f φ p dx = (k C)^{-1} ∫ (C t_f) (-Δ)^{(m-α)/2} φ dx`. -/
theorem cor_finite_backprojection_iv {m : ℕ} {α : ℝ} (hα : 0 < α) (hαm : α < m)
    (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x) (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m}
    (hQ : IsTraceClassCovariance Q) [IsProbabilityMeasure (densityMeasure p)]
    (hpQ : IsCenteredGaussian Q (densityMeasure p)) (f : Euclid m → ℂ)
    (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ φ : SchwartzMap (Euclid m) ℂ,
      ∫ x, f x * φ x ∂densityMeasure p =
        ((frameConst m α * admissibilityConst α ρ)⁻¹ : ℝ) *
          ∫ x, (admissibilityConst α ρ * frameRepresentative (directionMeasure m α) g x) *
            fracLaplacian ((m - α) / 2) φ x := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  With
Lebesgue direction measure and `α = m`, the multiplier is one and `k = (2π)^m`:
`t_f = (2π)^m g`. -/
theorem cor_finite_backprojection_v {m : ℕ} (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x)
    (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m} (hQ : IsTraceClassCovariance Q)
    [IsProbabilityMeasure (densityMeasure p)] (hpQ : IsCenteredGaussian Q (densityMeasure p))
    (f : Euclid m → ℂ) (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) :
    ∀ x, frameRepresentative volume g x = ((2 * Real.pi) ^ m : ℝ) * (f x * p x) := by
  sorry

/-- **Corollary [cor:finite-backprojection]** The frame operator in finite dimension.  With
Lebesgue direction measure and `α = m`, `S_ρ R_ρ f` is represented against the pivot measure by
`(2π)^m C^{(m)}_ρ f p`, that is `f = (2π)^{-m} (C^{(m)}_ρ)^{-1} p^{-1} S_ρ R_ρ f`. -/
theorem cor_finite_backprojection_vi {m : ℕ} (p : Euclid m → ℝ) (hp : ∀ x, 0 < p x)
    (hpc : Continuous p) {Q : Euclid m →L[ℝ] Euclid m} (hQ : IsTraceClassCovariance Q)
    [IsProbabilityMeasure (densityMeasure p)] (hpQ : IsCenteredGaussian Q (densityMeasure p))
    (f : Euclid m → ℂ) (hf : MemLp f 2 (densityMeasure p)) (g : SchwartzMap (Euclid m) ℂ)
    (hg : ∀ x, g x = f x * p x) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∀ h : Lp ℂ 2 (densityMeasure p), h ∈ spectralCore (densityMeasure p) volume →
      ∫ q, ridgelet (densityMeasure p) ρ f q * (starRingEnd ℂ) (ridgelet (densityMeasure p) ρ h q)
          ∂parameterMeasure (volume : Measure (Euclid m)) =
        ∫ x, (((2 * Real.pi) ^ m * admissibilityConst m ρ : ℝ) : ℂ) * (f x * p x) *
          (starRingEnd ℂ) (h x) ∂densityMeasure p := by
  sorry

end FiniteDim

/-! ### Proposition `prop:dilation-obstruction` -/

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  The sets `E_t` are Borel. -/
theorem prop_dilation_obstruction_i_a (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) :
    ∀ t : ℝ, MeasurableSet (strongLawSet e w t) := by
  sorry

set_option linter.unusedVariables false in
omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  The sets `E_t` are pairwise
disjoint. -/
theorem prop_dilation_obstruction_i_b (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) :
    ∀ t t' : ℝ, t ≠ t' → Disjoint (strongLawSet e w t) (strongLawSet e w t') := by
  sorry

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  For `t > 0`,
`𝒩(0,tW)(E_t) = 1`. -/
theorem prop_dilation_obstruction_i_c (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γ : ℝ → Measure H)
    (hγ : ∀ t : ℝ, 0 < t → IsCenteredGaussian (t • W) (γ t)) :
    ∀ t : ℝ, 0 < t → γ t (strongLawSet e w t) = 1 := by
  sorry

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  Consequently a σ-finite
measure dominates `𝒩(0,tW)` for at most countably many `t > 0`. -/
theorem prop_dilation_obstruction_i_d (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γ : ℝ → Measure H)
    (hγ : ∀ t : ℝ, 0 < t → IsCenteredGaussian (t • W) (γ t)) :
    ∀ ν : Measure H, SigmaFinite ν → Set.Countable {t : ℝ | 0 < t ∧ γ t ≪ ν} := by
  sorry

/-- **Proposition [prop:dilation-obstruction]** Dilation obstruction.  For a bounded Borel `r`
with `{r ≠ 0}` of positive Lebesgue measure, no finite complex Borel measure `Γ = h m` on
`H × ℝ` (a finite measure `m` with an integrable density `h`) has bias slices
`Γ⁺_ω(E) = ∫_{E×ℝ} e^{iωc} Γ(da,dc) = r(ω) (D_{1/ω})_# 𝒩(0,W)(E)` for almost every `ω ≠ 0`. -/
theorem prop_dilation_obstruction_ii (hH : ¬ FiniteDimensional ℝ H) {W : H →L[ℝ] H}
    (hW : IsTraceClassCovariance W) (e : HilbertBasis ℕ ℝ H) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hWe : ∀ j, W (e j) = w j • e j) (γW : Measure H) (hγW : IsCenteredGaussian W γW)
    (r : ℝ → ℝ) (hr : Measurable r) (hrb : ∃ M : ℝ, ∀ ω, |r ω| ≤ M)
    (hr0 : 0 < volume {ω : ℝ | r ω ≠ 0}) :
    ¬ ∃ m : Measure (H × ℝ), IsFiniteMeasure m ∧ ∃ h : H × ℝ → ℂ, Integrable h m ∧
      ∀ᵐ ω ∂(volume : Measure ℝ), ω ≠ 0 → ∀ E : Set H, MeasurableSet E →
        ∫ q in E ×ˢ Set.univ, Complex.exp ((ω * q.2 : ℝ) * Complex.I) * h q ∂m =
          (r ω : ℂ) * (((γW.map fun a => ω⁻¹ • a) E).toReal : ℂ) := by
  sorry

/-! ### Theorem `thm:general-weights` -/

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(i) for the
abstract pair: `R_ρ f ∈ L²(λ)` for `f ∈ 𝒟_{μ,ν}` and `α`-admissible `ρ`. -/
theorem thm_general_weights_plancherel_memLp (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) :
    MemLp (ridgelet μ ρ f) 2 (parameterMeasure ν) := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(i) for the
abstract pair: the Plancherel identity
`⟨R_{ρ₁} f, R_{ρ₂} g⟩_{L²(λ)} = C^{(α)}_{ρ₁,ρ₂} ⟨f,g⟩_{𝓔_{μ,ν}}`. -/
theorem thm_general_weights_plancherel (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ₁ ρ₂ : SchwartzMap ℝ ℝ) (hρ₁ : IsAdmissible α ρ₁) (hρ₂ : IsAdmissible α ρ₂)
    (f g : Lp ℂ 2 μ) (hf : f ∈ spectralCore μ ν) (hg : g ∈ spectralCore μ ν) :
    ∫ p, ridgelet μ ρ₁ f p * (starRingEnd ℂ) (ridgelet μ ρ₂ g p) ∂parameterMeasure ν =
      crossAdmissibilityConst α ρ₁ ρ₂ * spectralInner μ ν f g := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: the unique bounded extension `R_ρ : 𝓔_{μ,ν} → L²(λ)`. -/
theorem thm_general_weights_extension (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) :
    ∃! R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν),
      ∀ f : spectralCore μ ν,
        (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: `‖R_ρ f‖² = C^{(α)}_ρ ‖f‖²_{𝓔_{μ,ν}}`. -/
theorem thm_general_weights_extension_norm (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, ‖R G‖ ^ 2 = admissibilityConst α ρ * ‖G‖ ^ 2 := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: the extension has closed range. -/
theorem thm_general_weights_extension_closed_range (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    IsClosed (Set.range R) := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(ii) for the
abstract pair: `R_ρ = W_ρ U`. -/
theorem thm_general_weights_extension_coefficient (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ)
    (R : spectralRange μ ν →L[ℂ] Lp ℂ 2 (parameterMeasure ν))
    (hR : ∀ f : spectralCore μ ν,
      (R (spectralEmbed μ ν f) : H × ℝ → ℂ) =ᵐ[parameterMeasure ν] ridgelet μ ρ f) :
    ∀ G : spectralRange μ ν, R G = spectralCoefficient ν ρ ((G : Lp ℂ 2 ν) : H → ℂ) := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  Theorem `thm:B`(iii) for the
abstract pair: `R_ρ f = 0` `λ`-a.e. implies `f = 0` `μ`-a.e. for `f ∈ L²(μ)`. -/
theorem thm_general_weights_injective (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : H → ℂ) (hf : MemLp f 2 μ)
    (h : ridgelet μ ρ f =ᵐ[parameterMeasure ν] 0) :
    f =ᵐ[μ] 0 := by
  sorry

/-- **Theorem [thm:general-weights]** Abstract-weight extension.  `1 ∈ 𝒟_{μ,ν}` if and only if
`∫ |μ̂(ξ)|² ν(dξ) < ∞`. -/
theorem thm_general_weights_one_mem_iff (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) :
    MemLp.toLp (fun _ : H => (1 : ℂ)) (memLp_const 1) ∈ spectralCore μ ν ↔
      Integrable (fun ξ : H => ‖charFun μ ξ‖ ^ 2) ν := by
  sorry

/-! ### Example `ex:bandlimited-filter` -/

section Filters

open OperatorRidgelet.Filters

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The prescribed
Fourier transform `ρ̂_bp` is smooth. -/
theorem ex_bandlimited_filter_i : ContDiff ℝ (⊤ : ℕ∞) bandPassHat := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
nonpositive. -/
theorem ex_bandlimited_filter_ii : ∀ ω : ℝ, bandPassHat ω ≤ 0 := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
nonzero. -/
theorem ex_bandlimited_filter_iii : bandPassHat ≠ 0 := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ̂_bp` is
supported in `{1 ≤ |ω| ≤ 2}`. -/
theorem ex_bandlimited_filter_iv : tsupport bandPassHat ⊆ {ω : ℝ | 1 ≤ |ω| ∧ |ω| ≤ 2} := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The inverse
Fourier transform `ρ_bp` of `ρ̂_bp` is a real Schwartz function. -/
theorem ex_bandlimited_filter_v : ⇑bandPass = bandPassFun := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` is even. -/
theorem ex_bandlimited_filter_vi : ∀ t : ℝ, bandPass (-t) = bandPass t := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  The Fourier
transform of `ρ_bp` is the prescribed `ρ̂_bp`. -/
theorem ex_bandlimited_filter_vii : ∀ ω : ℝ, filterFourier bandPass ω = (bandPassHat ω : ℂ) := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` satisfies
the band-pass condition. -/
theorem ex_bandlimited_filter_viii : IsBandPass bandPass := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  `ρ_bp` is
`α`-admissible for every `α > 0`. -/
theorem ex_bandlimited_filter_ix : ∀ α : ℝ, 0 < α → IsAdmissible α bandPass := by
  sorry

/-- **Example [ex:bandlimited-filter]** A band-pass filter for every `α > 0`.  Multiplying by
`(C^{(α)}_{ρ_bp})^{-1/2}` normalizes the admissibility constant to one. -/
theorem ex_bandlimited_filter_x :
    ∀ α : ℝ, 0 < α →
      admissibilityConst α ((Real.sqrt (admissibilityConst α bandPass))⁻¹ • bandPass) = 1 := by
  sorry

/-! ### Example `ex:mexican-hat` -/

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ_MH(t) = (1 - t²) e^{-t²/2}` is a Schwartz
function. -/
theorem ex_mexican_hat_i : ⇑mexicanHat = mexicanHatFun := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ̂_MH(ω) = √(2π) ω² e^{-ω²/2}`. -/
theorem ex_mexican_hat_ii :
    ∀ ω : ℝ, filterFourier mexicanHat ω =
      ((Real.sqrt (2 * Real.pi) * ω ^ 2 * Real.exp (-ω ^ 2 / 2) : ℝ) : ℂ) := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  Under the standing assumption `α > 0`, `ρ_MH` is
`α`-admissible exactly for `α < 5`. -/
theorem ex_mexican_hat_iii : ∀ α : ℝ, 0 < α → (IsAdmissible α mexicanHat ↔ α < 5) := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  For `0 < α < 5`,
`C^{(α)}_{ρ_MH} = Γ((5-α)/2)`. -/
theorem ex_mexican_hat_iv :
    ∀ α : ℝ, 0 < α → α < 5 → admissibilityConst α mexicanHat = Real.Gamma ((5 - α) / 2) := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  In particular `C^{(1)}_{ρ_MH} = 1`. -/
theorem ex_mexican_hat_v : admissibilityConst 1 mexicanHat = 1 := by
  sorry

/-- **Example [ex:mexican-hat]** Mexican hat.  `ρ_MH` is not band pass. -/
theorem ex_mexican_hat_vi : ¬ IsBandPass mexicanHat := by
  sorry

end Filters

end OperatorRidgelet.Paper
