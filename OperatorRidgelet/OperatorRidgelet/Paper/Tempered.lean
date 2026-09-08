import OperatorRidgelet.Tempered.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Basic

/-!
# Statements of Section 5 (tempered synthesis activations and ReLU) and Appendix C

Each item is `theorem OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, identical to its twin in
`Challenge.Tempered`, proved from the library or left as `sorry`.

The statements are made for the abstract pair `(μ, ν)` of Appendix H (`μ` a probability measure,
`ν` σ-finite with full support and homogeneous of degree `α`), of which the Gaussian pair
`(μ_Q, ν_α)` of the manuscript is the instance; `𝓔_α` is represented by `𝒦_α = spectralRange μ ν`,
its anti-dual by `SpectralAntiDual μ ν`, the extended transform `R_ρ` by `ridgeletExtension`,
the synthesis `S_ρ` by `synthesis`, and the Riesz map `T_α` and its inverse by `rieszMap` and
`rieszInv`, all from `OperatorRidgelet.Reconstruction.Defs` (Section 4; see also the discussion
in `OperatorRidgelet.Tempered.Defs`).  The target `g_G` and regularity along rays in Corollary
`cor:relu-admissible`(viii) are `spectralTarget` and `IsRegularAlongRays` with the frequency
window `IsFrequencyWindow ρ I`, so that (viii) is the instance `b = ReLU` of Theorem A(iii).
The distributional admissibility constant `C^{(α)}_{β,ρ}` is the shared
`temperedAdmissibilityConst`.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Complex Filter Topology LeanRidgelet LeanRidgelet.Fourier
open scoped ENNReal NNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-! ### Definition `def:regularized-synthesis` -/

/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  For a band-pass `ρ` there
is an even `χ ∈ C_c^∞(ℝ ∖ {0})` equal to one on a neighbourhood of `supp ρ̂`. -/
theorem def_regularized_synthesis_i (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) :
    ∃ χ : ℝ → ℝ, IsCutoff ρ χ := by
  sorry

/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  There is an even,
compactly supported, smooth approximate identity `(η_ε)_{ε>0}`. -/
theorem def_regularized_synthesis_ii : ∃ η : ℝ → ℝ → ℝ, IsApproximateIdentity η :=
  ⟨bumpApproximateIdentity, isApproximateIdentity_bumpApproximateIdentity⟩

/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  For real `β`, band-pass
`ρ`, a cutoff `χ`, and an approximate identity `(η_ε)`, the regularized spectrum
`β̂_ε = χ (β̂ * η_ε)` belongs to `C_c^∞(ℝ ∖ {0})` for every `ε > 0`. -/
theorem def_regularized_synthesis_iii (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedSpectrum β χ η ε) ∧
      HasCompactSupport (regularizedSpectrum β χ η ε) ∧
      (0 : ℝ) ∉ tsupport (regularizedSpectrum β χ η ε) := by
  sorry

/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  There is a real Schwartz
function `β_ε` with `β̂_ε = χ (β̂ * η_ε)`: the chosen `regularizedActivation` has this Fourier
transform. -/
theorem def_regularized_synthesis_iv (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (ε : ℝ) (hε : 0 < ε) :
    ∀ ω : ℝ, filterFourier (regularizedActivation β χ η ε) ω = regularizedSpectrum β χ η ε ω := by
  sorry

/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  The real Schwartz function
`β_ε` with `β̂_ε = χ (β̂ * η_ε)` is unique. -/
theorem def_regularized_synthesis_v (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (ε : ℝ) (hε : 0 < ε) :
    ∀ b : SchwartzMap ℝ ℝ, (∀ ω : ℝ, filterFourier b ω = regularizedSpectrum β χ η ε ω) →
      b = regularizedActivation β χ η ε := by
  sorry

set_option linter.unusedVariables false in
omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Definition [def:regularized-synthesis]** Regularized synthesis.  For `γ ∈ Ran R_ρ` the
regularized synthesis `S_{β_ε} γ = R'_{β_ε} γ` is a well-defined element of `𝓔_α'`: it is the
continuous anti-linear functional `g ↦ ⟨γ, R_{β_ε} g⟩_{L²(λ)}` (in the representation of
`OperatorRidgelet.Reconstruction.Defs`, where `S_ρ` is the transpose of the bounded extension
`R_ρ`, this holds by definition). -/
theorem def_regularized_synthesis_vi (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (ε : ℝ) (hε : 0 < ε) (γ : Lp ℂ 2 (parameterMeasure ν))
    (hγ : γ ∈ ridgeletRange μ ν ρ) :
    ∀ g : spectralRange μ ν,
      regularizedSynthesis μ ν β χ η ε γ g =
        inner ℂ (ridgeletExtension μ ν (regularizedActivation β χ η ε) g) γ :=
  fun _ => rfl

/-! ### Theorem `thm:tempered-reconstruction` -/

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  For
every `f ∈ 𝓔_α` the limit `S_β R_ρ f = lim_{ε ↓ 0} S_{β_ε} R_ρ f` exists in `𝓔_α'`. -/
theorem thm_tempered_reconstruction_i (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (f : spectralRange μ ν) :
    ∃ F : SpectralAntiDual μ ν,
      Tendsto (fun ε : ℝ => regularizedSynthesis μ ν β χ η ε (ridgeletExtension μ ν ρ f))
        (𝓝[>] 0) (𝓝 F) := by
  sorry

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  The
limit `S_β R_ρ f` does not depend on the cutoff `χ` or on the approximate identity `(η_ε)`. -/
theorem thm_tempered_reconstruction_ii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ χ' : ℝ → ℝ) (hχ : IsCutoff ρ χ) (hχ' : IsCutoff ρ χ')
    (η η' : ℝ → ℝ → ℝ) (hη : IsApproximateIdentity η) (hη' : IsApproximateIdentity η')
    (f : spectralRange μ ν) :
    temperedSynthesis μ ν β χ η (ridgeletExtension μ ν ρ f) =
      temperedSynthesis μ ν β χ' η' (ridgeletExtension μ ν ρ f) := by
  sorry

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  The
frame identity `S_β R_ρ f = C^{(α)}_{β,ρ} T_α f` for `f ∈ 𝓔_α`. -/
theorem thm_tempered_reconstruction_iii (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (f : spectralRange μ ν) :
    temperedSynthesis μ ν β χ η (ridgeletExtension μ ν ρ f) =
      temperedAdmissibilityConst α β ρ • rieszMap μ ν f := by
  sorry

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  If
`C^{(α)}_{β,ρ} ≠ 0`, then `f = (C^{(α)}_{β,ρ})⁻¹ T_α⁻¹ S_β R_ρ f` for `f ∈ 𝓔_α`. -/
theorem thm_tempered_reconstruction_iv (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (hC : temperedAdmissibilityConst α β ρ ≠ 0)
    (f : spectralRange μ ν) :
    f = (temperedAdmissibilityConst α β ρ)⁻¹ •
      rieszInv μ ν
        (temperedSynthesis μ ν β χ η (ridgeletExtension μ ν ρ f)) := by
  sorry

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  If
`C^{(α)}_{β,ρ} ≠ 0`, then `g = (C^{(α)}_{β,ρ})⁻¹ S_β (R_ρ T_α⁻¹ g)` for `g ∈ 𝓔_α'`. -/
theorem thm_tempered_reconstruction_v (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (χ : ℝ → ℝ) (hχ : IsCutoff ρ χ) (η : ℝ → ℝ → ℝ)
    (hη : IsApproximateIdentity η) (hC : temperedAdmissibilityConst α β ρ ≠ 0)
    (g : SpectralAntiDual μ ν) :
    g = (temperedAdmissibilityConst α β ρ)⁻¹ •
      temperedSynthesis μ ν β χ η
        (ridgeletExtension μ ν ρ (rieszInv μ ν g)) := by
  sorry

/-- **Theorem [thm:tempered-reconstruction]** Reconstruction with a tempered activation.  If
`β` is not a polynomial (equivalently `β ≠ 0` in `𝒮'/𝒫`), then a band-pass `ρ` with
`C^{(α)}_{β,ρ} ≠ 0` exists. -/
theorem thm_tempered_reconstruction_vi {α : ℝ} (hα : 0 < α) (β : TemperedDistribution ℝ ℂ)
    (hβ : IsRealDistribution β) (hpoly : ¬ IsPolynomialDistribution β) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α β ρ ≠ 0 := by
  sorry

/-! ### Corollary `cor:relu-admissible` -/

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  Under the manuscript's convention
`ReLU^ = -fp(ω^{-2}) + iπ δ₀'`: tested against a Schwartz function `φ`, the Hadamard finite part
`⟨fp(ω^{-2}), φ⟩ = lim_{ε ↓ 0} (∫_{|ω|>ε} φ(ω) ω^{-2} dω - 2 φ(0)/ε)` equals
`-⟨ReLU^, φ⟩ - iπ φ'(0)`. -/
theorem cor_relu_admissible_i :
    ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun ε : ℝ => (∫ ω in {ω : ℝ | ε < |ω|}, φ ω / (ω : ℂ) ^ 2) - 2 * φ 0 / (ε : ℂ))
        (𝓝[>] 0)
        (𝓝 (-(angularFourierDistribution reluDistribution φ) -
          (Real.pi : ℂ) * Complex.I * deriv φ 0)) := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  Away from the origin `ReLU^` equals
`-ω^{-2}`: `⟨ReLU^, φ⟩ = ∫ (-ω^{-2}) φ(ω) dω` for every Schwartz `φ` supported away from `0`. -/
theorem cor_relu_admissible_ii :
    ∀ φ : SchwartzMap ℝ ℂ, (0 : ℝ) ∉ tsupport φ →
      angularFourierDistribution reluDistribution φ = ∫ ω : ℝ, -((ω : ℂ) ^ 2)⁻¹ * φ ω := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  If `ρ̂ ∈ C_c^∞(ℝ ∖ {0})` is
nonzero, even, and nonpositive, then `C^{(α)}_{ReLU,ρ} = -(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω`. -/
theorem cor_relu_admissible_iii {α : ℝ} (hα : 0 < α) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) :
    temperedAdmissibilityConst α reluDistribution ρ = (reluAdmissibilityScale α ρ : ℂ) := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  Under the same hypotheses the
constant `-(2π)⁻¹ ∫ ρ̂(ω) |ω|^{-α-2} dω` is positive. -/
theorem cor_relu_admissible_iv {α : ℝ} (hα : 0 < α) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) :
    0 < reluAdmissibilityScale α ρ := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  After rescaling, `ρ` is still
band-pass and `C^{(α)}_{ReLU,ρ} = 1`. -/
theorem cor_relu_admissible_v {α : ℝ} (hα : 0 < α) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) :
    IsBandPass (reluNormalizedFilter α ρ) ∧
      temperedAdmissibilityConst α reluDistribution (reluNormalizedFilter α ρ) = 1 := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  With the rescaled filter the first
reconstruction formula holds with ReLU synthesis for every `α > 0`:
`f = T_α⁻¹ S_{ReLU} R_ρ f` for `f ∈ 𝓔_α`. -/
theorem cor_relu_admissible_vi (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) (χ : ℝ → ℝ)
    (hχ : IsCutoff (reluNormalizedFilter α ρ) χ) (η : ℝ → ℝ → ℝ) (hη : IsApproximateIdentity η)
    (f : spectralRange μ ν) :
    f = rieszInv μ ν
      (temperedSynthesis μ ν reluDistribution χ η
        (ridgeletExtension μ ν (reluNormalizedFilter α ρ) f)) := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  With the rescaled filter the second
reconstruction formula holds with ReLU synthesis for every `α > 0`:
`g = S_{ReLU} (R_ρ T_α⁻¹ g)` for `g ∈ 𝓔_α'`. -/
theorem cor_relu_admissible_vii (μ ν : Measure H) [IsProbabilityMeasure μ] [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) (χ : ℝ → ℝ)
    (hχ : IsCutoff (reluNormalizedFilter α ρ) χ) (η : ℝ → ℝ → ℝ) (hη : IsApproximateIdentity η)
    (g : SpectralAntiDual μ ν) :
    g = temperedSynthesis μ ν reluDistribution χ η
      (ridgeletExtension μ ν (reluNormalizedFilter α ρ) (rieszInv μ ν g)) := by
  sorry

/-- **Corollary [cor:relu-admissible]** ReLU is admissible.  With the rescaled filter Theorem
A(iii) holds with ReLU synthesis for every `α > 0`: for `G` regular along rays and every `x`,
the inner integral `∫ γ_G(a,c) ReLU(⟪a,x⟫ + c) dc` converges absolutely for `ν`-almost every
`a`, its `ν`-integral converges absolutely, and it equals `g_G(x)`. -/
theorem cor_relu_admissible_viii (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure] {α : ℝ}
    (hα : 0 < α) (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hρ_real : ∀ ω : ℝ, (filterFourier ρ ω).im = 0)
    (hρ_even : ∀ ω : ℝ, filterFourier ρ (-ω) = filterFourier ρ ω)
    (hρ_nonpos : ∀ ω : ℝ, (filterFourier ρ ω).re ≤ 0) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    (G : H → ℂ) (hG : IsRegularAlongRays ν I G) :
    ∀ x : H,
      (∀ᵐ a ∂ν, Integrable fun c : ℝ =>
        coefficientFormula (reluNormalizedFilter α ρ) G (a, c) * (relu (⟪a, x⟫ + c) : ℂ)) ∧
      Integrable (fun a : H => ∫ c : ℝ,
        coefficientFormula (reluNormalizedFilter α ρ) G (a, c) * (relu (⟪a, x⟫ + c) : ℂ)) ν ∧
      ∫ a : H, (∫ c : ℝ,
        coefficientFormula (reluNormalizedFilter α ρ) G (a, c) * (relu (⟪a, x⟫ + c) : ℂ)) ∂ν =
        spectralTarget ν G x := by
  sorry

/-! ### Example `ex:standard-activations` -/

/-- **Example [ex:standard-activations]** Standard activations.  ReLU is covered by Theorem
`thm:tempered-reconstruction`, Theorem A(iii), and the finite-width bounds: for every `α > 0`
there is a band-pass `ρ` with `C^{(α)}_{ReLU,ρ} ≠ 0`. -/
theorem ex_standard_activations_relu {α : ℝ} (hα : 0 < α) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α reluDistribution ρ ≠ 0 := by
  sorry

/-- **Example [ex:standard-activations]** Standard activations.  `tanh` is covered by Theorem
`thm:tempered-reconstruction`, Theorem A(iii), and the finite-width bounds: for every `α > 0`
there is a band-pass `ρ` with `C^{(α)}_{tanh,ρ} ≠ 0`. -/
theorem ex_standard_activations_tanh {α : ℝ} (hα : 0 < α) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α tanhDistribution ρ ≠ 0 := by
  sorry

/-- **Example [ex:standard-activations]** Standard activations.  The Gaussian distribution
function `Φ` is covered by Theorem `thm:tempered-reconstruction`, Theorem A(iii), and the
finite-width bounds: for every `α > 0` there is a band-pass `ρ` with `C^{(α)}_{Φ,ρ} ≠ 0`. -/
theorem ex_standard_activations_gaussianCdf {α : ℝ} (hα : 0 < α) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧
      temperedAdmissibilityConst α gaussianCdfDistribution ρ ≠ 0 := by
  sorry

/-- **Example [ex:standard-activations]** Standard activations.  The Gaussian `e^{-u²/2}` is
covered by Theorem `thm:tempered-reconstruction`, Theorem A(iii), and the finite-width bounds:
for every `α > 0` there is a band-pass `ρ` with `C^{(α)}_{e^{-u²/2},ρ} ≠ 0`. -/
theorem ex_standard_activations_gaussian {α : ℝ} (hα : 0 < α) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧
      temperedAdmissibilityConst α gaussianDistribution ρ ≠ 0 := by
  sorry

/-! ### Lemma `lem:weighted-duality` -/

/-- **Lemma [lem:weighted-duality]** Hilbert structure and continuous activation pairing.  The
map `β ↦ ⟨ω⟩^s B^{-t} β̂` is well defined on `𝒜_{s,t}`: its value is represented by an element
of `L²(ℝ)`. -/
theorem lem_weighted_duality_i (s t : ℝ) (β : TemperedDistribution ℝ ℂ)
    (hβ : MemActivationSpace s t β) :
    ∃ σ : L2 ℝ volume,
      Lp.toTemperedDistributionCLM ℂ volume 2 σ = activationFourierCoordinate s t β := by
  sorry

/-- **Lemma [lem:weighted-duality]** Hilbert structure and continuous activation pairing.  The
map `β ↦ ⟨ω⟩^s B^{-t} β̂` is injective on `𝒜_{s,t}`. -/
theorem lem_weighted_duality_ii (s t : ℝ) (β β' : TemperedDistribution ℝ ℂ)
    (hβ : MemActivationSpace s t β) (hβ' : MemActivationSpace s t β')
    (h : activationCoordinate s t β = activationCoordinate s t β') :
    β = β' := by
  sorry

/-- **Lemma [lem:weighted-duality]** Hilbert structure and continuous activation pairing.  The
map `β ↦ ⟨ω⟩^s B^{-t} β̂` is onto `L²(ℝ)`: every `σ ∈ L²(ℝ)` is the coordinate of the activation
`β = 𝓕⁻¹[B^t ⟨ω⟩^{-s} σ] ∈ 𝒜_{s,t}` (the vendored `activationRealization`); the isometry is the
definition of the norm `‖β‖_{𝒜_{s,t}} = ‖σ‖_{L²}`. -/
theorem lem_weighted_duality_iii (s t : ℝ) (σ : L2 ℝ volume) :
    MemActivationSpace s t (activationRealization s t σ) ∧
      activationCoordinate s t (activationRealization s t σ) = σ := by
  sorry

/-- **Lemma [lem:weighted-duality]** Hilbert structure and continuous activation pairing.  The
duality bound `|(2π)⁻¹ ⟨β̂, r⟩| ≤ (2π)⁻¹ ‖β‖_{𝒜_{s,t}} ‖r‖_{ℋ^♯_{s,t}}` for `β ∈ 𝒜_{s,t}` and
Schwartz `r`. -/
theorem lem_weighted_duality_iv (s t : ℝ) (β : TemperedDistribution ℝ ℂ)
    (hβ : MemActivationSpace s t β) (r : SchwartzMap ℝ ℂ) :
    ‖((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β r‖ ≤
      (2 * Real.pi)⁻¹ * activationNorm s t β * testFilterNorm s t r := by
  sorry

/-- **Lemma [lem:weighted-duality]** Hilbert structure and continuous activation pairing.  The
pairing extends to the completion of the test filters in `ℋ^♯_{s,t}`, which is `L²(ℝ)` through
the coordinate `r ↦ ⟨ω⟩^{-s} B^t r`: there is a continuous linear functional on `L²(ℝ)` of norm
at most `(2π)⁻¹ ‖β‖_{𝒜_{s,t}}` that agrees with `(2π)⁻¹ ⟨β̂, r⟩` on the test filters. -/
theorem lem_weighted_duality_v (s t : ℝ) (β : TemperedDistribution ℝ ℂ)
    (hβ : MemActivationSpace s t β) :
    ∃ Φ : L2 ℝ volume →L[ℂ] ℂ, ‖Φ‖ ≤ (2 * Real.pi)⁻¹ * activationNorm s t β ∧
      ∀ r : SchwartzMap ℝ ℂ,
        Φ ((testFilterCoordinate s t r).toLp 2 volume) =
          ((2 * Real.pi)⁻¹ : ℝ) * angularFourierDistribution β r := by
  sorry

/-! ### Lemma `lem:standard-activation-class` -/

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
ReLU belongs to `𝒜_{0,2}`. -/
theorem lem_standard_activation_class_relu_mem : MemActivationSpaceFun 0 2 relu :=
  ⟨reluTemperedDistribution 2 (by norm_num), reluTemperedDistribution_apply 2 (by norm_num),
    memActivationSpace_reluTemperedDistribution 2 (by norm_num)⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
ReLU is globally Lipschitz. -/
theorem lem_standard_activation_class_relu_lipschitz : ∃ L : ℝ≥0, LipschitzWith L relu :=
  ⟨1, lipschitzWith_relu⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
ReLU is not a polynomial. -/
theorem lem_standard_activation_class_relu_not_polynomial : ¬ IsPolynomialFun relu :=
  not_isPolynomialFun_relu

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
`tanh` belongs to `𝒜_{0,2}`. -/
theorem lem_standard_activation_class_tanh_mem : MemActivationSpaceFun 0 2 Real.tanh :=
  ⟨tanhTemperedDistribution 2 (by norm_num), tanhTemperedDistribution_apply 2 (by norm_num),
    memActivationSpace_tanhTemperedDistribution 2 (by norm_num)⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
`tanh` is globally Lipschitz. -/
theorem lem_standard_activation_class_tanh_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L Real.tanh :=
  ⟨1, lipschitzWith_tanh⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
`tanh` is not a polynomial. -/
theorem lem_standard_activation_class_tanh_not_polynomial : ¬ IsPolynomialFun Real.tanh :=
  not_isPolynomialFun_of_bounded abs_tanh_le_one tanh_zero_ne_tanh_one

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian distribution function `Φ` belongs to `𝒜_{0,2}`. -/
theorem lem_standard_activation_class_gaussianCdf_mem : MemActivationSpaceFun 0 2 gaussianCdf :=
  memActivationSpaceFun_of_bounded measurable_gaussianCdf abs_gaussianCdf_le_one (by norm_num)

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian distribution function `Φ` is globally Lipschitz. -/
theorem lem_standard_activation_class_gaussianCdf_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L gaussianCdf :=
  ⟨_, lipschitzWith_gaussianCdf⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian distribution function `Φ` is not a polynomial. -/
theorem lem_standard_activation_class_gaussianCdf_not_polynomial :
    ¬ IsPolynomialFun gaussianCdf :=
  not_isPolynomialFun_of_bounded abs_gaussianCdf_le_one gaussianCdf_zero_lt_gaussianCdf_one.ne

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian `e^{-u²/2}` belongs to `𝒜_{0,2}`. -/
theorem lem_standard_activation_class_gaussian_mem : MemActivationSpaceFun 0 2 gaussianFun :=
  memActivationSpaceFun_of_bounded continuous_gaussianFun.measurable abs_gaussianFun_le_one
    (by norm_num)

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian `e^{-u²/2}` is globally Lipschitz. -/
theorem lem_standard_activation_class_gaussian_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L gaussianFun :=
  ⟨1, lipschitzWith_gaussianFun⟩

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
The Gaussian `e^{-u²/2}` is not a polynomial. -/
theorem lem_standard_activation_class_gaussian_not_polynomial : ¬ IsPolynomialFun gaussianFun :=
  not_isPolynomialFun_of_bounded abs_gaussianFun_le_one gaussianFun_zero_ne_gaussianFun_one

/-- **Lemma [lem:standard-activation-class]** Standard activations and admissible test filters.
For every non-polynomial real `β ∈ 𝒮'` there is a real band-pass `ρ` with
`C^{(α)}_{β,ρ} = 1`. -/
theorem lem_standard_activation_class_exists_filter {α : ℝ} (hα : 0 < α)
    (β : TemperedDistribution ℝ ℂ) (hβ : IsRealDistribution β)
    (hpoly : ¬ IsPolynomialDistribution β) :
    ∃ ρ : SchwartzMap ℝ ℝ, IsBandPass ρ ∧ temperedAdmissibilityConst α β ρ = 1 := by
  sorry

end OperatorRidgelet.Paper
