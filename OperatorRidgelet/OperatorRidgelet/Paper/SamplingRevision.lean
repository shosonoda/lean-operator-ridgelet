import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.ToFoML.TwoCoordinate
import OperatorRidgelet.Sampling.FirstMoment
import OperatorRidgelet.Sampling.Variance

/-! # Integrable Banach-valued sampling: manuscript statements -/

noncomputable section
namespace OperatorRidgelet.Paper
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

/-- **Lemma [lem:banach-rademacher-vanishing](i).** The signed empirical mean of a
Bochner-integrable separable Banach-valued atom tends to zero in expected norm. -/
theorem lem_banach_rademacher_vanishing_i {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → E} (hint : Integrable Φ p) :
    Tendsto (fun N : ℕ => ∫ z : (Fin N → Ω) × (Fin N → ℝ),
      ‖(N : ℝ)⁻¹ • ∑ j, z.2 j • Φ (z.1 j)‖
        ∂((Measure.pi fun _ : Fin N => p).prod (rademacherMeasure N))) atTop (𝓝 0) := by
  exact tendsto_signed_sample_average p hint

/-- **Lemma [lem:banach-rademacher-vanishing](ii).** Symmetrization of the empirical mean.
The finite sum averages over the uniform Boolean sign vectors; the inverse width outside
the norm is the equivalent normalization of the manuscript's empirical averages. -/
theorem lem_banach_rademacher_vanishing_ii {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → E} (hint : Integrable Φ p) (N : ℕ) :
    (N : ℝ)⁻¹ *
        (∫ ω, ‖∑ j : Fin N, Φ (ω j) - (N : ℝ) • ∫ x, Φ x ∂p‖
          ∂(Measure.pi fun _ : Fin N => p)) ≤
      2 * (N : ℝ)⁻¹ * ∑ σ : Fin N → Bool, (2 ^ N : ℝ)⁻¹ *
        (∫ ω, ‖∑ j : Fin N, (if σ j then (1 : ℝ) else -1) • Φ (ω j)‖
          ∂(Measure.pi fun _ : Fin N => p)) := by
  classical
  have hw : ∑ _σ : Fin N → Bool, (2 ^ N : ℝ)⁻¹ = 1 := by
    simp
  have hs := integral_norm_sum_sub_le p hint
    (fun (σ : Fin N → Bool) j => if σ j then (1 : ℝ) else -1)
    (fun _ => (2 ^ N : ℝ)⁻¹) (fun _ => by positivity) hw
    (fun σ j => by split <;> simp)
  calc
    _ ≤ (N : ℝ)⁻¹ * (2 * ∑ σ : Fin N → Bool, (2 ^ N : ℝ)⁻¹ *
        (∫ ω, ‖∑ j : Fin N, (if σ j then (1 : ℝ) else -1) • Φ (ω j)‖
          ∂(Measure.pi fun _ : Fin N => p))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- **Corollary [cor:vector-rates](i).** The exact integrated variance of the sampled network,
including the subtracted squared norm of its target and the zero-variation case. -/
theorem cor_vector_rates_i_exact {H Y : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] {β : ℝ → ℂ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y) [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ))
    (ζ : Measure H) [IsProbabilityMeasure ζ] (hζ : Integrable (fun x : H => ‖x‖ ^ 2) ζ)
    {N : ℕ} (hN : 0 < N) :
    ∫ θ, (∫ x, ‖polarSampledNetwork β Γ θ x - integralNetwork β Γ x‖ ^ 2 ∂ζ)
        ∂sampleLaw N (polarLaw Γ) =
      (N : ℝ)⁻¹ * (polarWeight Γ ^ 2 *
        (∫ θ, (∫ x, ‖β (⟪θ.1, x⟫ + θ.2)‖ ^ 2 ∂ζ) ∂polarLaw Γ) -
          ∫ x, ‖integralNetwork β Γ x‖ ^ 2 ∂ζ) := by
  exact integral_polarSampledNetwork_sq_eq hβ Γ hM ζ hζ hN

/-- **Lemma [lem:two-coordinate-comparison]** A two-coordinate Rademacher comparison.  For
bounded `ψ_i, u_i, v_i` on a nonempty set `S` whose increments satisfy
`|ψ_i(s) − ψ_i(t)| ≤ |u_i(s) − u_i(t)| + |v_i(s) − v_i(t)|`, the Rademacher average of
`sup_s ∑_i ε_i ψ_i(s)` is at most twice the average of
`sup_s ∑_i (ε_{i1} u_i(s) + ε_{i2} v_i(s))` over two independent sign vectors.  The averages
are the uniform averages over the Boolean sign vectors. -/
theorem lem_two_coordinate_comparison {S : Type*} [Nonempty S] {N : ℕ}
    {ψ u v : Fin N → S → ℝ} (hψ : ∀ i, ∃ C, ∀ s, |ψ i s| ≤ C)
    (hu : ∀ i, ∃ C, ∀ s, |u i s| ≤ C) (hv : ∀ i, ∃ C, ∀ s, |v i s| ≤ C)
    (hincr : ∀ i s t, |ψ i s - ψ i t| ≤ |u i s - u i t| + |v i s - v i t|) :
    (2 ^ N : ℝ)⁻¹ * ∑ ε : Fin N → Bool, ⨆ s, ∑ i, (if ε i then (1 : ℝ) else -1) * ψ i s ≤
      2 * ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹ *
        ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool, ⨆ s,
          ∑ i, ((if ε₁ i then (1 : ℝ) else -1) * u i s +
            (if ε₂ i then (1 : ℝ) else -1) * v i s)) := by
  exact avg_iSup_boolSignVector_le hψ hu hv hincr

end OperatorRidgelet.Paper
