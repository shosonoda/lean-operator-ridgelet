import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Sampling.FirstMoment

/-! # Integrable Banach-valued sampling: manuscript statements -/

noncomputable section
namespace OperatorRidgelet.Paper
open MeasureTheory Filter Topology
open scoped ENNReal

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

end OperatorRidgelet.Paper
