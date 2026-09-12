import OperatorRidgelet.Reconstruction.VectorBiasFourier
import OperatorRidgelet.ToMathlib.PartialFourierUnitary

/-! # The partial bias Fourier unitary and its measurable representatives -/

noncomputable section
open MeasureTheory Complex Filter Topology
open scoped FourierTransform ComplexConjugate ENNReal
namespace OperatorRidgelet
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
variable {H : Type*} [MeasurableSpace H] [SecondCountableTopology Y]
variable (ν : Measure H) [SFinite ν]

/-- The angular partial Fourier unitary has jointly strongly measurable bias-Fourier
representatives, with its target measure normalized by `1 / (2π)`. -/
theorem exists_hasBiasFourierVec_angularPartialFourierL2Equiv
    (γ : Lp Y 2 (parameterMeasure ν)) :
    ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
      HasBiasFourierVec ν γ Φ ∧
      Function.uncurry Φ =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)]
        ⇑(angularPartialFourierL2Equiv ν γ) := by
  let Ψ := partialFourierL2Rep ν γ
  have hΨ := partialFourierL2Rep_spec ν γ
  have hkey : ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      (fun ω => Ψ (a, (2 * Real.pi)⁻¹ * ω)) =ᵐ[volume]
        lineFourierL2Vec (fun c => γ (a, c)) hu := by
    filter_upwards [hΨ.2.2] with a ha hu
    exact (quasiMeasurePreserving_mul_left_volume (by positivity)).ae_eq_comp (ha hu)
  refine ⟨fun a ω => Ψ (a, (2 * Real.pi)⁻¹ * ω), ?_, ?_,
    (angularPartialFourierL2Equiv_coe_rep ν γ).symm⟩
  · exact hΨ.1.comp_measurable
      (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  · refine ⟨?_, ?_⟩
    · filter_upwards [hkey, ae_memLp_slice_vec (Lp.memLp γ)] with a ha hu
      exact (memLp_lineFourierL2Vec hu).ae_eq (ha hu).symm
    · filter_upwards [hkey, ae_memLp_slice_vec (Lp.memLp γ)] with a ha hu φ
      rw [integral_mul_conj_eq_lineFourierL2Vec hu φ]
      congr 1
      apply integral_congr_ae
      filter_upwards [ha hu] with ω hω
      rw [hω]

/-- Partial bias Fourier transformation is a unitary with jointly measurable representatives
satisfying the Fourier-Schwartz characterization on almost every bias slice. -/
theorem exists_unitary_hasBiasFourierVec :
    ∃ U : Lp Y 2 (parameterMeasure ν) ≃ₗᵢ[ℂ]
      Lp Y 2 (ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • (volume : Measure ℝ))),
      ∀ γ : Lp Y 2 (parameterMeasure ν),
        ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
        HasBiasFourierVec ν γ Φ ∧
        Function.uncurry Φ =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)] ⇑(U γ) :=
  ⟨angularPartialFourierL2Equiv ν, exists_hasBiasFourierVec_angularPartialFourierL2Equiv ν⟩

end OperatorRidgelet
