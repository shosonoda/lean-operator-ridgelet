import OperatorRidgelet.Reconstruction.VectorBackprojection
import OperatorRidgelet.ToMathlib.FourierLpPairing
import OperatorRidgelet.ToMathlib.PartialFourierL2

/-! # Existence of vector-valued bias-Fourier representatives -/

noncomputable section
open MeasureTheory Complex Filter Topology
open scoped FourierTransform ComplexConjugate
namespace OperatorRidgelet
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The angular Fourier transform of a square-integrable vector-valued function. -/
def lineFourierL2Vec (u : ℝ → Y) (hu : MemLp u 2 volume) (ω : ℝ) : Y :=
  (𝓕 (hu.toLp u) : Lp Y 2 (volume : Measure ℝ)) ((2 * Real.pi)⁻¹ * ω)

/-- The angular L² Fourier transform is square integrable. -/
theorem memLp_lineFourierL2Vec {u : ℝ → Y} (hu : MemLp u 2 volume) :
    MemLp (lineFourierL2Vec u hu) 2 volume :=
  (Lp.memLp _).comp_mul_left (by positivity)

/-- Parseval against a Schwartz test function for the angular vector L² Fourier transform. -/
theorem integral_mul_conj_eq_lineFourierL2Vec {u : ℝ → Y} (hu : MemLp u 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    (∫ c, conj (φ c) • u c) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ ω, conj (lineFourier φ ω) • lineFourierL2Vec u hu ω := by
  simp_rw [lineFourier_eq_fourier (φ : ℝ → ℂ)]
  unfold lineFourierL2Vec
  rw [Measure.integral_comp_mul_left (fun x =>
      conj (𝓕 (φ : ℝ → ℂ) x) • (𝓕 (hu.toLp u) : Lp Y 2 volume) x)
      (2 * Real.pi)⁻¹, inv_inv, abs_of_pos (by positivity),
    smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  exact (integral_fourier_toLp_conj_smul_fourier_schwartz hu φ).symm


/-- Every strongly measurable square-integrable vector coefficient has a jointly strongly
measurable partial Fourier representative. -/
theorem exists_stronglyMeasurable_hasBiasFourierVec_of_memLp
    {H : Type*} [MeasurableSpace H] [SecondCountableTopology Y]
    {ν : Measure H} [SFinite ν] {γ : H × ℝ → Y}
    (hγ : StronglyMeasurable γ) (hγ₂ : MemLp γ 2 (ν.prod volume)) :
    ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
      HasBiasFourierVec ν γ Φ := by
  borelize Y
  obtain ⟨Φ, hΦm, _, hkey⟩ := exists_measurable_partialFourierL2 hγ.measurable hγ₂
  have hkey' : ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => γ (a, c)) 2 volume,
      (fun ω => Φ (a, (2 * Real.pi)⁻¹ * ω)) =ᵐ[volume]
        lineFourierL2Vec (fun c => γ (a, c)) hu := by
    filter_upwards [hkey] with a ha hu
    exact (quasiMeasurePreserving_mul_left_volume (by positivity)).ae_eq_comp (ha hu)
  refine ⟨fun a ω => Φ (a, (2 * Real.pi)⁻¹ * ω),
    (hΦm.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))).stronglyMeasurable,
    ?_, ?_⟩
  · filter_upwards [hkey', ae_memLp_slice_vec hγ₂] with a ha hu
    exact (memLp_lineFourierL2Vec hu).ae_eq (ha hu).symm
  · filter_upwards [hkey', ae_memLp_slice_vec hγ₂] with a ha hu φ
    rw [integral_mul_conj_eq_lineFourierL2Vec hu φ]
    congr 1
    apply integral_congr_ae
    filter_upwards [ha hu] with ω hω
    rw [hω]

/-- Every L² vector coefficient has a jointly strongly measurable bias-Fourier representative. -/
theorem exists_stronglyMeasurable_hasBiasFourierVec {H : Type*} [MeasurableSpace H]
    [SecondCountableTopology Y] {ν : Measure H} [SFinite ν]
    (γ : Lp Y 2 (parameterMeasure ν)) :
    ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
      HasBiasFourierVec ν γ Φ :=
  exists_stronglyMeasurable_hasBiasFourierVec_of_memLp (Lp.stronglyMeasurable γ) (Lp.memLp γ)

/-- On L² coefficients, backprojection always uses an actual Fourier representative. -/
theorem backprojectionVec_eq_of_exists {H : Type*} [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology Y]
    (α : ℝ) (ν : Measure H) [SFinite ν] (ρ : ℝ → ℝ)
    (γ : Lp Y 2 (parameterMeasure ν)) :
    ∃ Φ : H → ℝ → Y, StronglyMeasurable (Function.uncurry Φ) ∧
      HasBiasFourierVec ν γ Φ ∧ backprojectionVec α ν ρ γ = backprojectionOfVec α ρ Φ := by
  have hex := exists_stronglyMeasurable_hasBiasFourierVec γ
  exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, by
    unfold backprojectionVec
    rw [dif_pos hex]⟩

end OperatorRidgelet
