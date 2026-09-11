import OperatorRidgelet.Reconstruction.VectorValued
import OperatorRidgelet.Reconstruction.Hermite

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

/-- Fubini identifies the pairing of a vector spectral target with its Fourier pairing. -/
theorem integral_inner_spectralTarget (μ ν : Measure H) [SFinite μ] [SFinite ν]
    {G g : H → Y} (hG : Integrable G ν) (hg : Integrable g μ) :
    ∫ x, inner ℂ (g x) (spectralTarget ν G x) ∂μ =
      ∫ ξ, inner ℂ (gaussFourierVec μ g ξ) (G ξ) ∂ν := by
  have hint : Integrable (fun z : H × H =>
      inner ℂ (g z.1) (Complex.exp ((⟪z.1, z.2⟫ : ℝ) * Complex.I) • G z.2))
      (μ.prod ν) := by
    refine ((hg.norm.mul_prod hG.norm).mono' ?_ ?_)
    · exact (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).inner
        (((by fun_prop : Continuous fun z : H × H =>
          Complex.exp ((⟪z.1, z.2⟫ : ℝ) * Complex.I))).aestronglyMeasurable.smul
          (hG.aestronglyMeasurable.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd))
    · filter_upwards with z
      simpa only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
        using norm_inner_le_norm (g z.1)
          (Complex.exp ((⟪z.1, z.2⟫ : ℝ) * Complex.I) • G z.2)
  have hL : ∀ x, inner ℂ (g x) (spectralTarget ν G x) =
      ∫ ξ, inner ℂ (g x) (Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • G ξ) ∂ν := by
    intro x
    exact ((innerSL ℂ (g x)).integral_comp_comm
      (hG.smul_of_top_right (memLp_top_of_bound
        (by fun_prop : Continuous fun ξ : H =>
          Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I)).aestronglyMeasurable
        1 (Eventually.of_forall fun ξ => (Complex.norm_exp_ofReal_mul_I _).le)))).symm
  simp_rw [hL]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards with ξ
  have hgξ : Integrable (fun x => character ξ x • g x) μ := by
    refine hg.smul_of_top_right (memLp_top_of_bound ?_ 1 ?_)
    · exact (continuous_character ξ).aestronglyMeasurable
    · filter_upwards with x
      exact (norm_character ξ x).le
  have hi : inner ℂ (∫ x, character ξ x • g x ∂μ) (G ξ) =
      ∫ x, inner ℂ (character ξ x • g x) (G ξ) ∂μ := by
    calc
      _ = (starRingEnd ℂ) (inner ℂ (G ξ) (∫ x, character ξ x • g x ∂μ)) :=
        (inner_conj_symm _ _).symm
      _ = _ := by
        rw [← integral_inner hgξ, ← integral_conj]
        simp only [inner_conj_symm]
  rw [gaussFourierVec, hi]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_smul_left, inner_smul_right, character, ← Complex.exp_conj,
    map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

/-- The transpose of the vector spectral embedding is represented by its spectral target. -/
theorem transposeEmbedVec_apply_eq_integral (μ ν : Measure H) [IsFiniteMeasure μ] [SFinite ν]
    (G : Lp Y 2 ν) (hG : Integrable (G : H → Y) ν) (g : spectralCoreVec Y μ ν) :
    transposeEmbedVec μ ν G (spectralEmbedVec μ ν g) =
      ∫ x, inner ℂ ((g : Lp Y 2 μ) x) (spectralTarget ν (G : H → Y) x) ∂μ := by
  rw [integral_inner_spectralTarget μ ν hG ((Lp.memLp _).integrable one_le_two)]
  change inner ℂ (gaussFourierLpVec μ ν g) G = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.2.coeFn_toLp] with ξ hξ
  rw [show gaussFourierLpVec μ ν g ξ = gaussFourierVec μ (g : Lp Y 2 μ) ξ from hξ]

open ProbabilityTheory in
/-- Continuous scalar testing commutes with vector Hermite coefficients. -/
theorem inner_hermiteCoefficientVec (μ : Measure H) {Q : H →L[ℝ] H}
    (hμ : IsCenteredGaussian Q μ) {f : H → Y} (hf : MemLp f 2 μ)
    {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (n : ℕ) (y : Y) :
    inner ℂ y (hermiteCoefficientVec μ Q f ξ n) =
      hermiteCoefficient μ Q (fun x => inner ℂ y (f x)) ξ n := by
  have hcoord := isStdGaussianCoord_inner_div hμ ξ hpos
  have hint : Integrable (fun x => hermiteC n (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) • f x) μ :=
    memLp_one_iff_integrable.mp
      (MemLp.smul (p := 2) (q := 2) (r := 1) hf
        (hcoord.memLp_comp (memLp_two_hermiteC n)))
  simp only [hermiteCoefficientVec, hermiteCoefficient,
    Polynomial.aeval_hermite_eq_eval_hermiteR]
  change inner ℂ y (∫ x, hermiteC n (⟪x, ξ⟫ / Real.sqrt ⟪Q ξ, ξ⟫) • f x ∂μ) = _
  rw [← integral_inner hint]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_smul_right, hermiteC]
  ring

/-- Scalar Hermite totality yields totality in a separable complex Hilbert target. -/
theorem ae_eq_of_hermiteCoefficientVec_eq [CompleteSpace H] [Nontrivial H]
    {μ : Measure H} {Q : H →L[ℝ] H} (hQ : IsTraceClassCovariance Q)
    (hμ : IsCenteredGaussian Q μ) {f g : H → Y} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hcoeff : ∀ ξ : H, ξ ≠ 0 → ∀ n : ℕ,
      hermiteCoefficientVec μ Q f ξ n = hermiteCoefficientVec μ Q g ξ n) :
    f =ᵐ[μ] g := by
  have hy : ∀ y : Y, (fun x => inner ℂ y (f x)) =ᵐ[μ] fun x => inner ℂ y (g x) := by
    intro y
    refine ae_eq_of_hermiteCoefficient_eq hQ hμ (hf.const_inner y) (hg.const_inner y) ?_
    intro ξ hξ n
    rw [← inner_hermiteCoefficientVec μ hμ hf (hQ.inner_pos hξ),
      ← inner_hermiteCoefficientVec μ hμ hg (hQ.inner_pos hξ), hcoeff ξ hξ n]
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  have hD : ∀ᵐ x ∂μ, ∀ y ∈ D, inner ℂ y (f x) = inner ℂ y (g x) :=
    (ae_ball_iff hDc).mpr fun y _ => hy y
  filter_upwards [hD] with x hx
  have hfun : (fun y : Y => inner ℂ y (f x)) = fun y => inner ℂ y (g x) :=
    Continuous.ext_on hDd (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const) hx
  exact ext_inner_left ℂ (fun y => congrFun hfun y)

end OperatorRidgelet
