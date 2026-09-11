import OperatorRidgelet.Reconstruction.VectorFrame
import OperatorRidgelet.ToMathlib.ContDiffOnParametricIntegral

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y]

/-- All polynomial moments of a Gaussian coordinate times an `L²` target are integrable. -/
theorem integrable_inner_norm_pow_mul_norm {μ : Measure H} {Q : H →L[ℝ] H}
    (hμ : IsCenteredGaussian Q μ) {f : H → Y} (hf : MemLp f 2 μ)
    {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (k : ℕ) :
    Integrable (fun x => ‖(⟪x, ξ⟫ : ℝ)‖ ^ k * ‖f x‖) μ := by
  haveI := hμ.isProbabilityMeasure
  have hm := (continuous_id.inner continuous_const : Continuous fun x : H => ⟪x, ξ⟫).measurable
  have hp : MemLp (fun x : H => ⟪x, ξ⟫) ((2 * k : ℕ) : ℝ≥0∞) μ := by
    have hp := memLp_id_gaussianReal' (μ := 0) (v := Real.toNNReal ⟪Q ξ, ξ⟫)
      ((2 * k : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)
    rw [← hμ.map_inner_eq_gaussianReal ξ hpos.le] at hp
    exact hp.comp_of_map hm.aemeasurable
  have hp₂ : MemLp (fun x : H => ‖(⟪x, ξ⟫ : ℝ)‖ ^ k) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hm.norm.pow_const k).aestronglyMeasurable).mpr
    convert hp.integrable_norm_pow' using 1
    funext x
    rw [← pow_mul, Nat.mul_comm]
    rfl
  exact hp₂.integrable_mul hf.norm

/-- Derivatives of the Fourier-line kernel, with real parameter. -/
theorem iteratedDeriv_fourierLine_kernel (f : H → Y) (ξ : H) (x : H) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => Complex.exp (-((s : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I)) • f x) t =
      ((-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) ^ k *
        Complex.exp (-((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I))) • f x := by
  have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => Complex.exp (-((s : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I))) := by fun_prop
  rw [iteratedDeriv_smul_const
    (hc.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))]
  congr 1
  have he : (fun s : ℝ => Complex.exp (-((s : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I))) =
      fun s : ℝ => Complex.exp ((-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * (s : ℂ)) := by
    funext s
    congr 1
    ring
  rw [he, iteratedDeriv_comp_ofReal k (fun z : ℂ =>
    Complex.exp ((-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * z)) (by fun_prop),
    iteratedDeriv_cexp_const_mul]
  congr 2
  ring

/-- The vector Fourier transform along a Gaussian ray is smooth on the real line. -/
theorem contDiff_gaussFourierLineVec_real {μ : Measure H} {Q : H →L[ℝ] H}
    (hμ : IsCenteredGaussian Q μ) {f : H → Y} (hf : MemLp f 2 μ)
    {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => gaussFourierLineVec μ f ξ t) := by
  have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  apply contDiffOn_univ.mp
  apply contDiffOn_integral_of_dominated isOpen_univ
    (fun x => (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      Complex.exp (-((s : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I)) • f x)).contDiffOn)
  · intro k t _
    simp_rw [iteratedDeriv_fourierLine_kernel]
    exact (by fun_prop : Continuous fun x : H =>
      (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) ^ k *
        Complex.exp (-((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I))).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  · intro k
    refine ⟨fun x => ‖(⟪x, ξ⟫ : ℝ)‖ ^ k * ‖f x‖,
      integrable_inner_norm_pow_mul_norm hμ hf hpos k, fun x t _ => ?_⟩
    rw [iteratedDeriv_fourierLine_kernel, norm_smul, norm_mul, norm_pow,
      norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one]
    have he : -((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I) =
        ((-(t * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The real restriction of the vector Hermite extension is smooth. -/
theorem contDiff_hermiteExtensionVec_real {μ : Measure H} {Q : H →L[ℝ] H}
    (hμ : IsCenteredGaussian Q μ) {f : H → Y} (hf : MemLp f 2 μ)
    {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => hermiteExtensionVec μ Q f ξ t) := by
  have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  exact (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ =>
    Complex.exp ((t : ℂ) ^ 2 * ((⟪Q ξ, ξ⟫ : ℝ) : ℂ) / 2)).smul
      (contDiff_gaussFourierLineVec_real hμ hf hpos)

/-- Scalar testing of the vector Hermite extension, on its real restriction. -/
theorem inner_hermiteExtensionVec_real (μ : Measure H) [IsFiniteMeasure μ]
    (Q : H →L[ℝ] H) (f : Lp Y 2 μ) (ξ : H) (t : ℝ) (y : Y) :
    inner ℂ y (hermiteExtensionVec μ Q f ξ t) =
      hermiteExtension μ Q (fun x => inner ℂ y (f x)) ξ t := by
  have hint : Integrable (fun x =>
      Complex.exp (-((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I)) • f x) μ := by
    apply ((Lp.memLp f).integrable one_le_two).smul_of_top_right
    refine memLp_top_of_bound (by fun_prop : Continuous fun x : H =>
      Complex.exp (-((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I))).aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [show -((t : ℂ) * (⟪x, ξ⟫ : ℝ) * Complex.I) =
      ((-(t * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  unfold hermiteExtensionVec hermiteExtension gaussFourierLineVec gaussFourierLine
  rw [inner_smul_right, ← integral_inner hint]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_smul_right, mul_comm]

/-- Hermite inversion for a Hilbert-valued target follows by continuous scalar testing. -/
theorem hermiteCoefficientVec_eq_iteratedDeriv (μ : Measure H) [IsFiniteMeasure μ]
    {Q : H →L[ℝ] H} (hμ : IsCenteredGaussian Q μ) (f : Lp Y 2 μ)
    {ξ : H} (hpos : 0 < ⟪Q ξ, ξ⟫) (n : ℕ) :
    hermiteCoefficientVec μ Q f ξ n =
      (Complex.I ^ n / ((Real.sqrt ⟪Q ξ, ξ⟫ : ℝ) : ℂ) ^ n) •
        iteratedDeriv n (fun t : ℝ => hermiteExtensionVec μ Q f ξ t) 0 := by
  apply ext_inner_left ℂ
  intro y
  rw [inner_hermiteCoefficientVec μ hμ (Lp.memLp f) hpos,
    inner_smul_right, hermiteCoefficient_eq_iteratedDeriv hμ ((Lp.memLp f).const_inner y) hpos]
  congr 1
  have hfun : (fun t : ℝ => hermiteExtension μ Q (fun x => inner ℂ y (f x)) ξ t) =
      ((innerSL ℂ y).restrictScalars ℝ) ∘
        (fun t : ℝ => hermiteExtensionVec μ Q f ξ t) := by
    funext t
    exact (inner_hermiteExtensionVec_real μ Q f ξ t y).symm
  rw [hfun, iteratedDeriv,
    ((innerSL ℂ y).restrictScalars ℝ).iteratedFDeriv_comp_left
      (contDiff_hermiteExtensionVec_real hμ (Lp.memLp f) hpos).contDiffAt
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  rfl

end OperatorRidgelet
