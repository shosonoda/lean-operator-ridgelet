import OperatorRidgelet.Examples.LayerRegular
import OperatorRidgelet.Examples.LayerRidgelet

/-! # Ray regularity for vector-valued Gaussian layers -/

noncomputable section
set_option maxHeartbeats 800000
namespace OperatorRidgelet
open MeasureTheory Complex Filter Topology
open scoped ENNReal RealInnerProductSpace Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] {Ω : Type*} [MeasurableSpace Ω]
  {m : Measure Ω} {a : Ω → H} {b : Ω → Y}

/-- Use the Borel measurable structure on the vector output space. -/
local instance : MeasurableSpace Y := borel Y
/-- The chosen measurable structure is the Borel structure. -/
local instance : BorelSpace Y := ⟨rfl⟩

/-- The constant vector in the Gaussian spectral density of a layer. -/
def layerDensityConstVec (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (y : Ω) : Y :=
  (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ : ℝ) : ℂ) • b y

/-- The Gaussian spectral density associated with one direction of a layer. -/
def layerDensityVec (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (y : Ω) (ξ : H) : Y :=
  (((Real.sqrt (1 + ⟪Q (a y), a y⟫))⁻¹ *
    Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) • b y

/-- The vector layer density separates into its ray profile and radial exponential factor. -/
theorem layerDensityVec_eq (Q : H →L[ℝ] H) (a : Ω → H) (b : Ω → Y) (y : Ω) (ξ : H) :
    layerDensityVec Q a b y ξ =
      ((Real.exp (-⟪layerCovariance Q a y ξ, ξ⟫ / 2) : ℝ) : ℂ) • layerDensityConstVec Q a b y := by
  simp only [layerDensityVec, layerDensityConstVec, Complex.ofReal_mul, smul_smul]
  rw [mul_comm]

/-- The vector ray profile has norm bounded by the output vector's norm. -/
theorem norm_layerDensityConstVec_le {Q : H →L[ℝ] H} (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫)
    (a : Ω → H) (b : Ω → Y) (y : Ω) : ‖layerDensityConstVec Q a b y‖ ≤ ‖b y‖ := by
  rw [layerDensityConstVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ?_)
  exact Real.one_le_sqrt.mpr (by linarith [hQ0 (a y)])

/-- Positivity of the covariance bounds the full density by the output vector's norm. -/
theorem norm_layerDensityVec_le {Q : H →L[ℝ] H} (hQ0 : ∀ x, 0 ≤ ⟪Q x, x⟫)
    (a : Ω → H) (b : Ω → Y) (y : Ω) {ξ : H} (hS0 : 0 ≤ ⟪layerCovariance Q a y ξ, ξ⟫) :
    ‖layerDensityVec Q a b y ξ‖ ≤ ‖b y‖ := by
  rw [layerDensityVec_eq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    (norm_layerDensityConstVec_le hQ0 a b y)
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- The vector layer density is jointly measurable in its spatial and frequency parameters. -/
theorem IsLayerData.measurable_uncurry_layerDensityVec {Q : H →L[ℝ] H}
    (hL : IsLayerData m a b) : Measurable (Function.uncurry (layerDensityVec Q a b)) := by
  have hA : StronglyMeasurable fun p : Ω × H => a p.1 :=
    hL.stronglyMeasurable_a.comp_measurable measurable_fst
  have hx : StronglyMeasurable fun p : Ω × H => p.2 := measurable_snd.stronglyMeasurable
  have hQa := Q.continuous.comp_stronglyMeasurable hA
  have hQx := Q.continuous.comp_stronglyMeasurable hx
  have h1 : Measurable fun p : Ω × H => ⟪Q (a p.1), p.2⟫ := (hQa.inner hx).measurable
  have h2 : Measurable fun p : Ω × H => ⟪Q p.2, p.2⟫ := (hQx.inner hx).measurable
  have h3 : Measurable fun p : Ω × H => ⟪Q (a p.1), a p.1⟫ := (hQa.inner hA).measurable
  have hκ : Measurable fun p : Ω × H => ⟪layerCovariance Q a p.1 p.2, p.2⟫ := by
    have heq : (fun p : Ω × H => ⟪layerCovariance Q a p.1 p.2, p.2⟫) =
        fun p : Ω × H => ⟪Q p.2, p.2⟫ - ⟪Q (a p.1), p.2⟫ ^ 2 / (1 + ⟪Q (a p.1), a p.1⟫) :=
      funext fun p => inner_layerCovariance Q a p.1 p.2
    rw [heq]
    exact h2.sub ((h1.pow_const 2).div (measurable_const.add h3))
  have hconst : Measurable fun p : Ω × H => (((Real.sqrt (1 + ⟪Q (a p.1), a p.1⟫))⁻¹ : ℝ) : ℂ)
      := Complex.measurable_ofReal.comp
    ((Real.continuous_sqrt.measurable.comp (measurable_const.add h3)).inv)
  have hexp : Measurable fun p : Ω × H =>
      ((Real.exp (-⟪layerCovariance Q a p.1 p.2, p.2⟫ / 2) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hκ.neg.div_const 2))
  have heq : Function.uncurry (layerDensityVec Q a b) = fun p : Ω × H =>
      ((((Real.sqrt (1 + ⟪Q (a p.1), a p.1⟫))⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-⟪layerCovariance Q a p.1 p.2, p.2⟫ / 2) : ℝ) : ℂ)) • b p.1 := by
    funext p
    simp only [Function.uncurry, layerDensityVec, Complex.ofReal_mul]
  rw [heq]
  exact (hconst.mul hexp).smul (hL.stronglyMeasurable_b.measurable.comp measurable_fst)

/-- The complex embedding of the radial exponential factor is smooth. -/
theorem contDiff_ofReal_exp_layer (S : H →L[ℝ] H) (a : H) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun ω : ℝ => ((Real.exp (-⟪S (ω • a), ω • a⟫ / 2) : ℝ) : ℂ) := by
  simpa using contDiff_const_mul_ofReal_exp_inner_map_smul_self S 1 a

variable [IsFiniteMeasure m]

/-- **Example `ex:operator-layer`(ii)**: the transform `𝒢_Q F_φ` of the scalar observable of a
layer with Gaussian activation is regular along rays, for every compact frequency window away
from the origin.  The densities `G_y` are Gaussian with covariances `S_y` satisfying
`θ Q ≤ S_y` and `‖S_y‖ ≤ ‖Q‖ + ‖Q‖²‖A‖_∞²` uniformly in `y`, so the ray-derivative bounds are
uniform in `y` up to the factor `|w_φ(y)|`, and the weighted form of Lemma
`lem:ray-regular-examples`(c) applies. -/
theorem IsLayerData.isRegularAlongRays_gaussFourierVec_operatorLayer_gaussianFun
    {Q : H →L[ℝ] H} (hQ : IsPositiveTraceClass Q) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Q μ) (hL : IsLayerData m a b) (ν : Measure H)
    (hdecay : ∀ t : ℝ, 0 < t → ∀ k : ℕ,
      Integrable (fun ξ : H => ‖ξ‖ ^ (2 * k) * Real.exp (-t * ⟪Q ξ, ξ⟫)) ν)
    {I : Set ℝ} (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) :
    IsRegularAlongRays ν I (gaussFourierVec μ (operatorLayer m a b gaussianFun)) := by
  obtain ⟨r, R, hr, hrR⟩ := hI.exists_pos_le_abs_le hI0
  have hθ : (0 : ℝ) < (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹ := by positivity
  have ht : (0 : ℝ) < ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) :=
    mul_pos (div_pos (pow_pos (by linarith) 2) two_pos) hθ
  have hSB : ∀ y : Ω, ‖layerCovariance Q a y‖ ≤ (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) :=
    fun y => hL.norm_layerCovariance_le hQ.inner_nonneg y
  have hS0 : ∀ (y : Ω) (ξ : H), 0 ≤ ⟪layerCovariance Q a y ξ, ξ⟫ := fun y ξ =>
    le_trans (mul_nonneg hθ.le (hQ.inner_nonneg ξ)) (hL.inner_layerCovariance_ge hQ y ξ)
  -- the transform is the Bochner integral of the Gaussian densities
  have hGfun : gaussFourierVec μ (operatorLayer m a b gaussianFun) =
      fun ξ => ∫ y, layerDensityVec Q a b y ξ ∂m :=
    funext fun ξ =>
      hL.gaussFourierVec_operatorLayer_gaussianFun' hQ.isSelfAdjoint hQ.inner_nonneg hμ ξ
  rw [hGfun]
  -- an open annulus around the window
  have hU : IsOpen ({ω : ℝ | r / 2 < |ω|} ∩ {ω : ℝ | |ω| < R + 1}) :=
    (isOpen_lt continuous_const continuous_abs).inter (isOpen_lt continuous_abs continuous_const)
  have hIU : I ⊆ {ω : ℝ | r / 2 < |ω|} ∩ {ω : ℝ | |ω| < R + 1} := fun ω hω =>
    ⟨by have := (hrR ω hω).1; simp only [Set.mem_setOf_eq]; linarith,
     by have := (hrR ω hω).2; simp only [Set.mem_setOf_eq]; linarith⟩
  refine IsRegularAlongRays.integral_weighted_of_measurable_derivatives m
      (hL.measurable_uncurry_layerDensityVec (Q := Q))
    (W := fun y => ‖b y‖) hL.integrable_b.norm
    (fun y => norm_nonneg _)
    (fun y ξ => norm_layerDensityVec_le hQ.inner_nonneg a b y (hS0 y ξ)) hU hIU
    (fun y a' => ?_) (fun a' k t ht' => ?_) (fun k => ?_)
  · have hfun : (fun ω : ℝ => layerDensityVec Q a b y (ω • a')) =
        fun ω : ℝ => ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ) •
          layerDensityConstVec Q a b y :=
      funext fun ω => layerDensityVec_eq Q a b y (ω • a')
    rw [hfun]
    exact ((contDiff_ofReal_exp_layer (layerCovariance Q a y) a').smul contDiff_const).contDiffOn
  · have hLs : IsLayerData m a (fun _ : Ω => (1 : ℂ)) :=
      ⟨hL.stronglyMeasurable_a, hL.bounded_a, stronglyMeasurable_const, integrable_const _⟩
    let F := layerDensity Q a (fun _ : Ω => (1 : ℂ)) (1 : ℂ)
    have hF : ∀ y, ContDiff ℝ (⊤ : ℕ∞) (fun ω : ℝ => F y (ω • a')) := by
      intro y
      simpa only [F, layerDensity_eq] using
        contDiff_const_mul_ofReal_exp_inner_map_smul_self (layerCovariance Q a y)
          (layerDensityConst Q a (fun _ : Ω => (1 : ℂ)) 1 y) a'
    have hm := measurable_iteratedDeriv_of_forall_contDiffOn (x := t)
      (f := fun y ω => F y (ω • a'))
      (fun t => (hLs.measurable_uncurry_layerDensity (Q := Q) (1 : ℂ)).comp
        (measurable_id.prodMk measurable_const))
      (fun y => ⟨Set.univ, isOpen_univ, Set.mem_univ _, (hF y).contDiffOn⟩) k
    have heq : (fun y => iteratedDeriv k (fun ω : ℝ => layerDensityVec Q a b y (ω • a')) t) =
        fun y => iteratedDeriv k (fun ω : ℝ => F y (ω • a')) t • b y := by
      funext y
      have hfun : (fun ω : ℝ => layerDensityVec Q a b y (ω • a')) =
          fun ω : ℝ => F y (ω • a') • b y := by
        simp [F, layerDensityVec, layerDensity, layerWeight]
      rw [hfun, iteratedDeriv_smul_const ((hF y).of_le (by exact_mod_cast le_top)).contDiffAt]
    rw [heq]
    exact hm.aestronglyMeasurable.smul hL.stronglyMeasurable_b.aestronglyMeasurable
  -- the uniform ray-derivative bound
  refine ⟨fun a' => ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
      (1 + ‖a'‖) ^ 2) ^ k *
    (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) *
        ⟪Q a', a'⟫), fun a' => by positivity, ?_, ?_⟩
  · -- integrability of the weight
    have hint : Integrable (fun a' : H =>
        (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
            (1 + |R + 1|) ^ k) * 2 ^ (3 * k + 2) *
          (2 + ‖a'‖ ^ (2 * (3 * k + 2))) *
              Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)) ν := by
      have h0 := hdecay ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) ht 0
      have hN := hdecay ((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) ht (3 * k + 2)
      simp only [mul_zero, pow_zero, one_mul] at h0
      refine (((h0.const_mul 2).add hN).const_mul
        ((((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
            (1 + |R + 1|) ^ k) *
          2 ^ (3 * k + 2))).congr (Filter.Eventually.of_forall fun a' => ?_)
      simp only [Pi.add_apply]
      ring
    refine lt_of_le_of_lt (lintegral_mono fun a' => ?_) hint.lintegral_lt_top
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    beta_reduce
    have ha1 : (1 : ℝ) ≤ (1 + ‖a'‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg a'])
    have hstep : ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k ≤
        ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k * (1 + ‖a'‖) ^ (2 * k) := by
      have hnn : (0 : ℝ) ≤
          (k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 := by positivity
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hle : (k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 ≤
          ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) * (1 + ‖a'‖) ^ 2 := by
        nlinarith [ha1, hk0, mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)
          (show (0 : ℝ) ≤ (1 + ‖a'‖) ^ 2 - 1 by linarith)]
      calc ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k
          ≤ (((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) * (1 + ‖a'‖) ^ 2) ^ k :=
            pow_le_pow_left₀ hnn hle k
        _ = ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
              (1 + ‖a'‖) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    have hpow : (1 + ‖a'‖) ^ (k + 2) * (1 + ‖a'‖) ^ (2 * k) ≤
        2 ^ (3 * k + 2) * (2 + ‖a'‖ ^ (2 * (3 * k + 2))) := by
      rw [← pow_add]
      have hidx : k + 2 + 2 * k = 3 * k + 2 := by ring
      rw [hidx]
      exact one_add_pow_le_two_pow_mul_two_add_pow (3 * k + 2) (norm_nonneg a')
    calc (1 + ‖a'‖) ^ (k + 2) *
        (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k *
          (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) *
              ⟪Q a', a'⟫))
        ≤ (1 + ‖a'‖) ^ (k + 2) * (((k : ℝ) + 1) *
            (((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k * (1 + ‖a'‖) ^ (2 * k)) *
            (1 + |R + 1|) ^ k * Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹)
                * ⟪Q a', a'⟫)) := by gcongr
      _ = (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) *
            ((1 + ‖a'‖) ^ (k + 2) * (1 + ‖a'‖) ^ (2 * k)) *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) := by ring
      _ ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) *
            (2 ^ (3 * k + 2) * (2 + ‖a'‖ ^ (2 * (3 * k + 2)))) *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)
                := by gcongr
      _ = (((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2)) ^ k *
          (1 + |R + 1|) ^ k) * 2 ^ (3 * k + 2) *
            (2 + ‖a'‖ ^ (2 * (3 * k + 2))) *
                Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)
                := by ring
  · -- the pointwise bound on the ray derivatives
    intro y a'
    refine iSup_le fun j => iSup₂_le fun ω hω => ?_
    have hωr : r / 2 ≤ |ω| := le_of_lt hω.1
    have hωR : |ω| ≤ R + 1 := le_of_lt hω.2
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
    have hjkR : ((j : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    have hfun : (fun ω : ℝ => layerDensityVec Q a b y (ω • a')) =
        fun ω : ℝ => ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ) •
          layerDensityConstVec Q a b y :=
      funext fun ω => layerDensityVec_eq Q a b y (ω • a')
    rw [← ofReal_norm, hfun]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [iteratedDeriv_smul_const
        (contDiff_ofReal_exp_layer (layerCovariance Q a y) a').contDiffAt, norm_smul, mul_comm]
    have hd := norm_iteratedDeriv_ofReal_exp_inner_map_smul_self_le (hS0 y) (hSB y)
      (r := r / 2) (by positivity) (R := R + 1) (j : ℕ) a' hωr hωR
    have hA1 : ((j : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 1 := by linarith
    have hA2 : (((j : ℕ) : ℝ) + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ (j : ℕ) ≤
        ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k := by
      refine le_trans (pow_le_pow_left₀ (by positivity) (by linarith) (j : ℕ))
        (pow_le_pow_right₀ ?_ hjk)
      have : (0 : ℝ) ≤ (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2 := by positivity
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hA3 : (1 + |R + 1|) ^ (j : ℕ) ≤ (1 + |R + 1|) ^ k :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (R + 1)]) hjk
    have hA4 : Real.exp (-((r / 2) ^ 2 / 2) * ⟪layerCovariance Q a y a', a'⟫) ≤
        Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) := by
      rw [Real.exp_le_exp]
      have h1 := hL.inner_layerCovariance_ge hQ y a'
      nlinarith [sq_nonneg (r / 2), hQ.inner_nonneg a', div_nonneg (sq_nonneg (r / 2)) two_pos.le]
    have hstep : ‖iteratedDeriv (j : ℕ) (fun ω : ℝ =>
          ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ)) ω‖ ≤
        ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
            (1 + ‖a'‖) ^ 2) ^ k * (1 + |R + 1|) ^ k *
          Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) :=
      hd.trans (by
        refine mul_le_mul (mul_le_mul (mul_le_mul hA1 hA2 (by positivity) (by positivity)) hA3
          (by positivity) (by positivity)) hA4 (Real.exp_nonneg _) (by positivity))
    calc ‖layerDensityConstVec Q a b y‖ *
          ‖iteratedDeriv (j : ℕ) (fun ω : ℝ =>
            ((Real.exp (-⟪layerCovariance Q a y (ω • a'), ω • a'⟫ / 2) : ℝ) : ℂ)) ω‖
        ≤ ‖b y‖ * (((k : ℝ) + 1) *
            ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) * (1 + ‖a'‖) ^ 2) ^ k *
                (1 + |R + 1|) ^ k *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫)) :=
          mul_le_mul (norm_layerDensityConstVec_le hQ.inner_nonneg a b y) hstep
            (norm_nonneg _) (norm_nonneg _)
      _ = ((k : ℝ) + 1) * ((k : ℝ) + 1 + (‖Q‖ + ‖Q‖ ^ 2 * layerSupNorm a ^ 2) *
          (1 + ‖a'‖) ^ 2) ^ k * (1 + |R + 1|) ^ k *
            Real.exp (-((r / 2) ^ 2 / 2 * (1 + ‖Q‖ * layerSupNorm a ^ 2)⁻¹) * ⟪Q a', a'⟫) *
                ‖b y‖ := by ring


end OperatorRidgelet
