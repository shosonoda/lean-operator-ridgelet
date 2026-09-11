import OperatorRidgelet.Examples.ConvolutionSpectrum
import OperatorRidgelet.ToMathlib.NuclearTrace
import OperatorRidgelet.ToMathlib.QuadraticLatticeSummability

/-! # Trace-class Bessel covariance on the torus

The operator is constructed as a summable series of positive rank-one operators on the real
cosine and sine components of the Fourier basis. Coefficient uniqueness identifies this
construction with the Bessel multiplier.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ComplexConjugate



namespace OperatorRidgelet
variable {d : ℕ}

def torusCosine (n : Fin d → ℤ) : TorusL2 d := Complex.reCLM.compLp (torusFourierBasis d n)
def torusSine (n : Fin d → ℤ) : TorusL2 d := Complex.imCLM.compLp (torusFourierBasis d n)

theorem torusCharacter_neg_index (n : Fin d → ℤ) (t : Torus d) :
    torusCharacter (-n) t = conj (torusCharacter n t) := by
  simp only [torusCharacter, Pi.neg_apply, fourier_neg, map_prod]

theorem ofReal_torusCosine (n : Fin d → ℤ) :
    Complex.ofRealCLM.compLp (torusCosine n) =
      (1/2 : ℂ) • (torusFourierBasis d n + torusFourierBasis d (-n)) := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' (torusCosine n),
    Complex.reCLM.coeFn_compLp' (torusFourierBasis d n),
    Lp.coeFn_smul (1/2 : ℂ) (torusFourierBasis d n + torusFourierBasis d (-n)),
    Lp.coeFn_add (torusFourierBasis d n) (torusFourierBasis d (-n)),
    torusFourierBasis_coeFn n, torusFourierBasis_coeFn (-n)] with t h1 h2 h3 h4 h5 h6
  dsimp only [torusCosine] at h1 ⊢
  rw [h1, h2, h3, Pi.smul_apply, h4, Pi.add_apply, h5, h6, torusCharacter_neg_index]
  simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, smul_eq_mul]
  rw [Complex.re_eq_add_conj]
  ring

theorem ofReal_torusSine (n : Fin d → ℤ) :
    Complex.ofRealCLM.compLp (torusSine n) =
      (1/(2*Complex.I) : ℂ) • (torusFourierBasis d n - torusFourierBasis d (-n)) := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' (torusSine n),
    Complex.imCLM.coeFn_compLp' (torusFourierBasis d n),
    Lp.coeFn_smul (1/(2*Complex.I) : ℂ) (torusFourierBasis d n - torusFourierBasis d (-n)),
    Lp.coeFn_sub (torusFourierBasis d n) (torusFourierBasis d (-n)),
    torusFourierBasis_coeFn n, torusFourierBasis_coeFn (-n)] with t h1 h2 h3 h4 h5 h6
  dsimp only [torusSine] at h1 ⊢
  rw [h1, h2, h3, Pi.smul_apply, h4, Pi.sub_apply, h5, h6, torusCharacter_neg_index]
  simp only [Complex.ofRealCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [Complex.im_eq_sub_conj]
  ring

def torusCoefficient (m : Fin d → ℤ) : TorusL2 d →L[ℝ] ℂ :=
  ((innerSL ℂ (torusFourierBasis d m)).restrictScalars ℝ).comp
    (Complex.ofRealCLM.compLpL 2 (torusHaar d))

theorem torusCoefficient_apply (m : Fin d → ℤ) (x : TorusL2 d) :
    torusCoefficient m x = torusFourierCoeff (fun t => (x t : ℂ)) m := by
  change inner ℂ (torusFourierBasis d m) (Complex.ofRealCLM.compLp x) = _
  rw [← (torusFourierBasis d).repr_apply_apply, torusFourierBasis_repr,
    torusFourierCoeff_ofReal_compLp]

theorem torusCoefficient_cosine (n m : Fin d → ℤ) :
    torusCoefficient m (torusCosine n) =
      (1/2 : ℂ) * ((if n = m then 1 else 0) + (if -n = m then 1 else 0)) := by
  classical
  change inner ℂ (torusFourierBasis d m) (Complex.ofRealCLM.compLp (torusCosine n)) = _
  rw [ofReal_torusCosine, inner_smul_right, inner_add_right]
  simp only [orthonormal_iff_ite.mp (torusFourierBasis d).orthonormal, eq_comm]

theorem torusCoefficient_sine (n m : Fin d → ℤ) :
    torusCoefficient m (torusSine n) =
      (1/(2*Complex.I) : ℂ) * ((if n = m then 1 else 0) - (if -n = m then 1 else 0)) := by
  classical
  change inner ℂ (torusFourierBasis d m) (Complex.ofRealCLM.compLp (torusSine n)) = _
  rw [ofReal_torusSine, inner_smul_right, inner_sub_right]
  simp only [orthonormal_iff_ite.mp (torusFourierBasis d).orthonormal, eq_comm]

theorem torusCoefficient_neg (n : Fin d → ℤ) (x : TorusL2 d) :
    torusCoefficient (-n) x = conj (torusCoefficient n x) := by
  simp only [torusCoefficient_apply, torusFourierCoeff]
  rw [← integral_conj]
  simp only [torusCharacter_neg_index, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]

theorem inner_torusCosine (n : Fin d → ℤ) (x : TorusL2 d) :
    ⟪torusCosine n,x⟫ = (torusCoefficient n x).re := by
  apply Complex.ofReal_injective
  rw [← inner_ofRealCLM_compLp, ofReal_torusCosine, inner_smul_left, inner_add_left]
  change conj (1/2 : ℂ) * (torusCoefficient n x + torusCoefficient (-n) x) = _
  rw [torusCoefficient_neg, Complex.re_eq_add_conj]
  simp only [map_div₀, map_one, map_ofNat]
  ring

theorem inner_torusSine (n : Fin d → ℤ) (x : TorusL2 d) :
    ⟪torusSine n,x⟫ = -(torusCoefficient n x).im := by
  apply Complex.ofReal_injective
  rw [← inner_ofRealCLM_compLp, ofReal_torusSine, inner_smul_left, inner_sub_left]
  change conj (1/(2*Complex.I) : ℂ) * (torusCoefficient n x - torusCoefficient (-n) x) = _
  rw [torusCoefficient_neg, Complex.ofReal_neg, Complex.im_eq_sub_conj]
  simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_I]
  field_simp

theorem torusCosine_norm_le_one (n : Fin d → ℤ) : ‖torusCosine n‖ ≤ 1 := by
  have h := Complex.reCLM.norm_compLp_le (torusFourierBasis d n)
  have hle : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_re_le_norm z
  calc
    ‖torusCosine n‖ ≤ ‖Complex.reCLM‖ * ‖torusFourierBasis d n‖ := h
    _ ≤ 1 := by rw [(torusFourierBasis d).orthonormal.1 n, mul_one]; exact hle

theorem torusSine_norm_le_one (n : Fin d → ℤ) : ‖torusSine n‖ ≤ 1 := by
  have h := Complex.imCLM.norm_compLp_le (torusFourierBasis d n)
  have hle : ‖Complex.imCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_im_le_norm z
  calc
    ‖torusSine n‖ ≤ ‖Complex.imCLM‖ * ‖torusFourierBasis d n‖ := h
    _ ≤ 1 := by rw [(torusFourierBasis d).orthonormal.1 n, mul_one]; exact hle

theorem torusCoefficient_rankPair (n m : Fin d → ℤ) (x : TorusL2 d) :
    torusCoefficient m ((rankOne ℝ (torusCosine n) (torusCosine n) +
      rankOne ℝ (torusSine n) (torusSine n)) x) =
      (if n = m then torusCoefficient n x / 2 else 0) +
        (if -n = m then conj (torusCoefficient n x) / 2 else 0) := by
  classical
  rw [ContinuousLinearMap.add_apply, map_add, rankOne_apply, rankOne_apply, map_smul, map_smul,
    inner_torusCosine, inner_torusSine, torusCoefficient_cosine, torusCoefficient_sine]
  simp only [Complex.real_smul]
  split_ifs <;> apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> ring

def torusMultiplier (p : (Fin d → ℤ) → ℝ) : TorusL2 d →L[ℝ] TorusL2 d :=
  (∑' n, p n • rankOne ℝ (torusCosine n) (torusCosine n)) +
    ∑' n, p n • rankOne ℝ (torusSine n) (torusSine n)


theorem hasSum_torusMultiplier {p : (Fin d → ℤ) → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) :
    HasSum (fun n => p n • (rankOne ℝ (torusCosine n) (torusCosine n) +
      rankOne ℝ (torusSine n) (torusSine n))) (torusMultiplier p) := by
  have hr := ContinuousLinearMap.summable_weighted_rankOne hp
    (ContinuousLinearMap.summable_weight_norm_sq hp hs torusCosine_norm_le_one)
  have hi := ContinuousLinearMap.summable_weighted_rankOne hp
    (ContinuousLinearMap.summable_weight_norm_sq hp hs torusSine_norm_le_one)
  simpa only [smul_add, torusMultiplier] using hr.hasSum.add hi.hasSum

theorem torusMultiplier_coefficient {p : (Fin d → ℤ) → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (heven : ∀ n, p (-n) = p n)
    (x : TorusL2 d) (m : Fin d → ℤ) :
    torusCoefficient m (torusMultiplier p x) = (p m : ℂ) * torusCoefficient m x := by
  classical
  have h := ((hasSum_torusMultiplier hp hs).mapL
    (ContinuousLinearMap.apply ℝ (TorusL2 d) x)).mapL (torusCoefficient m)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, map_smul,
    torusCoefficient_rankPair] at h
  simp only [smul_add, smul_ite, smul_zero, Complex.real_smul] at h
  have h' := (hasSum_ite_eq m ((p m : ℂ) * (torusCoefficient m x / 2))).add
    (hasSum_ite_eq (-m) ((p (-m) : ℂ) * (conj (torusCoefficient (-m) x) / 2)))
  have hf : (fun n => (if n = m then (p n : ℂ) * (torusCoefficient n x / 2) else 0) +
      (if -n = m then (p n : ℂ) * (conj (torusCoefficient n x) / 2) else 0)) =
      (fun n => (if n = m then (p m : ℂ) * (torusCoefficient m x / 2) else 0) +
      (if n = -m then (p (-m) : ℂ) * (conj (torusCoefficient (-m) x) / 2) else 0)) := by
    funext n
    simp only [neg_eq_iff_eq_neg]
    split_ifs <;> simp_all
  rw [hf] at h
  have heq := h.unique h'
  rw [heq, heven, torusCoefficient_neg, starRingEnd_self_apply]
  ring

theorem isPositiveTraceClass_torusMultiplier {p : (Fin d → ℤ) → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) : IsPositiveTraceClass (torusMultiplier p) := by
  have hr := ContinuousLinearMap.summable_weight_norm_sq hp hs torusCosine_norm_le_one
  have hi := ContinuousLinearMap.summable_weight_norm_sq hp hs torusSine_norm_le_one
  refine ⟨?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.isSelfAdjoint_tsum_weighted_rankOne hp hr).add
      (ContinuousLinearMap.isSelfAdjoint_tsum_weighted_rankOne hp hi)
  · intro x
    unfold torusMultiplier
    rw [ContinuousLinearMap.add_apply, inner_add_left]
    exact add_nonneg (ContinuousLinearMap.inner_tsum_weighted_rankOne_nonneg hp hr x)
      (ContinuousLinearMap.inner_tsum_weighted_rankOne_nonneg hp hi x)
  · obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ (TorusL2 d)
    refine ⟨w, b, ?_⟩
    simpa only [torusMultiplier, ContinuousLinearMap.add_apply, inner_add_left] using
      (ContinuousLinearMap.summable_inner_tsum_weighted_rankOne hp hr b).add
        (ContinuousLinearMap.summable_inner_tsum_weighted_rankOne hp hi b)

theorem isTraceClassCovariance_torusMultiplier {p : (Fin d → ℤ) → ℝ}
    (hp : ∀ n, 0 < p n) (hs : Summable p) (heven : ∀ n, p (-n) = p n) :
    IsTraceClassCovariance (torusMultiplier p) := by
  refine ⟨isPositiveTraceClass_torusMultiplier (fun n => (hp n).le) hs, ?_⟩
  intro x y hxy
  apply torusFourierCoeff_real_ext
  intro m
  have hc := congrArg (torusCoefficient m) hxy
  rw [torusMultiplier_coefficient (fun n => (hp n).le) hs heven,
    torusMultiplier_coefficient (fun n => (hp n).le) hs heven] at hc
  simpa only [torusCoefficient_apply] using
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hp m).ne') hc

theorem isTraceClassCovariance_besselOperator (d : ℕ) (s : ℝ) (hs : (d : ℝ)/2 < s) :
    IsTraceClassCovariance (besselOperator d s) := by
  classical
  let p (n : Fin d → ℤ) := (1 + torusFreqNormSq n)^(-s)
  have hp : ∀ n, 0 < p n := fun n => Real.rpow_pos_of_pos (by unfold torusFreqNormSq; positivity) _
  have hsum : Summable p := Real.summable_one_add_sum_int_sq_rpow d s hs
  have heven : ∀ n, p (-n) = p n := by
    intro n
    simp only [p, torusFreqNormSq, Pi.neg_apply, Int.cast_neg, neg_sq]
  have hspec (x : TorusL2 d) (n : Fin d → ℤ) :
      torusFourierCoeff (fun t => (torusMultiplier p x t : ℂ)) n =
        (p n : ℂ) * torusFourierCoeff (fun t => (x t : ℂ)) n := by
    simpa only [torusCoefficient_apply] using
      torusMultiplier_coefficient (fun n => (hp n).le) hsum heven x n
  have hex : ∃ Q : TorusL2 d →L[ℝ] TorusL2 d, ∀ x n,
      torusFourierCoeff (fun t => (Q x t : ℂ)) n =
        (p n : ℂ) * torusFourierCoeff (fun t => (x t : ℂ)) n := ⟨torusMultiplier p, hspec⟩
  have heq : besselOperator d s = torusMultiplier p := by
    unfold besselOperator
    rw [dif_pos hex]
    apply ContinuousLinearMap.ext
    intro x
    apply torusFourierCoeff_real_ext
    intro n
    rw [hex.choose_spec, hspec]
  rw [heq]
  exact isTraceClassCovariance_torusMultiplier hp hsum heven
end OperatorRidgelet
