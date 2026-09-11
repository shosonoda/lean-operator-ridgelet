import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Transform.Gaussian
import OperatorRidgelet.ToMathlib.PositiveEigenbasis
import OperatorRidgelet.ToMathlib.GaussianOrthonormalCoordinates
import OperatorRidgelet.ToMathlib.GaussianCoordinateLaw
import OperatorRidgelet.ToMathlib.GaussianHilbert

/-!
# The Gaussian integral of a quadratic exponential

Let `Σ` be a positive self-adjoint trace-class operator with positive square root `R = Σ^{1/2}`,
let `S` be a bounded positive self-adjoint operator and put `M = R S R`.  Along an orthonormal
eigenbasis `(u_j)` of `M` with eigenvalues `m_j ≥ 0` the vectors

`t_j = m_j^{-1/2} S R u_j`

are the coordinates of the manuscript's proof: they satisfy `R t_j = m_j^{1/2} u_j`, hence
`⟪Σ t_i, t_j⟫ = m_i δ_ij` (so their `𝒩(0,Σ)`-laws are independent `𝒩(0, m_j)`) and
`⟪Σ x, t_j⟫ = m_j^{1/2} ⟪R x, u_j⟫`, and `∑_j ⟪t_j, ξ⟫² = ⟪S ξ, ξ⟫` on the closure of the range
of `R`, which carries all the mass of `𝒩(0,Σ)`.  This is the content of this file up to
the Gaussian integral itself is `integral_exp_quadratic_eigen`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### Positive square roots -/

namespace IsPositiveSqrt

variable {Q R : H →L[ℝ] H}

theorem isSymmetric (hR : IsPositiveSqrt R Q) : (R : H →ₗ[ℝ] H).IsSymmetric :=
  hR.isSelfAdjoint.isSymmetric

theorem apply_apply (hR : IsPositiveSqrt R Q) (y : H) : R (R y) = Q y := by
  conv_rhs => rw [← hR.mul_self]
  rfl

theorem inner_left (hR : IsPositiveSqrt R Q) (y z : H) : ⟪R y, z⟫ = ⟪y, R z⟫ :=
  hR.isSymmetric y z

theorem inner_cov (hR : IsPositiveSqrt R Q) (y z : H) : ⟪Q y, z⟫ = ⟪R y, R z⟫ := by
  rw [← hR.apply_apply y]
  exact hR.inner_left (R y) z

/-- A unit eigenvector of `Q` with eigenvalue `p` is an eigenvector of the positive square root
`R` with eigenvalue `√p`. -/
theorem apply_eigenvector (hR : IsPositiveSqrt R Q) {b : H} (hb : ‖b‖ = 1) {p : ℝ}
    (hQb : Q b = p • b) : R b = Real.sqrt p • b := by
  have hRb : ⟪R b, R b⟫ = p := by
    rw [← hR.inner_cov, hQb, real_inner_smul_left, real_inner_self_eq_norm_sq, hb]
    ring
  have hp0 : 0 ≤ p := hRb ▸ real_inner_self_nonneg
  have hnorm : ‖R b‖ ^ 2 = p := by rw [← real_inner_self_eq_norm_sq]; exact hRb
  have hnn : 0 ≤ ⟪R b, b⟫ := hR.inner_nonneg b
  have hle : ⟪R b, b⟫ ≤ Real.sqrt p := by
    calc ⟪R b, b⟫ ≤ ‖R b‖ * ‖b‖ := real_inner_le_norm _ _
      _ = ‖R b‖ := by rw [hb, mul_one]
      _ = Real.sqrt p := by rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hge : Real.sqrt p ≤ ⟪R b, b⟫ := by
    rcases eq_or_lt_of_le hp0 with h0 | hpos
    · rw [← h0, Real.sqrt_zero]
      exact hnn
    · have hcs := ContinuousLinearMap.inner_map_mul_le hR.isSymmetric hR.inner_nonneg b (R b)
      have h2 : ⟪R (R b), R b⟫ = p * ⟪R b, b⟫ := by
        rw [hR.apply_apply, hQb, real_inner_smul_left, real_inner_comm b (R b)]
      rw [hRb, h2] at hcs
      have hpc : p ≤ ⟪R b, b⟫ ^ 2 := by nlinarith
      nlinarith [Real.sq_sqrt hp0, Real.sqrt_nonneg p, sq_nonneg (Real.sqrt p - ⟪R b, b⟫)]
  have heq : ⟪R b, b⟫ = Real.sqrt p := le_antisymm hle hge
  have hz : ‖R b - Real.sqrt p • b‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, heq, norm_smul, hb, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg p), hnorm]
    linarith [Real.sq_sqrt hp0]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hz
  rwa [norm_eq_zero, sub_eq_zero] at this

end IsPositiveSqrt


/-! ### The coordinate vectors of an eigenbasis of `M = R S R` -/

section Coord

set_option linter.unusedSectionVars false

variable {Cov S R : H →L[ℝ] H} {κ : Type*}

/-- The unit coordinate vector `t_j = m_j⁻¹ S R u_j` attached to the eigenvector `u_j = e j` of
`M = R S R` with eigenvalue `m_j ≠ 0`.  It satisfies `R t_j = u_j`, so that `⟪t_j, ·⟫` is a
standard normal coordinate of `𝒩(0,Σ)`. -/
def unitCoordVec (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) (j : κ) : H :=
  (m j)⁻¹ • S (R (e j))

variable {e : HilbertBasis κ ℝ H} {m : κ → ℝ}

theorem inner_map_SR (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m) (j : κ)
    (y : H) : ⟪S (R (e j)), R y⟫ = m j * ⟪e j, y⟫ := by
  rw [← hR.inner_left]
  have : R (S (R (e j))) = (R * S * R) (e j) := rfl
  rw [this, hM j, real_inner_smul_left]

theorem eigenvalue_nonneg (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) (j : κ) : 0 ≤ m j := by
  have h := inner_map_SR hR hM j (e j)
  rw [real_inner_self_eq_norm_sq, e.orthonormal.1 j, one_pow, mul_one] at h
  rw [← h]
  exact hS0 _

theorem map_unitCoordVec (hM : HasEigenbasis (R * S * R) e m) {j : κ} (hj : m j ≠ 0) :
    R (unitCoordVec S R e m j) = e j := by
  have h1 : R (S (R (e j))) = (R * S * R) (e j) := rfl
  rw [unitCoordVec, map_smul, h1, hM j, smul_smul, inv_mul_cancel₀ hj, one_smul]

theorem map_SR_eq_smul_unit (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) {j : κ}
    (hj : m j ≠ 0) : S (R (e j)) = m j • unitCoordVec S R e m j := by
  rw [unitCoordVec, smul_smul, mul_inv_cancel₀ hj, one_smul]

theorem inner_unitCoordVec_map (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m)
    {j : κ} (hj : m j ≠ 0) (y : H) : ⟪unitCoordVec S R e m j, R y⟫ = ⟪e j, y⟫ := by
  rw [← hR.inner_left, map_unitCoordVec hM hj]

theorem inner_cov_unitCoordVec_self (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {j : κ} (hj : m j ≠ 0) :
    ⟪Cov (unitCoordVec S R e m j), unitCoordVec S R e m j⟫ = 1 := by
  rw [hR.inner_cov, map_unitCoordVec hM hj, real_inner_self_eq_norm_sq, e.orthonormal.1 j, one_pow]

theorem inner_cov_unitCoordVec_ne (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {i j : κ} (hi : m i ≠ 0) (hj : m j ≠ 0) (hij : i ≠ j) :
    ⟪Cov (unitCoordVec S R e m i), unitCoordVec S R e m j⟫ = 0 := by
  rw [hR.inner_cov, map_unitCoordVec hM hi, map_unitCoordVec hM hj, e.orthonormal.2 hij]

theorem inner_cov_left_unitCoordVec (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {j : κ} (hj : m j ≠ 0) (x : H) :
    ⟪Cov x, unitCoordVec S R e m j⟫ = ⟪R x, e j⟫ := by
  rw [hR.inner_cov, map_unitCoordVec hM hj]

end Coord

/-! ### The truncated quadratic form -/

section Truncation

set_option linter.unusedSectionVars false

variable {Cov S R : H →L[ℝ] H} {κ : Type*} {e : HilbertBasis κ ℝ H} {m : κ → ℝ}

theorem unitCoordVec_eq_zero {j : κ} (hj : m j = 0) : unitCoordVec S R e m j = 0 := by
  rw [unitCoordVec, hj, inv_zero, zero_smul]

/-- The `F`-section `∑_{j ∈ F} ⟪t_j, ξ⟫ R u_j` of the expansion of `ξ`. -/
def coordSum (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) (F : Finset κ) (ξ : H) : H :=
  ∑ j ∈ F, ⟪unitCoordVec S R e m j, ξ⟫ • R (e j)

/-- The truncated quadratic form `∑_{j ∈ F} m_j ⟪t_j, ξ⟫²`. -/
def truncQuad (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) (F : Finset κ) (ξ : H) : ℝ :=
  ∑ j ∈ F, m j * ⟪unitCoordVec S R e m j, ξ⟫ ^ 2

theorem inner_map_SR_right (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) (j : κ)
    (ξ : H) :
    ⟪unitCoordVec S R e m j, ξ⟫ * ⟪S (R (e j)), ξ⟫ =
      m j * ⟪unitCoordVec S R e m j, ξ⟫ ^ 2 := by
  rcases eq_or_ne (m j) 0 with hj | hj
  · rw [unitCoordVec_eq_zero hj, inner_zero_left, hj]
    ring
  · rw [map_SR_eq_smul_unit S R e m hj, real_inner_smul_left]
    ring

theorem inner_map_coordSum_self (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m)
    (F : Finset κ) (ξ : H) :
    ⟪S (coordSum S R e m F ξ), coordSum S R e m F ξ⟫ = truncQuad S R e m F ξ := by
  simp only [coordSum, truncQuad, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single j]
  · rw [inner_map_SR hR hM j (e j), real_inner_self_eq_norm_sq, e.orthonormal.1 j, one_pow,
      mul_one]
    ring
  · intro i _ hij
    rw [inner_map_SR hR hM i (e j), e.orthonormal.2 hij]
    ring
  · intro h
    exact absurd hj h

theorem inner_map_coordSum_right (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ)
    (F : Finset κ) (ξ : H) :
    ⟪S (coordSum S R e m F ξ), ξ⟫ = truncQuad S R e m F ξ := by
  simp only [coordSum, truncQuad, map_sum, map_smul, sum_inner, real_inner_smul_left]
  exact Finset.sum_congr rfl fun j _ => inner_map_SR_right S R e m j ξ

theorem inner_map_sub_coordSum (hS : IsSelfAdjoint S) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) (F : Finset κ) (ξ : H) :
    ⟪S (ξ - coordSum S R e m F ξ), ξ - coordSum S R e m F ξ⟫ =
      ⟪S ξ, ξ⟫ - truncQuad S R e m F ξ := by
  have hsym : ⟪S ξ, coordSum S R e m F ξ⟫ = ⟪S (coordSum S R e m F ξ), ξ⟫ :=
    (hS.isSymmetric _ _).trans (real_inner_comm _ _)
  rw [map_sub]
  simp only [inner_sub_left, inner_sub_right]
  rw [hsym, inner_map_coordSum_self hR hM, inner_map_coordSum_right S R e m]
  ring

theorem truncQuad_le (hS : IsSelfAdjoint S) (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) (F : Finset κ) (ξ : H) :
    truncQuad S R e m F ξ ≤ ⟪S ξ, ξ⟫ := by
  have h := hS0 (ξ - coordSum S R e m F ξ)
  rw [inner_map_sub_coordSum hS hR hM] at h
  linarith

end Truncation

/-! ### Convergence of the truncated quadratic form on the closure of the range of `R` -/

section Convergence

set_option linter.unusedSectionVars false

variable {Cov S R : H →L[ℝ] H} {κ : Type*} {e : HilbertBasis κ ℝ H} {m : κ → ℝ}

theorem inner_map_add_le_two (hS : IsSelfAdjoint S) (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫) (p q : H) :
    ⟪S (p + q), p + q⟫ ≤ 2 * ⟪S p, p⟫ + 2 * ⟪S q, q⟫ := by
  have h := hS0 (p - q)
  have hc := ContinuousLinearMap.inner_map_comm hS.isSymmetric p q
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right] at h ⊢
  rw [hc] at h
  linarith

theorem coordSum_add (F : Finset κ) (a b : H) :
    coordSum S R e m F (a + b) = coordSum S R e m F a + coordSum S R e m F b := by
  simp only [coordSum, inner_add_right, add_smul]
  exact Finset.sum_add_distrib

theorem inner_map_map_eq (hR : IsPositiveSqrt R Cov) (y : H) :
    ⟪(R * S * R) y, y⟫ = ⟪S (R y), R y⟫ :=
  hR.isSymmetric (S (R y)) y

theorem truncQuad_map (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m)
    (F : Finset κ) (y : H) :
    truncQuad S R e m F (R y) = ∑ j ∈ F, m j * ⟪e j, y⟫ ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases eq_or_ne (m j) 0 with hj | hj
  · rw [hj]; ring
  · rw [inner_unitCoordVec_map hR hM hj]

theorem tendsto_truncQuad_map (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m)
    (y : H) :
    Filter.Tendsto (fun F : Finset κ => truncQuad S R e m F (R y)) Filter.atTop
      (nhds ⟪S (R y), R y⟫) := by
  have h := ContinuousLinearMap.hasSum_inner_map_self_of_eigen e m hM y
  rw [inner_map_map_eq hR] at h
  have h2 : Filter.Tendsto (fun F : Finset κ => ∑ j ∈ F, m j * ⟪e j, y⟫ ^ 2) Filter.atTop
      (nhds ⟪S (R y), R y⟫) := h
  rw [show (fun F : Finset κ => truncQuad S R e m F (R y)) =
      fun F : Finset κ => ∑ j ∈ F, m j * ⟪e j, y⟫ ^ 2 from
    funext fun F => truncQuad_map hR hM F y]
  exact h2

/-- On the closure of the range of `R` the truncated quadratic forms converge to `⟪S ξ, ξ⟫`. -/
theorem tendsto_truncQuad (hS : IsSelfAdjoint S) (hS0 : ∀ x, 0 ≤ ⟪S x, x⟫)
    (hR : IsPositiveSqrt R Cov) (hM : HasEigenbasis (R * S * R) e m) {ξ : H}
    (hξ : ξ ∈ closure (Set.range (R : H → H))) :
    Filter.Tendsto (fun F : Finset κ => truncQuad S R e m F ξ) Filter.atTop
      (nhds ⟪S ξ, ξ⟫) := by
  have key : Filter.Tendsto (fun F : Finset κ => ⟪S ξ, ξ⟫ - truncQuad S R e m F ξ)
      Filter.atTop (nhds 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have hpos8 : (0 : ℝ) < ε / (8 * (‖S‖ + 1)) := by positivity
    obtain ⟨u, ⟨y, rfl⟩, hu⟩ := Metric.mem_closure_iff.1 hξ _ (Real.sqrt_pos.2 hpos8)
    set w : H := ξ - R y with hw
    have hwn : ⟪S w, w⟫ ≤ ε / 8 := by
      have h1 : ⟪S w, w⟫ ≤ ‖S‖ * ‖w‖ ^ 2 := by
        calc ⟪S w, w⟫ ≤ ‖S w‖ * ‖w‖ := real_inner_le_norm _ _
          _ ≤ ‖S‖ * ‖w‖ * ‖w‖ := by
              gcongr
              exact S.le_opNorm _
          _ = ‖S‖ * ‖w‖ ^ 2 := by ring
      have hd : ‖w‖ < Real.sqrt (ε / (8 * (‖S‖ + 1))) := by
        rw [hw, ← dist_eq_norm]; exact hu
      have h2 : ‖w‖ ^ 2 ≤ ε / (8 * (‖S‖ + 1)) := by
        nlinarith [norm_nonneg w, Real.sq_sqrt hpos8.le,
          Real.sqrt_nonneg (ε / (8 * (‖S‖ + 1)))]
      have h3 : ‖S‖ * (ε / (8 * (‖S‖ + 1))) ≤ ε / 8 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (‖S‖ + 1))]
        nlinarith [norm_nonneg S, hε.le]
      calc ⟪S w, w⟫ ≤ ‖S‖ * ‖w‖ ^ 2 := h1
        _ ≤ ‖S‖ * (ε / (8 * (‖S‖ + 1))) := by gcongr
        _ ≤ ε / 8 := h3
    have hlim := tendsto_truncQuad_map hR hM (S := S) (e := e) (m := m) y
    have hz : Filter.Tendsto (fun F : Finset κ => ⟪S (R y), R y⟫ - truncQuad S R e m F (R y))
        Filter.atTop (nhds 0) := by
      have hc : Filter.Tendsto (fun _ : Finset κ => ⟪S (R y), R y⟫) Filter.atTop
          (nhds ⟪S (R y), R y⟫) := tendsto_const_nhds
      simpa using hc.sub hlim
    have hev : ∀ᶠ F : Finset κ in Filter.atTop,
        ⟪S (R y), R y⟫ - truncQuad S R e m F (R y) < ε / 4 := by
      filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hz (ε / 4) (by positivity)] with F hF
      calc ⟪S (R y), R y⟫ - truncQuad S R e m F (R y)
          ≤ ‖⟪S (R y), R y⟫ - truncQuad S R e m F (R y)‖ := le_abs_self _
        _ < ε / 4 := hF
    filter_upwards [hev] with F hF
    have hsplit : ξ = R y + w := by rw [hw]; abel
    have hdec : ⟪S ξ, ξ⟫ - truncQuad S R e m F ξ =
        ⟪S (ξ - coordSum S R e m F ξ), ξ - coordSum S R e m F ξ⟫ :=
      (inner_map_sub_coordSum hS hR hM F ξ).symm
    have hlin : ξ - coordSum S R e m F ξ =
        (R y - coordSum S R e m F (R y)) + (w - coordSum S R e m F w) := by
      rw [show ξ - coordSum S R e m F ξ = ξ - coordSum S R e m F (R y + w) by rw [← hsplit],
        coordSum_add]
      rw [hsplit]
      abel
    have hb := inner_map_add_le_two hS hS0 (R y - coordSum S R e m F (R y))
      (w - coordSum S R e m F w)
    rw [inner_map_sub_coordSum hS hR hM F (R y), inner_map_sub_coordSum hS hR hM F w] at hb
    have h0 : 0 ≤ truncQuad S R e m F w := by
      rw [← inner_map_coordSum_self hR hM F w]; exact hS0 _
    have hnonneg : 0 ≤ ⟪S ξ, ξ⟫ - truncQuad S R e m F ξ := by
      have := truncQuad_le hS hS0 hR hM F ξ; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hdec, hlin]
    calc ⟪S ((R y - coordSum S R e m F (R y)) + (w - coordSum S R e m F w)),
            (R y - coordSum S R e m F (R y)) + (w - coordSum S R e m F w)⟫
        ≤ 2 * (⟪S (R y), R y⟫ - truncQuad S R e m F (R y)) +
            2 * (⟪S w, w⟫ - truncQuad S R e m F w) := hb
      _ < ε := by linarith
  have hfin : Filter.Tendsto
      (fun F : Finset κ => ⟪S ξ, ξ⟫ - (⟪S ξ, ξ⟫ - truncQuad S R e m F ξ)) Filter.atTop
      (nhds (⟪S ξ, ξ⟫ - 0)) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : Finset κ => ⟪S ξ, ξ⟫) Filter.atTop
      (nhds ⟪S ξ, ξ⟫)).sub key
  simpa using hfin

end Convergence

/-! ### The support of a centred Gaussian measure -/

section Support

variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- A positive self-adjoint trace-class operator has a countable orthonormal eigenbasis with
nonnegative summable eigenvalues (injectivity is *not* assumed, so `0` may be an eigenvalue). -/
theorem IsPositiveTraceClass.exists_eigenbasis' {Cov : H →L[ℝ] H}
    (hCov : IsPositiveTraceClass Cov) :
    ∃ (κ : Type) (_ : Countable κ) (b : HilbertBasis κ ℝ H) (p : κ → ℝ),
      (∀ k, 0 ≤ p k) ∧ Summable p ∧ ∀ k, Cov (b k) = p k • b k := by
  obtain ⟨ι, b0, hb0⟩ := hCov.hasSummableTrace
  have hcomp := ContinuousLinearMap.isCompactOperator_of_summable_inner
    hCov.isSelfAdjoint.isSymmetric hCov.inner_nonneg b0 hb0
  obtain ⟨κ, hκ, b, hb⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_eigenvector_of_isCompactOperator
      hCov.isSelfAdjoint hcomp
  refine ⟨κ, hκ, b, fun k => ⟪Cov (b k), b k⟫, fun k => hCov.inner_nonneg _, ?_, hb⟩
  have hkey := ContinuousLinearMap.tsum_ofReal_inner_map_eq_of_eigen b0 b
    (fun k => ⟪Cov (b k), b k⟫) (fun k => hCov.inner_nonneg _) hb
  have hlhs : ∑' i, ENNReal.ofReal ⟪Cov (b0 i), b0 i⟫ ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hCov.inner_nonneg _) hb0]
    exact ENNReal.ofReal_ne_top
  rw [hkey] at hlhs
  have hnn : Summable fun k => (⟪Cov (b k), b k⟫).toNNReal :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [ENNReal.ofReal] using hlhs)
  refine (NNReal.summable_coe.2 hnn).congr fun k => ?_
  exact Real.coe_toNNReal _ (hCov.inner_nonneg _)

/-- A centred Gaussian measure with covariance `Σ = R²` is carried by the closure of the range
of `R`: its Karhunen–Loève series has all its partial sums there. -/
theorem IsCenteredGaussian.ae_mem_closure_range {Cov R : H →L[ℝ] H}
    (hCov : IsPositiveTraceClass Cov) (hR : IsPositiveSqrt R Cov) {μ : Measure H}
    (hμ : IsCenteredGaussian Cov μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ closure (Set.range (R : H → H)) := by
  obtain ⟨κ, hκ, b, p, hp, hs, hPe⟩ := hCov.exists_eigenbasis'
  have hμ' : μ = gaussianSeries b p :=
    hμ.unique (isCenteredGaussian_gaussianSeries b p hp hs hPe)
  have hbase : ∀ᵐ z ∂stdGaussianPi κ,
      gaussianSeriesMap b p z ∈ closure (Set.range (R : H → H)) := by
    filter_upwards [ae_hasSum_gaussianSeriesMap b p hp hs] with z hz
    refine mem_closure_of_tendsto hz (Filter.Eventually.of_forall fun F => ?_)
    refine ⟨∑ i ∈ F, z i • b i, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hR.apply_eigenvector (b.orthonormal.1 i) (hPe i), smul_smul, mul_comm]
  rw [hμ', gaussianSeries]
  exact (MeasureTheory.ae_map_iff (measurable_gaussianSeriesMap b p).aemeasurable
    (isClosed_closure (s := Set.range (R : H → H))).measurableSet).2 hbase

end Support

/-! ### The residual coordinate -/

section Residual

set_option linter.unusedSectionVars false

variable {Cov S R : H →L[ℝ] H} {κ : Type*} {e : HilbertBasis κ ℝ H} {m : κ → ℝ}

/-- The residual coordinate `x - ∑_{j ∈ G} ⟪R x, u_j⟫ t_j`; it is `Cov`-orthogonal to every
`t_j` with `j ∈ G`. -/
def residCoord (S R : H →L[ℝ] H) (e : HilbertBasis κ ℝ H) (m : κ → ℝ) (G : Finset κ) (x : H) :
    H :=
  x - ∑ j ∈ G, ⟪R x, e j⟫ • unitCoordVec S R e m j

theorem inner_residCoord (G : Finset κ) (x ξ : H) :
    ⟪residCoord S R e m G x, ξ⟫ +
        ∑ j ∈ G, ⟪R x, e j⟫ * ⟪unitCoordVec S R e m j, ξ⟫ = ⟪x, ξ⟫ := by
  simp only [residCoord, inner_sub_left, sum_inner, real_inner_smul_left]
  ring

theorem inner_cov_residCoord_unitCoordVec (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {G : Finset κ} (hG : ∀ j ∈ G, m j ≠ 0) (x : H)
    {j : κ} (hjG : j ∈ G) : ⟪Cov (residCoord S R e m G x), unitCoordVec S R e m j⟫ = 0 := by
  simp only [residCoord, map_sub, inner_sub_left, map_sum, map_smul, sum_inner,
    real_inner_smul_left]
  rw [inner_cov_left_unitCoordVec hR hM (hG j hjG) x, Finset.sum_eq_single j]
  · rw [inner_cov_unitCoordVec_self hR hM (hG j hjG), mul_one, sub_self]
  · intro i hi hij
    rw [inner_cov_unitCoordVec_ne hR hM (hG i hi) (hG j hjG) hij, mul_zero]
  · intro h
    exact absurd hjG h

theorem inner_right_residCoord {G : Finset κ} (x : H) {w : H}
    (hw : ∀ j ∈ G, ⟪w, unitCoordVec S R e m j⟫ = 0) :
    ⟪w, residCoord S R e m G x⟫ = ⟪w, x⟫ := by
  have hz : ∀ j ∈ G, ⟪w, (⟪R x, e j⟫ : ℝ) • unitCoordVec S R e m j⟫ = 0 := fun j hj => by
    rw [real_inner_smul_right, hw j hj, mul_zero]
  rw [residCoord, inner_sub_right, inner_sum, Finset.sum_eq_zero hz, sub_zero]

theorem inner_cov_residCoord_self (hCov : IsSelfAdjoint Cov) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {G : Finset κ} (hG : ∀ j ∈ G, m j ≠ 0) (x : H) :
    ⟪Cov (residCoord S R e m G x), residCoord S R e m G x⟫ =
      ⟪Cov x, x⟫ - ∑ j ∈ G, ⟪R x, e j⟫ ^ 2 := by
  rw [inner_right_residCoord x
    (fun j hj => inner_cov_residCoord_unitCoordVec hR hM hG x hj),
    ContinuousLinearMap.inner_map_comm hCov.isSymmetric _ x, residCoord, inner_sub_right,
    inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [real_inner_smul_right, inner_cov_left_unitCoordVec hR hM (hG j hj) x, sq]

end Residual

/-! ### The Gaussian integral over a finite set of coordinates -/

section FiniteIntegral

set_option linter.unusedSectionVars false

variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The Gaussian integral of `e^{i⟪x,ξ⟫ - q_G(ξ)/2}` for the truncated quadratic form `q_G`
along a finite set `G` of eigenvectors with nonzero eigenvalues. -/
theorem integral_exp_truncQuad {Cov S R : H →L[ℝ] H} {κ : Type} {e : HilbertBasis κ ℝ H}
    {m : κ → ℝ} (hCovsa : IsSelfAdjoint Cov) (hm0 : ∀ k, 0 ≤ m k) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) {μ : Measure H} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian Cov μ) (x : H) (G : Finset κ) (hG : ∀ j ∈ G, m j ≠ 0) :
    ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I - ((truncQuad S R e m G ξ / 2 : ℝ) : ℂ)) ∂μ =
      ((∏ j ∈ G, (Real.sqrt (1 + m j))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-(((⟪Cov x, x⟫ -
          ∑ j ∈ G, (m j / (1 + m j)) * ⟪R x, e j⟫ ^ 2) / 2 : ℝ) : ℂ)) := by
  classical
  set w : H := residCoord S R e m G x with hw
  set s0 : ℝ := ⟪Cov x, x⟫ - ∑ j ∈ G, ⟪R x, e j⟫ ^ 2 with hs0
  have hws : ⟪Cov w, w⟫ = s0 := inner_cov_residCoord_self hCovsa hR hM hG x
  have hs0nonneg : 0 ≤ s0 := by
    rw [← hws, hR.inner_cov]
    exact real_inner_self_nonneg
  set v : Option {j : κ // j ∈ G} → H := fun i => i.elim w fun j => unitCoordVec S R e m j.1
    with hvdef
  set sg : Option {j : κ // j ∈ G} → ℝ := fun i => i.elim s0 fun _ => 1 with hsgdef
  set g : Option {j : κ // j ∈ G} → ℝ → ℂ := fun i =>
    i.elim (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      fun j t => Complex.exp (((⟪R x, e j.1⟫ * t : ℝ) : ℂ) * Complex.I -
        ((m j.1 * t ^ 2 / 2 : ℝ) : ℂ)) with hgdef
  have hsg : ∀ i, 0 ≤ sg i := by
    rintro (_ | j)
    · exact hs0nonneg
    · exact zero_le_one
  have hvv : ∀ i j, ⟪Cov (v i), v j⟫ = if i = j then sg i else 0 := by
    rintro (_ | i) (_ | j)
    · rw [if_pos rfl]
      exact hws
    · rw [if_neg (by simp)]
      exact inner_cov_residCoord_unitCoordVec hR hM hG x j.2
    · rw [if_neg (by simp)]
      show ⟪Cov (unitCoordVec S R e m i.1), w⟫ = 0
      rw [ContinuousLinearMap.inner_map_comm hCovsa.isSymmetric]
      exact inner_cov_residCoord_unitCoordVec hR hM hG x i.2
    · by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        exact inner_cov_unitCoordVec_self hR hM (hG i.1 i.2)
      · rw [if_neg (by simpa using hij)]
        exact inner_cov_unitCoordVec_ne hR hM (hG i.1 i.2) (hG j.1 j.2)
          fun h => hij (Subtype.ext h)
  have hg : ∀ i, Continuous (g i) := by
    rintro (_ | j)
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact Complex.continuous_exp.comp (by fun_prop)
  have hprod : ∀ ξ : H, ∏ i, g i ⟪v i, ξ⟫ =
      Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I - ((truncQuad S R e m G ξ / 2 : ℝ) : ℂ)) := by
    intro ξ
    have h1 : (∏ j : {j : κ // j ∈ G}, g (some j) ⟪v (some j), ξ⟫) =
        ∏ j ∈ G, Complex.exp (((⟪R x, e j⟫ * ⟪unitCoordVec S R e m j, ξ⟫ : ℝ) : ℂ) *
          Complex.I - ((m j * ⟪unitCoordVec S R e m j, ξ⟫ ^ 2 / 2 : ℝ) : ℂ)) :=
      Finset.prod_coe_sort G fun j : κ =>
        Complex.exp (((⟪R x, e j⟫ * ⟪unitCoordVec S R e m j, ξ⟫ : ℝ) : ℂ) * Complex.I -
          ((m j * ⟪unitCoordVec S R e m j, ξ⟫ ^ 2 / 2 : ℝ) : ℂ))
    have hA := inner_residCoord (S := S) (R := R) (e := e) (m := m) G x ξ
    have hB : truncQuad S R e m G ξ = ∑ j ∈ G, m j * ⟪unitCoordVec S R e m j, ξ⟫ ^ 2 := rfl
    have hgn : g none ⟪v none, ξ⟫ = Complex.exp ((⟪w, ξ⟫ : ℝ) * Complex.I) := rfl
    rw [Fintype.prod_option, h1, ← Complex.exp_sum, hgn, ← Complex.exp_add]
    rw [hB, ← hA, hw, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum,
      ← Complex.ofReal_sum, ← Finset.sum_div]
    push_cast
    ring
  have hnone : ∫ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) ∂gaussianReal 0 s0.toNNReal =
      Complex.exp (-((s0 / 2 : ℝ) : ℂ)) := by
    have h1 : charFun (gaussianReal 0 s0.toNNReal) (1 : ℝ) =
        ∫ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) ∂gaussianReal 0 s0.toNNReal := by
      rw [charFun_apply_real]
      simp
    rw [← h1, charFun_gaussianReal, Real.coe_toNNReal _ hs0nonneg]
    push_cast
    ring_nf
  have hsome : ∀ j : κ, m j ≠ 0 →
      (∫ t : ℝ, Complex.exp (((⟪R x, e j⟫ * t : ℝ) : ℂ) * Complex.I -
          ((m j * t ^ 2 / 2 : ℝ) : ℂ)) ∂gaussianReal 0 (1 : ℝ).toNNReal) =
        (((Real.sqrt (1 + m j))⁻¹ : ℝ) : ℂ) *
          Complex.exp (-((⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) : ℝ) : ℂ)) := by
    intro j _
    rw [show (1 : ℝ).toNNReal = 1 from by simp]
    exact ProbabilityTheory.integral_exp_mul_I_sub_sq_gaussianReal_one (hm0 j) _
  calc ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I -
          ((truncQuad S R e m G ξ / 2 : ℝ) : ℂ)) ∂μ
      = ∫ ξ, ∏ i, g i ⟪v i, ξ⟫ ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hprod ξ).symm)
    _ = ∏ i, ∫ t, g i t ∂gaussianReal 0 (sg i).toNNReal :=
        MeasureTheory.integral_prod_comp_inner hμ.charFun_eq v sg hsg hvv g hg
    _ = (∫ t, g none t ∂gaussianReal 0 (sg none).toNNReal) *
          ∏ j : {j : κ // j ∈ G}, ∫ t, g (some j) t ∂gaussianReal 0 (sg (some j)).toNNReal :=
        Fintype.prod_option _
    _ = Complex.exp (-((s0 / 2 : ℝ) : ℂ)) *
          ∏ j ∈ G, ((((Real.sqrt (1 + m j))⁻¹ : ℝ) : ℂ) *
            Complex.exp (-((⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) : ℝ) : ℂ))) := by
        rw [show (∫ t, g none t ∂gaussianReal 0 (sg none).toNNReal) =
          ∫ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) ∂gaussianReal 0 s0.toNNReal from rfl, hnone]
        congr 1
        rw [← Finset.prod_coe_sort G fun j => ((((Real.sqrt (1 + m j))⁻¹ : ℝ) : ℂ) *
          Complex.exp (-((⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) : ℝ) : ℂ)))]
        exact Finset.prod_congr rfl fun j _ => hsome j.1 (hG j.1 j.2)
    _ = ((∏ j ∈ G, (Real.sqrt (1 + m j))⁻¹ : ℝ) : ℂ) *
          Complex.exp (-(((⟪Cov x, x⟫ -
            ∑ j ∈ G, (m j / (1 + m j)) * ⟪R x, e j⟫ ^ 2) / 2 : ℝ) : ℂ)) := by
        rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod]
        rw [mul_comm (Complex.exp (-((s0 / 2 : ℝ) : ℂ))), mul_assoc, ← Complex.exp_add]
        congr 1
        have hsum : ∑ j ∈ G, (-((⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) : ℝ) : ℂ)) =
            -((∑ j ∈ G, ⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum, Finset.sum_neg_distrib]
        have hreal : ∑ j ∈ G, ⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) + s0 / 2 =
            (⟪Cov x, x⟫ - ∑ j ∈ G, (m j / (1 + m j)) * ⟪R x, e j⟫ ^ 2) / 2 := by
          have hterm : ∀ j ∈ G, ⟪R x, e j⟫ ^ 2 / (2 * (1 + m j)) =
              (⟪R x, e j⟫ ^ 2 - (m j / (1 + m j)) * ⟪R x, e j⟫ ^ 2) / 2 := by
            intro j _
            have h1 : (0 : ℝ) < 1 + m j := by linarith [hm0 j]
            field_simp
            ring
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib, hs0]
          ring
        rw [hsum]
        congr 1
        rw [← hreal]
        push_cast
        ring

end FiniteIntegral

/-! ### The resolvent quadratic form -/

section Resolvent

set_option linter.unusedSectionVars false

variable {Cov S R : H →L[ℝ] H} {κ : Type*} {e : HilbertBasis κ ℝ H} {m : κ → ℝ}

/-- `I + M` is invertible for a positive `M`. -/
theorem isUnit_one_add_of_nonneg {M : H →L[ℝ] H} (hM0 : ∀ y, 0 ≤ ⟪M y, y⟫) :
    IsUnit (1 + M) := by
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (1 + M) (c := 1) one_pos
    fun y => ?_
  have hy : ⟪(1 + M) y, y⟫ = ‖y‖ ^ 2 + ⟪M y, y⟫ := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, inner_add_left,
      real_inner_self_eq_norm_sq]
  rw [hy]
  have h0 := hM0 y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa using h0

theorem inverse_one_add_smul {M : H →L[ℝ] H} (hM : IsUnit (1 + M)) {u : H} {c : ℝ}
    (hc : M u = c • u) (hc1 : (1 : ℝ) + c ≠ 0) :
    Ring.inverse (1 + M) u = (1 + c)⁻¹ • u := by
  have h1 : (1 + M) u = (1 + c) • u := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, hc, add_smul, one_smul]
  have h2 : Ring.inverse (1 + M) ((1 + M) u) = u := by
    have h3 := Ring.inverse_mul_cancel (1 + M) hM
    calc Ring.inverse (1 + M) ((1 + M) u) = (Ring.inverse (1 + M) * (1 + M)) u := rfl
      _ = (1 : H →L[ℝ] H) u := by rw [h3]
      _ = u := rfl
  rw [h1, map_smul] at h2
  have h4 := congrArg (fun z : H => (1 + c)⁻¹ • z) h2
  simpa [smul_smul, inv_mul_cancel₀ hc1] using h4

/-- The resolvent quadratic form `⟪R (I+M)⁻¹ R x, x⟫` expands as `∑_j (1+m_j)⁻¹ ⟪u_j, R x⟫²`. -/
theorem hasSum_resolventForm (hS0 : ∀ y, 0 ≤ ⟪S y, y⟫) (hR : IsPositiveSqrt R Cov)
    (hM : HasEigenbasis (R * S * R) e m) (hm0 : ∀ k, 0 ≤ m k) (x : H) :
    HasSum (fun j => (1 + m j)⁻¹ * ⟪e j, R x⟫ ^ 2) (resolventForm R (R * S * R) x) := by
  have hMpos : ∀ y, 0 ≤ ⟪(R * S * R) y, y⟫ := by
    intro y
    rw [inner_map_map_eq hR]
    exact hS0 _
  have hunit := isUnit_one_add_of_nonneg hMpos
  have hNe : ∀ k, Ring.inverse (1 + R * S * R) (e k) = (1 + m k)⁻¹ • e k := fun k =>
    inverse_one_add_smul hunit (hM k) (by linarith [hm0 k])
  have hform : resolventForm R (R * S * R) x =
      ⟪Ring.inverse (1 + R * S * R) (R x), R x⟫ := by
    rw [resolventForm]
    exact hR.isSymmetric _ x
  rw [hform]
  exact ContinuousLinearMap.hasSum_inner_map_self_of_eigen e (fun k => (1 + m k)⁻¹) hNe (R x)

/-- Parseval for the coordinates `x_j = ⟪R x, u_j⟫`: `∑_j x_j² = ⟪Σ x, x⟫`. -/
theorem hasSum_inner_cov_self (hR : IsPositiveSqrt R Cov) (e : HilbertBasis κ ℝ H) (x : H) :
    HasSum (fun j => ⟪e j, R x⟫ ^ 2) ⟪Cov x, x⟫ := by
  have h := e.hasSum_inner_sq (R x)
  rwa [← real_inner_self_eq_norm_sq, ← hR.inner_cov] at h

end Resolvent

end OperatorRidgelet
