import OperatorRidgelet.Examples.Defs
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

end OperatorRidgelet
