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

end OperatorRidgelet
