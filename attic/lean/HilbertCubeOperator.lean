import OperatorRidgelet.HilbertCube

/-!
# A genuinely infinite-dimensional operator-learning target

Multiplying the scalar Hilbert-cube target by a nonzero output vector gives a continuous
Hilbert-valued target.  It is an exact countably-wide ReLU network and remains non-cylindrical with
respect to every finite coordinate set.
-/

noncomputable section

namespace OperatorRidgelet

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def hilbertCubeReLUOperatorTarget (ψ : H) (x : BinaryHilbertCube) : H :=
  hilbertCubeReLUTarget x • ψ

/-- The Hilbert-valued width-`N` truncation. -/
def hilbertCubeFiniteReLUOperatorNetwork
    (N : ℕ) (ψ : H) (x : BinaryHilbertCube) : H :=
  hilbertCubeFiniteReLUNetwork N x • ψ

theorem continuous_hilbertCubeReLUOperatorTarget (ψ : H) :
    Continuous (hilbertCubeReLUOperatorTarget ψ) := by
  exact continuous_hilbertCubeReLUTarget.smul continuous_const

theorem norm_hilbertCubeReLUOperatorTarget_sub_finite_le
    (N : ℕ) (ψ : H) (x : BinaryHilbertCube) :
    ‖hilbertCubeReLUOperatorTarget ψ x - hilbertCubeFiniteReLUOperatorNetwork N ψ x‖ ≤
      ((1 : ℝ) / 2) ^ N * ‖ψ‖ := by
  rw [hilbertCubeReLUOperatorTarget, hilbertCubeFiniteReLUOperatorNetwork, ← sub_smul,
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_hilbertCubeReLUTarget_sub_finite_le N x) (norm_nonneg ψ)

theorem hilbertCubeReLUOperatorTarget_not_dependsOnCoordinates
    (ψ : H) (hψ : ψ ≠ 0) (s : Finset ℕ) :
    ¬DependsOnCoordinates (hilbertCubeReLUOperatorTarget ψ) s := by
  let j := s.sup id + 1
  have hj : j ∉ s := by
    intro hjmem
    have hjle : j ≤ s.sup id := Finset.le_sup (f := id) hjmem
    omega
  intro hdep
  have heq := hdep BinaryHilbertCube.zero (BinaryHilbertCube.basis j) (by
    intro i hi
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hj hi
    simp [BinaryHilbertCube.zero, BinaryHilbertCube.basis, hij])
  have hzero : hilbertCubeReLUTarget BinaryHilbertCube.zero = 0 := by
    simp [hilbertCubeReLUTarget, BinaryHilbertCube.zero, LeanRidgelet.relu]
  rw [hilbertCubeReLUOperatorTarget, hilbertCubeReLUOperatorTarget,
    hzero, hilbertCubeReLUTarget_basis] at heq
  simp only [zero_smul] at heq
  have hcoeff : ((1 : ℝ) / 2) ^ (j + 1) ≠ 0 := by positivity
  exact (smul_ne_zero hcoeff hψ) heq.symm

end OperatorRidgelet
