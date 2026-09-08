import LeanRidgelet.Activation.ReLU
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A compact, genuinely infinite-dimensional exact ReLU example

The binary Hilbert cube is a countable product of compact intervals.  The geometric-coordinate
functional below is an exact countably-wide ReLU network and does not depend on any finite set of
coordinates.  This provides a small formal test case before formalizing the Gaussian and PDE
measure representations from the manuscript.
-/

open scoped BigOperators Topology

namespace OperatorRidgelet

open LeanRidgelet

/-- The compact cube `[0,1]^ℕ`. -/
abbrev BinaryHilbertCube := ∀ _ : ℕ, Set.Icc (0 : ℝ) 1

theorem isCompact_univ_binaryHilbertCube :
    IsCompact (Set.univ : Set BinaryHilbertCube) := by
  exact isCompact_univ

/-- The origin of the binary Hilbert cube. -/
def BinaryHilbertCube.zero : BinaryHilbertCube :=
  fun _ ↦ ⟨0, by simp⟩

/-- The `j`-th coordinate vertex of the binary Hilbert cube. -/
def BinaryHilbertCube.basis (j : ℕ) : BinaryHilbertCube :=
  fun n ↦ ⟨if n = j then 1 else 0, by split_ifs <;> simp⟩

/-- Exact countably-wide ReLU network on the Hilbert cube. -/
noncomputable def hilbertCubeReLUTarget (x : BinaryHilbertCube) : ℝ :=
  ∑' n : ℕ, ((1 : ℝ) / 2) ^ (n + 1) * relu (x n)

/-- The first `N` neurons of the exact Hilbert-cube ReLU target. -/
noncomputable def hilbertCubeFiniteReLUNetwork (N : ℕ) (x : BinaryHilbertCube) : ℝ :=
  ∑ n ∈ Finset.range N, ((1 : ℝ) / 2) ^ (n + 1) * relu (x n)

private theorem summable_hilbertCubeReLUTerm (x : BinaryHilbertCube) :
    Summable (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + 1) * relu (x n)) := by
  have hsum : Summable (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
        ((1 : ℝ) / 2)
  apply hsum.of_norm_bounded
  intro n
  have hx0 : 0 ≤ (x n : ℝ) := (x n).property.1
  have hx1 : (x n : ℝ) ≤ 1 := (x n).property.2
  rw [relu, max_eq_left hx0, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) hx0)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ ((1 : ℝ) / 2) ^ (n + 1))

theorem continuous_hilbertCubeReLUTarget : Continuous hilbertCubeReLUTarget := by
  have hsum : Summable (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
        ((1 : ℝ) / 2)
  apply continuous_tsum (fun n ↦ by
    apply Continuous.mul continuous_const
    unfold relu
    fun_prop) hsum
  intro n x
  have hx0 : 0 ≤ (x n : ℝ) := (x n).property.1
  have hx1 : (x n : ℝ) ≤ 1 := (x n).property.2
  rw [relu, max_eq_left hx0, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) hx0)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ ((1 : ℝ) / 2) ^ (n + 1))

theorem abs_hilbertCubeReLUTarget_sub_finite_le
    (N : ℕ) (x : BinaryHilbertCube) :
    |hilbertCubeReLUTarget x - hilbertCubeFiniteReLUNetwork N x| ≤
      ((1 : ℝ) / 2) ^ N := by
  let f : ℕ → ℝ := fun n ↦ ((1 : ℝ) / 2) ^ (n + 1) * relu (x n)
  have hf : Summable f := summable_hilbertCubeReLUTerm x
  have hsplit := hf.sum_add_tsum_nat_add N
  have herror :
      hilbertCubeReLUTarget x - hilbertCubeFiniteReLUNetwork N x =
        ∑' n : ℕ, f (n + N) := by
    dsimp only [hilbertCubeReLUTarget, hilbertCubeFiniteReLUNetwork, f] at hsplit ⊢
    linarith
  have hnonneg (n : ℕ) : 0 ≤ f (n + N) := by
    exact mul_nonneg (by positivity) (relu_nonneg _)
  rw [herror, abs_of_nonneg (tsum_nonneg hnonneg)]
  have hgeom : HasSum (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + N + 1))
      (((1 : ℝ) / 2) ^ N) := by
    have hraw : HasSum
        (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (N + 1) * ((1 : ℝ) / 2) ^ n)
        (((1 : ℝ) / 2) ^ (N + 1) * 2) :=
      hasSum_geometric_two.mul_left (((1 : ℝ) / 2) ^ (N + 1))
    have hfun :
        (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + N + 1)) =
          fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (N + 1) * ((1 : ℝ) / 2) ^ n := by
      funext n
      calc
        ((1 : ℝ) / 2) ^ (n + N + 1) = ((1 : ℝ) / 2) ^ ((N + 1) + n) := by
          congr 1
          omega
        _ = ((1 : ℝ) / 2) ^ (N + 1) * ((1 : ℝ) / 2) ^ n := pow_add _ _ _
    have hval : ((1 : ℝ) / 2) ^ (N + 1) * 2 = ((1 : ℝ) / 2) ^ N := by
      rw [pow_succ]
      ring
    rw [hfun, ← hval]
    exact hraw
  calc
    (∑' n : ℕ, f (n + N)) ≤
        ∑' n : ℕ, ((1 : ℝ) / 2) ^ (n + N + 1) := by
      apply ((summable_nat_add_iff N).2 hf).tsum_le_tsum
      · intro n
        dsimp only [f]
        have hx1 : (x (n + N) : ℝ) ≤ 1 := (x (n + N)).property.2
        have hx0 : 0 ≤ (x (n + N) : ℝ) := (x (n + N)).property.1
        rw [relu, max_eq_left hx0]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hx1
            (by positivity : 0 ≤ ((1 : ℝ) / 2) ^ (n + N + 1))
      · exact hgeom.summable
    _ = ((1 : ℝ) / 2) ^ N := hgeom.tsum_eq

/-- Dependence on only a specified finite set of coordinates. -/
def DependsOnCoordinates {Y : Type*} (F : BinaryHilbertCube → Y) (s : Finset ℕ) : Prop :=
  ∀ x y, (∀ i ∈ s, (x i : ℝ) = y i) → F x = F y

theorem hilbertCubeReLUTarget_basis (j : ℕ) :
    hilbertCubeReLUTarget (BinaryHilbertCube.basis j) =
      ((1 : ℝ) / 2) ^ (j + 1) := by
  rw [hilbertCubeReLUTarget]
  rw [tsum_eq_single j]
  · simp [BinaryHilbertCube.basis, relu]
  · intro n hn
    simp [BinaryHilbertCube.basis, hn, relu]

theorem hilbertCubeReLUTarget_not_dependsOnCoordinates (s : Finset ℕ) :
    ¬DependsOnCoordinates hilbertCubeReLUTarget s := by
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
    simp [hilbertCubeReLUTarget, BinaryHilbertCube.zero, relu]
  rw [hzero, hilbertCubeReLUTarget_basis] at heq
  have hpos : 0 < ((1 : ℝ) / 2) ^ (j + 1) := by positivity
  exact hpos.ne' heq.symm

end OperatorRidgelet
