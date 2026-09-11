import OperatorRidgelet.Examples.DirichletSolution
import OperatorRidgelet.ToMathlib.DiagonalHilbertBasis
import Mathlib.Analysis.PSeries

/-! # Spectral properties of the Dirichlet solution operator -/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Topology LeanRidgelet
open scoped RealInnerProductSpace

/-- Every Dirichlet eigenvalue is strictly positive, including the unused zero frequency. -/
theorem dirichletEigenvalue_pos (n : ℕ) : 0 < dirichletEigenvalue n := by
  unfold dirichletEigenvalue
  positivity

/-- The positive-frequency Dirichlet eigenvalues form a summable sequence. -/
theorem summable_dirichletEigenvalue : Summable (fun n : ℕ => dirichletEigenvalue (n + 1)) := by
  have hs : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by norm_num))
  apply (hs.mul_left (Real.pi ^ 2)⁻¹).of_nonneg_of_le
    (fun n => (dirichletEigenvalue_pos _).le)
  intro n
  rw [← mul_inv_rev]
  unfold dirichletEigenvalue
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- The Dirichlet eigenvalues decrease with the frequency. -/
theorem dirichletEigenvalue_antitone : Antitone dirichletEigenvalue := by
  intro m n hmn
  unfold dirichletEigenvalue
  apply inv_anti₀ (by positivity)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  gcongr

/-- The frequency-zero Dirichlet sine is the zero vector. -/
theorem dirichletEigenfunction_zero : dirichletEigenfunction 0 = 0 := by
  apply Lp.ext
  filter_upwards [dirichletEigenfunction_coeFn_ae 0, Lp.coeFn_zero ℝ 2 volume] with t ht hz
  simp only [Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero] at ht
  exact ht.trans hz.symm

variable (b : HilbertBasis ℕ ℝ UnitL2)
    (hb : ∀ n, b n = dirichletEigenfunction (n + 1))

include b hb

/-- A complete sine eigenbasis makes the Green operator an injective positive trace-class
covariance operator. -/
theorem isTraceClassCovariance_dirichletOperator_of_basis :
    IsTraceClassCovariance dirichletOperator := by
  have he (n : ℕ) : dirichletOperator (b n) = dirichletEigenvalue (n + 1) • b n := by
    rw [hb, dirichletOperator_eigenfunction]
  refine ⟨⟨b.isSelfAdjoint_of_eigen he,
    b.inner_map_self_nonneg_of_eigen he (fun n => (dirichletEigenvalue_pos _).le), ?_⟩,
    b.injective_of_eigen he (fun n => ne_of_gt (dirichletEigenvalue_pos _))⟩
  refine ⟨ℕ, b, ?_⟩
  have hnorm (n : ℕ) : ‖b n‖ = 1 := b.orthonormal.1 n
  simpa only [he, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm,
    one_pow, mul_one] using summable_dirichletEigenvalue

/-- The full Dirichlet Green operator is the convergent signed-pair ReLU expansion. -/
theorem hasSum_dirichletReLU_of_basis (x : UnitL2) :
    HasSum (fun n : ℕ => (dirichletEigenvalue n *
      (relu ⟪dirichletEigenfunction n, x⟫ - relu (-⟪dirichletEigenfunction n, x⟫))) •
        dirichletEigenfunction n) (dirichletOperator x) := by
  simp only [relu_sub_relu_neg]
  have he (n : ℕ) : dirichletOperator (b n) = dirichletEigenvalue (n + 1) • b n := by
    rw [hb, dirichletOperator_eigenfunction]
  have hs : HasSum (fun n : ℕ => (dirichletEigenvalue (n + 1) *
      ⟪dirichletEigenfunction (n + 1), x⟫) • dirichletEigenfunction (n + 1))
      (dirichletOperator x) := by
    simpa only [hb] using b.hasSum_map_of_eigen he x
  have hs' := (hasSum_nat_add_iff (f := fun n =>
    (dirichletEigenvalue n * ⟪dirichletEigenfunction n, x⟫) • dirichletEigenfunction n) 1).1 hs
  simpa only [hb, Finset.sum_range_one, dirichletEigenfunction_zero, inner_zero_left,
    mul_zero, zero_smul, add_zero] using hs'

/-- The positive-frequency sine sum equals the manuscript's `2N`-neuron network. -/
theorem dirichletReLUTruncation_eq_sum_basis (n : ℕ) (x : UnitL2) :
    dirichletReLUTruncation n x =
      ∑ i ∈ Finset.range n, (dirichletEigenvalue (i + 1) * ⟪b i, x⟫) • b i := by
  rw [dirichletReLUTruncation, spectralReLUNetwork_eq]
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rw [hb]

/-- The Dirichlet truncation error is controlled by the first omitted eigenvalue. -/
theorem norm_dirichletReLUTruncation_error_of_basis (n : ℕ) (x : UnitL2) :
    ‖dirichletOperator x - dirichletReLUTruncation n x‖ ≤
      dirichletEigenvalue (n + 1) * ‖x‖ := by
  rw [dirichletReLUTruncation_eq_sum_basis b hb]
  have he (i : ℕ) : dirichletOperator (b i) = dirichletEigenvalue (i + 1) • b i := by
    rw [hb, dirichletOperator_eigenfunction]
  apply b.norm_map_sub_sum_le he _ (dirichletEigenvalue_pos _).le
  intro i hi
  rw [abs_of_pos (dirichletEigenvalue_pos _)]
  exact dirichletEigenvalue_antitone (Nat.add_le_add_right
    (by simpa only [Finset.mem_range, not_lt] using hi) 1)

end OperatorRidgelet
