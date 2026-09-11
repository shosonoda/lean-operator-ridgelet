import OperatorRidgelet.Examples.DirichletSolution
import OperatorRidgelet.ToMathlib.SineCompleteness
import OperatorRidgelet.ToMathlib.SineIntegral

/-! # The complete Dirichlet sine eigenbasis -/

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace OperatorRidgelet

/-- The positive Dirichlet sine eigenfunctions form an orthonormal family. -/
theorem orthonormal_dirichletEigenfunction :
    Orthonormal ℝ (fun n : ℕ => dirichletEigenfunction (n + 1)) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [L2.inner_def]
  have heq : (∫ t : UnitOpenInterval,
      inner ℝ (dirichletEigenfunction (m + 1) t) (dirichletEigenfunction (n + 1) t)) =
      ∫ t : UnitOpenInterval,
        (Real.sqrt 2 * Real.sin ((m + 1 : ℕ) * Real.pi * t)) *
        (Real.sqrt 2 * Real.sin ((n + 1 : ℕ) * Real.pi * t)) := by
    apply integral_congr_ae
    filter_upwards [dirichletEigenfunction_coeFn_ae (m + 1),
      dirichletEigenfunction_coeFn_ae (n + 1)] with t ht ht'
    rw [ht, ht']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [heq]
  change (∫ t : Ioo (0 : ℝ) 1,
      (Real.sqrt 2 * Real.sin ((m + 1 : ℕ) * Real.pi * t)) *
      (Real.sqrt 2 * Real.sin ((n + 1 : ℕ) * Real.pi * t))
      ∂(volume.comap Subtype.val)) = _
  rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioo
      (fun t : ℝ => (Real.sqrt 2 * Real.sin ((m + 1 : ℕ) * Real.pi * t)) *
        (Real.sqrt 2 * Real.sin ((n + 1 : ℕ) * Real.pi * t))),
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    Real.integral_normalized_sin_mul (m + 1) (n + 1) (by omega) (by omega)]
  simp


/-- Orthogonality to every positive sine eigenfunction makes all sine integrals vanish. -/
theorem integral_sin_nat_eq_zero {x : UnitL2}
    (hx : ∀ n : ℕ, ⟪dirichletEigenfunction (n+1),x⟫ = 0) (n : ℕ) :
    (∫ t : UnitOpenInterval, Real.sin (n * Real.pi * t) * x t) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := hx n
    rw [L2.inner_def] at h
    have hi : (∫ t : UnitOpenInterval, ⟪dirichletEigenfunction (n+1) t,x t⟫) =
        Real.sqrt 2 * ∫ t : UnitOpenInterval, Real.sin ((n+1 : ℕ) * Real.pi * t) * x t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [dirichletEigenfunction_coeFn_ae (n+1)] with t ht
      rw [ht]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [hi] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- A vector orthogonal to every positive sine eigenfunction is zero. -/
theorem eq_zero_of_inner_dirichletEigenfunction {x : UnitL2}
    (hx : ∀ n : ℕ, ⟪dirichletEigenfunction (n + 1), x⟫ = 0) : x = 0 :=
  MeasureTheory.eq_zero_of_integral_sin (integral_sin_nat_eq_zero hx)

/-- The positive sine eigenfunctions are a Hilbert basis of the unit interval. -/
def dirichletSineBasis : HilbertBasis ℕ ℝ UnitL2 :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_dirichletEigenfunction (by
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    apply eq_zero_of_inner_dirichletEigenfunction
    intro n
    exact (Submodule.mem_orthogonal _ _).mp hx _
      (Submodule.subset_span (Set.mem_range_self n)))

/-- The sine basis uses the positive frequencies in their natural order. -/
theorem dirichletSineBasis_apply (n : ℕ) :
    dirichletSineBasis n = dirichletEigenfunction (n + 1) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

end OperatorRidgelet
