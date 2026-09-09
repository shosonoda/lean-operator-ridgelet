import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.ToMathlib.TraceClassEigenbasis
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Obstructions to cylindricity

A cylindrical function factors through a linear map `L : H → ℝ^m`.  In an infinite-dimensional
space `H` the kernel of `L` is nontrivial (`exists_ne_zero_mem_ker_of_not_finiteDimensional`),
so a function that separates every nonzero vector from the origin is not cylindrical
(`not_isCylindrical_of_ne_zero`).  Moreover, if `A` has infinite rank then `ker L` is not
contained in `ker A` (`HasInfiniteRank.exists_mem_ker_not_mem_ker`), which is the input of the
non-cylindricity argument for the neural-operator layer.  The positivity of a quadratic form
along an eigenbasis with positive eigenvalues (`inner_map_self_pos_of_eigen`) supplies the
separation for the Gaussian-parameter networks.
-/

noncomputable section

namespace OperatorRidgelet

open scoped RealInnerProductSpace

section Linear

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- In an infinite-dimensional space every linear map to `ℝ^m` has a nonzero kernel element. -/
theorem exists_ne_zero_mem_ker_of_not_finiteDimensional (hH : ¬ FiniteDimensional ℝ H) {m : ℕ}
    (L : H →ₗ[ℝ] (Fin m → ℝ)) : ∃ x : H, x ≠ 0 ∧ L x = 0 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    exact h x hx0 hx
  exact hH (FiniteDimensional.of_injective L hinj)

/-- A function that separates every nonzero vector from the origin is not cylindrical. -/
theorem not_isCylindrical_of_ne_zero {Y : Type*} (hH : ¬ FiniteDimensional ℝ H) {f : H → Y}
    (hf : ∀ x, x ≠ 0 → f x ≠ f 0) : ¬ IsCylindrical f := by
  rintro ⟨m, L, G, hG⟩
  obtain ⟨x, hx, hLx⟩ := exists_ne_zero_mem_ker_of_not_finiteDimensional hH L
  apply hf x hx
  rw [hG, Function.comp_apply, Function.comp_apply, hLx, map_zero]

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The domain of a linear map of infinite rank is infinite dimensional. -/
theorem HasInfiniteRank.not_finiteDimensional {A : H →ₗ[ℝ] F} (hA : HasInfiniteRank A) :
    ¬ FiniteDimensional ℝ H := fun _ => hA inferInstance

/-- If `A` has infinite rank, the kernel of a linear map `L : H → ℝ^m` is not contained in the
kernel of `A`. -/
theorem HasInfiniteRank.exists_mem_ker_not_mem_ker {A : H →ₗ[ℝ] F} (hA : HasInfiniteRank A)
    {m : ℕ} (L : H →ₗ[ℝ] (Fin m → ℝ)) : ∃ x : H, L x = 0 ∧ A x ≠ 0 := by
  by_contra h
  push Not at h
  have hle : LinearMap.ker L ≤ LinearMap.ker A := fun x hx => h x hx
  apply hA
  haveI : FiniteDimensional ℝ (H ⧸ LinearMap.ker L) :=
    (LinearMap.quotKerEquivRange L).symm.finiteDimensional
  rw [← Submodule.range_liftQ (LinearMap.ker L) A hle]
  infer_instance

end Linear

section Eigen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A space with a Hilbert basis indexed by `ℕ` is infinite dimensional. -/
theorem not_finiteDimensional_of_hilbertBasis (e : HilbertBasis ℕ ℝ H) :
    ¬ FiniteDimensional ℝ H := by
  intro _
  haveI := e.orthonormal.linearIndependent.finite_of_isNoetherian
  exact not_finite ℕ

/-- The quadratic form of an operator diagonal in a Hilbert basis with positive eigenvalues is
positive definite. -/
theorem inner_map_self_pos_of_eigen {Q : H →L[ℝ] H} {κ : Type*} (e : HilbertBasis κ ℝ H)
    (q : κ → ℝ) (hq : ∀ j, 0 < q j) (hQe : ∀ j, Q (e j) = q j • e j) {x : H} (hx : x ≠ 0) :
    0 < ⟪Q x, x⟫ := by
  have hsum := ContinuousLinearMap.hasSum_inner_map_self_of_eigen e q hQe x
  have hrepr : e.repr x ≠ 0 := fun h => hx (e.repr.map_eq_zero_iff.mp h)
  obtain ⟨j, hj⟩ : ∃ j, e.repr x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hrepr (by ext j; simpa using h j)
  rw [e.repr_apply_apply] at hj
  have hpos : 0 < q j * ⟪e j, x⟫ ^ 2 := mul_pos (hq j) (by positivity)
  exact hpos.trans_le (le_hasSum hsum j fun i _ => mul_nonneg (hq i).le (sq_nonneg _))

/-- The quadratic form of an operator diagonal in a Hilbert basis with positive eigenvalues is
nonnegative. -/
theorem inner_map_self_nonneg_of_eigen {Q : H →L[ℝ] H} {κ : Type*} (e : HilbertBasis κ ℝ H)
    (q : κ → ℝ) (hq : ∀ j, 0 < q j) (hQe : ∀ j, Q (e j) = q j • e j) (x : H) :
    0 ≤ ⟪Q x, x⟫ :=
  (ContinuousLinearMap.hasSum_inner_map_self_of_eigen e q hQe x).nonneg fun i =>
    mul_nonneg (hq i).le (sq_nonneg _)

end Eigen

end OperatorRidgelet
