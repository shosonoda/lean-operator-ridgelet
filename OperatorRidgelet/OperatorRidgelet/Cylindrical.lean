import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Obstructions to cylindrical factorization

These elementary lemmas isolate the step shared by the Gaussian ReLU and elliptic examples:
a target cannot factor through an observation map if it separates two inputs in one fibre.
-/

namespace OperatorRidgelet

/-- A function `F` factors through an observation map `P`. -/
def FactorsThrough {E Y Z : Type*} (F : E → Y) (P : E → Z) : Prop :=
  ∃ G : Z → Y, F = G ∘ P

/-- A function separating two points of one fibre cannot factor through the observation map. -/
theorem not_factorsThrough_of_fibre_separation {E Y Z : Type*} {F : E → Y} {P : E → Z}
    {x y : E} (hP : P x = P y) (hF : F x ≠ F y) : ¬FactorsThrough F P := by
  rintro ⟨G, hG⟩
  apply hF
  rw [hG]
  exact congrArg G hP

/-- Separating zero from a kernel vector obstructs factorization through a linear map. -/
theorem not_factorsThrough_linear_of_kernel_separation
    {𝕜 E Y Z : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid Z] [Module 𝕜 Z] {F : E → Y} (P : E →ₗ[𝕜] Z) {x : E}
    (hx : x ∈ LinearMap.ker P) (hF : F x ≠ F 0) : ¬FactorsThrough F P := by
  apply not_factorsThrough_of_fibre_separation (x := x) (y := 0)
  · simpa only [LinearMap.mem_ker, map_zero] using hx
  · exact hF

end OperatorRidgelet
