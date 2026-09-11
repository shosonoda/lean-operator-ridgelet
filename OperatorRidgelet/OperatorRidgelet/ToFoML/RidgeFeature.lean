import OperatorRidgelet.ToFoML.ActivationContraction
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Rademacher contraction for sampled ridge features on a compact candidate set

The theorem is stated for an arbitrary subset `K` of a real inner-product space; compactness is
therefore available to downstream compact-open arguments but is not unnecessarily required by the
finite-sample contraction step itself.
-/

noncomputable section

universe u v

namespace OperatorRidgelet

open LeanRidgelet

variable {H : Type u} {E : Type v}
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Affine preactivations restricted to an input set `K`. -/
def sampledRidgePreactivation (K : Set E) (a : H → E) (b : H → ℝ) :
    H → K → ℝ :=
  fun h x ↦ inner ℝ (a h) x - b h

/-- Lipschitz activation controls the empirical complexity of sampled affine ridge features. -/
theorem empiricalRademacherComplexity_sampledRidge_activation_contraction_finite
    [Fintype H] [Nonempty H]
    (K : Set E) (n : ℕ) (a : H → E) (b : H → ℝ) (σ : ℝ → ℝ)
    (S : Fin n → K) {L : ℝ} (hL : 0 ≤ L) (hσ_zero : σ 0 = 0)
    (hσ : ∀ u v, |σ u - σ v| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (fun h x ↦ σ (sampledRidgePreactivation K a b h x)) S ≤
      2 * L * empiricalRademacherComplexity n
        (sampledRidgePreactivation K a b) S := by
  exact empiricalRademacherComplexity_activation_contraction_finite
    n (sampledRidgePreactivation K a b) σ S hL hσ_zero hσ

/-- ReLU contracts the empirical complexity of sampled affine ridge features. -/
theorem empiricalRademacherComplexity_sampledRidge_relu_contraction_finite
    [Fintype H] [Nonempty H]
    (K : Set E) (n : ℕ) (a : H → E) (b : H → ℝ) (S : Fin n → K) :
    empiricalRademacherComplexity n
        (fun h x ↦ relu (sampledRidgePreactivation K a b h x)) S ≤
      2 * empiricalRademacherComplexity n (sampledRidgePreactivation K a b) S := by
  exact empiricalRademacherComplexity_relu_contraction_finite
    n (sampledRidgePreactivation K a b) S

end OperatorRidgelet
