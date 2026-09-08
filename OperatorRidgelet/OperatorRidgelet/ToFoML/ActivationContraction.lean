import FoML.Learning.Contraction
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Activation contraction for ridge-feature classes

FoML proves the contraction theorem for observation-dependent Lipschitz maps.  We expose its
activation specialization in the operator-ridgelet blueprint and prove the ReLU corollary.
-/

noncomputable section

universe u v

namespace OperatorRidgelet

variable {H : Type u} {𝒳 : Type v}

/-- A local ReLU definition, kept independent of the Lean-4.32 `lean-ridgelet` package. -/
def relu (x : ℝ) : ℝ := max x 0

theorem abs_relu_sub_relu_le (u v : ℝ) : |relu u - relu v| ≤ |u - v| := by
  exact abs_max_sub_max_le_abs u v 0

theorem empiricalRademacherComplexity_activation_contraction_finite
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (σ : ℝ → ℝ) (S : Fin n → 𝒳)
    {L : ℝ} (hL : 0 ≤ L) (hσ_zero : σ 0 = 0)
    (hσ : ∀ u v, |σ u - σ v| ≤ L * |u - v|) :
    empiricalRademacherComplexity n (fun h x ↦ σ (F h x)) S ≤
      2 * L * empiricalRademacherComplexity n F S := by
  exact empiricalRademacherComplexity_contraction_finite
    n F (fun _ u ↦ σ u) S hL (fun _ ↦ hσ_zero) (fun _ ↦ hσ)

theorem empiricalRademacherComplexity_relu_contraction_finite
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun h x ↦ relu (F h x)) S ≤
      2 * empiricalRademacherComplexity n F S := by
  simpa using
    (empiricalRademacherComplexity_activation_contraction_finite
      n F relu S (L := 1) (by norm_num) (by simp [relu])
      (by
        intro u v
        simpa using abs_relu_sub_relu_le u v))

end OperatorRidgelet
