import FoML.Probability.McDiarmid
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The bounded-difference inequality for the norm of a centred empirical sum

For a probability measure `p` on `Ω`, a strongly measurable `g : Ω → E` with `‖g‖ ≤ M`
everywhere, and the law `p^{⊗N} = Measure.pi (fun _ : Fin N => p)` of `N` independent samples,
the function `F(ω) = ‖∑_j g(ω_j) − N ∫ g dp‖` changes by at most `2M` when one sample is
replaced (`abs_norm_sum_sub_sub_norm_sum_update_sub_le`), so FoML's McDiarmid inequality
`mcdiarmid_inequality_pos_iid_of_const` gives the upper tail bound
`p^{⊗N} {F − ∫ F dp^{⊗N} ≥ ε} ≤ exp(−ε² / (2 N M²))`
(`measure_norm_sum_sub_sub_integral_ge_le`).
-/

open MeasureTheory
open scoped ENNReal

namespace OperatorRidgelet

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace Ω] [NormedSpace ℝ E] in
/-- Replacing one sample changes `‖∑_j g(ω_j) − v‖` by at most `2M` when `‖g‖ ≤ M`. -/
theorem abs_norm_sum_sub_sub_norm_sum_update_sub_le {N : ℕ} {g : Ω → E} {M : ℝ}
    (hg : ∀ ω, ‖g ω‖ ≤ M) (v : E) (i : Fin N) (ω : Fin N → Ω) (ω' : Ω) :
    |‖∑ j, g (ω j) - v‖ - ‖∑ j, g (Function.update ω i ω' j) - v‖| ≤ 2 * M := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hdiff : (∑ j, g (ω j) - v) - (∑ j, g (Function.update ω i ω' j) - v) =
      g (ω i) - g ω' := by
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj, sub_self])
        (fun h => absurd (Finset.mem_univ i) h), Function.update_self]
  rw [hdiff]
  calc ‖g (ω i) - g ω'‖ ≤ ‖g (ω i)‖ + ‖g ω'‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hg _) (hg _)
    _ = 2 * M := by ring

/-- **Bounded-difference inequality for the norm of a centred empirical sum.**  For `N`
independent samples `ω_j ∼ p` of a strongly measurable `g` with `‖g‖ ≤ M` everywhere, `M > 0`,
the deviation of `F(ω) = ‖∑_j g(ω_j) − N ∫ g dp‖` above its mean satisfies
`p^{⊗N} {F − ∫ F dp^{⊗N} ≥ ε} ≤ exp(−ε² / (2 N M²))` for every `ε ≥ 0`. -/
theorem measure_norm_sum_sub_sub_integral_ge_le (p : Measure Ω) [IsProbabilityMeasure p]
    {g : Ω → E} (hg : StronglyMeasurable g) {M : ℝ} (hM : 0 < M) (hgM : ∀ ω, ‖g ω‖ ≤ M)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin N => p) {ω | ε ≤ ‖∑ j, g (ω j) - (N : ℝ) • ∫ x, g x ∂p‖ -
        ∫ ω', ‖∑ j, g (ω' j) - (N : ℝ) • ∫ x, g x ∂p‖ ∂(Measure.pi fun _ : Fin N => p)} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * N * M ^ 2))) := by
  haveI : Nonempty Ω := Measure.nonempty_of_neZero p
  set v : E := (N : ℝ) • ∫ x, g x ∂p with hv
  set F : (Fin N → Ω) → ℝ := fun ω => ‖∑ j, g (ω j) - v‖ with hF
  have hFmeas : Measurable F :=
    ((Finset.stronglyMeasurable_fun_sum Finset.univ fun j _ =>
      hg.comp_measurable (measurable_pi_apply j)).sub stronglyMeasurable_const).norm.measurable
  have hFdiff : ∀ (i : Fin N) (ω : Fin N → Ω) (ω' : Ω),
      |F ω - F (Function.update ω i ω')| ≤ 2 * M :=
    fun i ω ω' => abs_norm_sum_sub_sub_norm_sum_update_sub_le hgM v i ω ω'
  have ht : 1 / (4 * N * M ^ 2) * (Fintype.card (Fin N) : ℝ) * (2 * M) ^ 2 ≤ 1 := by
    rw [Fintype.card_fin]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have : 1 / (4 * N * M ^ 2) * (N : ℝ) * (2 * M) ^ 2 = 1 := by
        field_simp
        ring
      exact this.le
  have hmc := mcdiarmid_inequality_pos_iid_of_const (μ := p) (X' := (id : Ω → Ω)) measurable_id
    hFdiff hFmeas hε ht
  simp only [Function.id_comp] at hmc
  have hexp : Real.exp (-2 * ε ^ 2 * (1 / (4 * N * M ^ 2))) =
      Real.exp (-ε ^ 2 / (2 * N * M ^ 2)) := by
    congr 1
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      field_simp
      ring
  rw [hexp] at hmc
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr hmc

end OperatorRidgelet
