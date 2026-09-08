import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Elementary growth bounds

* `one_add_pow_le_two_pow_mul_two_add_pow`: `(1 + x)^N ≤ 2^N (2 + x^(2N))` for `x ≥ 0`, which
  dominates a polynomial weight `(1 + x)^N` by even powers.
* `IsCompact.exists_pos_le_abs_le`: a compact subset of `ℝ` not containing `0` lies in an
  annulus `r ≤ |ω| ≤ R` with `0 < r`.
-/

/-- `(1 + x)^N ≤ 2^N (2 + x^(2N))` for `x ≥ 0`. -/
theorem one_add_pow_le_two_pow_mul_two_add_pow (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ N ≤ 2 ^ N * (2 + x ^ (2 * N)) := by
  rcases le_or_gt x 1 with h | h
  · calc (1 + x) ^ N ≤ (1 + 1) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * 1 := by ring
      _ ≤ 2 ^ N * (2 + x ^ (2 * N)) := by
          gcongr
          linarith [pow_nonneg hx (2 * N)]
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (2 + x ^ (2 * N)) := by
          gcongr
          have : x ^ N ≤ x ^ (2 * N) := pow_le_pow_right₀ h.le (by omega)
          linarith

/-- A compact subset of `ℝ` not containing `0` lies in an annulus `r ≤ |ω| ≤ R` with `0 < r`. -/
theorem IsCompact.exists_pos_le_abs_le {I : Set ℝ} (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) :
    ∃ r R : ℝ, 0 < r ∧ ∀ ω ∈ I, r ≤ |ω| ∧ |ω| ≤ R := by
  obtain ⟨R, hR⟩ := hI.isBounded.subset_closedBall (0 : ℝ)
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, R, one_pos, fun ω hω => hω.elim⟩
  obtain ⟨ω₀, hω₀, hmin⟩ := hI.exists_isMinOn hne continuous_norm.continuousOn
  refine ⟨|ω₀|, R, abs_pos.mpr fun h => hI0 (h ▸ hω₀), fun ω hω => ⟨?_, ?_⟩⟩
  · simpa [Real.norm_eq_abs] using (hmin hω : ‖ω₀‖ ≤ ‖ω‖)
  · simpa [Real.dist_eq] using hR hω
