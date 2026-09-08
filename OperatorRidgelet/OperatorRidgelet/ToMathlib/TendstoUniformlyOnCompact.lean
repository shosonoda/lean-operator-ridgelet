import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Order.Filter.Finite

/-!
# Uniformly Lipschitz sequences converge uniformly on compact sets

If `T n` are `K`-Lipschitz maps converging pointwise to a `K`-Lipschitz map `f`, then the
convergence is uniform on every compact set: cover the compact set by finitely many small balls
and use the Lipschitz bounds on each ball.
-/

open Filter Topology
open scoped NNReal

/-- A uniformly Lipschitz sequence converging pointwise to a Lipschitz map converges uniformly
on compact sets. -/
theorem tendstoUniformlyOn_of_lipschitzWith_of_tendsto {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {T : ℕ → X → Y} {f : X → Y} {K : ℝ≥0} (hT : ∀ n, LipschitzWith K (T n))
    (hf : LipschitzWith K f) (hlim : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (f x))) {s : Set X}
    (hs : IsCompact s) : TendstoUniformlyOn T f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hKδ⟩ : ∃ δ : ℝ, 0 < δ ∧ (K : ℝ) * δ < ε / 3 := by
    refine ⟨ε / 3 / ((K : ℝ) + 1), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [K.coe_nonneg, hε]
  obtain ⟨t, -, hcover⟩ := hs.elim_nhds_subcover (fun c => Metric.ball c δ)
    fun c _ => Metric.ball_mem_nhds c hδ
  have hev : ∀ᶠ n in atTop, ∀ c ∈ t, dist (f c) (T n c) < ε / 3 := by
    rw [eventually_all_finset]
    intro c _
    have := Metric.tendsto_nhds.mp (hlim c) (ε / 3) (by positivity)
    filter_upwards [this] with n hn
    rw [dist_comm]
    exact hn
  filter_upwards [hev] with n hn x hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
  rw [Metric.mem_ball] at hxc
  calc dist (f x) (T n x)
      ≤ dist (f x) (f c) + dist (f c) (T n c) + dist (T n c) (T n x) := dist_triangle4 _ _ _ _
    _ ≤ K * dist x c + dist (f c) (T n c) + K * dist c x := by
        gcongr
        · exact hf.dist_le_mul x c
        · exact (hT n).dist_le_mul c x
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm c x]
        have h1 : (K : ℝ) * dist x c ≤ K * δ := by gcongr
        linarith [hn c hc]
    _ = ε := by ring
