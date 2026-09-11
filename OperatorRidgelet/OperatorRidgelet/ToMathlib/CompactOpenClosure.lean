import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Closure from uniform approximation on compact sets -/

open Topology

namespace ContinuousMap

/-- Uniform approximation on each compact set implies membership in the compact-open closure. -/
theorem mem_closure_of_forall_isCompact {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y] {s : Set C(X, Y)} {f : C(X, Y)}
    (h : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ s, ∀ x ∈ K, dist (f x) (g x) < ε) : f ∈ closure s := by
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity Metric.uniformity_basis_dist.compactConvergenceUniformity)]
  rintro ⟨K, ε⟩ ⟨hK, hε⟩
  obtain ⟨g, hg, hfg⟩ := h K hK ε hε
  exact ⟨g, hg, fun x hx => by
    change dist (g x) (f x) < ε
    simpa only [dist_comm] using hfg x hx⟩

end ContinuousMap
