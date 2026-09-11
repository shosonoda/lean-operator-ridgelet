import OperatorRidgelet.Architecture.Defs
import OperatorRidgelet.Architecture.Basic
import OperatorRidgelet.ToMathlib.TendstoUniformlyOnCompact
import OperatorRidgelet.ToMathlib.StarProjectionBessel
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The Hilbert–Schmidt reduction of operator neurons (Lemma F.1)

The finite-rank orthogonal projections `Π_n` onto the spans of the first `n` terms of a dense
sequence converge strongly to the identity, uniformly on compact sets; `A Π_n` is Hilbert–Schmidt
for every bounded `A`; and the operator neurons `n_{ℓ,AΠ_n,b}` converge to `n_{ℓ,A,b}` in the
compact-open topology of `C(H, ℝ)` when the activation `σ` is Lipschitz.
-/

noncomputable section

namespace OperatorRidgelet

open Filter Topology
open scoped NNReal RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The span of the first `n` terms of a sequence `u`. -/
def spanFirst (u : ℕ → H) (n : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (u '' Set.Iio n)

/-- The span of finitely many vectors is finite-dimensional. -/
instance instFiniteDimensionalSpanFirst (u : ℕ → H) (n : ℕ) :
    FiniteDimensional ℝ (spanFirst u n) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image u)

/-- Each finite-dimensional approximation subspace is complete. -/
instance instCompleteSpaceSpanFirst (u : ℕ → H) (n : ℕ) : CompleteSpace (spanFirst u n) :=
  FiniteDimensional.complete ℝ _

/-- The orthogonal projections onto `span {u 0, …, u (n-1)}` converge strongly to the identity
when `u` has dense range. -/
theorem tendsto_starProjection_spanFirst {u : ℕ → H} (hu : DenseRange u) (x : H) :
    Tendsto (fun n => (spanFirst u n).starProjection x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp hu x ε hε
  refine ⟨m + 1, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm, Submodule.starProjection_minimal]
  have hmem : u m ∈ spanFirst u n :=
    Submodule.subset_span ⟨m, Set.mem_Iio.mpr (by omega), rfl⟩
  refine lt_of_le_of_lt (ciInf_le ⟨0, ?_⟩ ⟨u m, hmem⟩) ?_
  · rintro _ ⟨y, rfl⟩
    exact norm_nonneg _
  · rwa [← dist_eq_norm]

/-- Orthogonal projections are `1`-Lipschitz. -/
theorem lipschitzWith_one_starProjection (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    LipschitzWith 1 K.starProjection :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact K.norm_starProjection_apply_le _

/-- `A Π` is Hilbert–Schmidt for every bounded `A` and every finite-rank orthogonal
projection `Π`. -/
theorem isHilbertSchmidt_comp_starProjection (A : H →L[ℝ] H) (K : Submodule ℝ H)
    [FiniteDimensional ℝ K] : IsHilbertSchmidt (A ∘L K.starProjection) := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖A‖ ^ 2 * Module.finrank ℝ K))
    (hsNormSq_le fun s hs => ?_)
  rw [sum_enorm_sq_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ e ∈ s, ‖(A ∘L K.starProjection) e‖ ^ 2
      ≤ ∑ e ∈ s, ‖A‖ ^ 2 * ‖K.starProjection e‖ ^ 2 := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [ContinuousLinearMap.comp_apply, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = ‖A‖ ^ 2 * ∑ e ∈ s, ‖K.starProjection e‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ‖A‖ ^ 2 * Module.finrank ℝ K := by
        gcongr
        have := Orthonormal.sum_norm_sq_starProjection_le K hs Finset.univ
        rwa [Finset.sum_coe_sort s (fun e => ‖K.starProjection e‖ ^ 2)] at this

/-- The operator neuron `x ↦ ⟪ℓ, σ(A x + b)⟫` is continuous for Lipschitz `σ`. -/
theorem continuous_operatorNeuron {σ : H → H} {L : ℝ≥0} (hσ : LipschitzWith L σ) (ℓ : H)
    (A : H →L[ℝ] H) (b : H) : Continuous (operatorNeuron σ ℓ A b) :=
  continuous_const.inner (hσ.continuous.comp (A.continuous.add continuous_const))

/-- Every operator neuron with a bounded parameter is a compact-open limit of operator neurons
with Hilbert–Schmidt parameters, hence lies in the closure of their span. -/
theorem operatorNeuron_mem_closure_span_hilbertSchmidt [SecondCountableTopology H] {σ : H → H}
    {L : ℝ≥0} (hσ : LipschitzWith L σ) (ℓ : H) (A : H →L[ℝ] H) (b : H) {F : C(H, ℝ)}
    (hF : ⇑F = operatorNeuron σ ℓ A b) :
    F ∈ closure (Submodule.span ℝ (operatorNeuronSet σ {A | IsHilbertSchmidt A}) :
      Set C(H, ℝ)) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq H
  let Pn : ℕ → (H →L[ℝ] H) := fun n => (spanFirst u n).starProjection
  let Fn : ℕ → C(H, ℝ) := fun n =>
    ⟨operatorNeuron σ ℓ (A ∘L Pn n) b, continuous_operatorNeuron hσ ℓ _ b⟩
  refine mem_closure_of_tendsto (f := Fn) (b := atTop) ?_ (Eventually.of_forall fun n =>
    Submodule.subset_span ⟨ℓ, b, A ∘L Pn n, isHilbertSchmidt_comp_starProjection A _, rfl⟩)
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  have hP : TendstoUniformlyOn (fun n x => Pn n x) id atTop K :=
    tendstoUniformlyOn_of_lipschitzWith_of_tendsto (fun n => lipschitzWith_one_starProjection _)
      LipschitzWith.id (tendsto_starProjection_spanFirst hu) hK
  rw [Metric.tendstoUniformlyOn_iff] at hP ⊢
  intro ε hε
  set C : ℝ := ‖ℓ‖ * L * ‖A‖ with hC
  have hC0 : 0 ≤ C := by positivity
  filter_upwards [hP (ε / (C + 1)) (by positivity)] with n hn x hx
  rw [hF]
  show dist (operatorNeuron σ ℓ A b x) (operatorNeuron σ ℓ (A ∘L Pn n) b x) < ε
  simp only [operatorNeuron, ContinuousLinearMap.comp_apply]
  rw [Real.dist_eq, ← inner_sub_right]
  have hd := hn x hx
  simp only [id] at hd
  calc |⟪ℓ, σ (A x + b) - σ (A (Pn n x) + b)⟫|
      ≤ ‖ℓ‖ * ‖σ (A x + b) - σ (A (Pn n x) + b)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ℓ‖ * (L * ‖(A x + b) - (A (Pn n x) + b)‖) := by
        gcongr
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hσ.dist_le_mul _ _
    _ = ‖ℓ‖ * (L * ‖A (x - Pn n x)‖) := by
        congr 3
        rw [map_sub]
        abel
    _ ≤ ‖ℓ‖ * (L * (‖A‖ * ‖x - Pn n x‖)) := by
        gcongr
        exact A.le_opNorm _
    _ = C * dist x (Pn n x) := by
        rw [dist_eq_norm, hC]
        ring
    _ < ε := by
        calc C * dist x (Pn n x) ≤ C * (ε / (C + 1)) := by gcongr
          _ < ε := by
              rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
              nlinarith

end OperatorRidgelet
