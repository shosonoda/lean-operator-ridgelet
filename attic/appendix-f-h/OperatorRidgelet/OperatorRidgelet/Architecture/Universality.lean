import OperatorRidgelet.Architecture.Reduction
import OperatorRidgelet.ToMathlib.CompactOpenClosure
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem

/-!
# Compact-open universality for scalar and operator neurons

The finite-dimensional Leshno theorem is transported along continuous linear maps.
Finite-rank orthogonal projections then give approximation on every compact subset of
a separable Hilbert space. The rank-one section transfers this density to operator neurons.
-/

noncomputable section

namespace OperatorRidgelet

open Topology Filter
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem exists_ridgeSpan_lift {β : ℝ → ℝ} (hβ : Continuous β)
    {n : ℕ} (L : H →L[ℝ] EuclideanSpace ℝ (Fin n))
    (K : Set (EuclideanSpace ℝ (Fin n))) {g : K → ℝ}
    (hg : g ∈ UniversalApproximation.Leshno.genSpan β K) :
    ∃ G ∈ Submodule.span ℝ (ridgeSet (H := H) β),
      ∀ x (hx : L x ∈ K), G x = g ⟨L x, hx⟩ := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨a, c⟩, rfl⟩ := hg
    let G : C(H, ℝ) := ⟨fun x => β (inner ℝ (L.adjoint a) x + c), hβ.comp (by fun_prop)⟩
    refine ⟨G, Submodule.subset_span ⟨L.adjoint a, c, rfl⟩, ?_⟩
    intro x hx
    simp only [G, ContinuousMap.coe_mk, UniversalApproximation.Leshno.genFun,
      ContinuousLinearMap.adjoint_inner_left]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
  | add g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, hG₁, he₁⟩ := ih₁
    obtain ⟨G₂, hG₂, he₂⟩ := ih₂
    exact ⟨G₁ + G₂, Submodule.add_mem _ hG₁ hG₂,
      fun x hx => by simp only [ContinuousMap.add_apply, Pi.add_apply, he₁ x hx, he₂ x hx]⟩
  | smul c g _ ih =>
    obtain ⟨G, hG, he⟩ := ih
    exact ⟨c • G, Submodule.smul_mem _ c hG,
      fun x hx => by simp only [ContinuousMap.smul_apply, Pi.smul_apply, he x hx]⟩

/-- A continuous function of finitely many linear coordinates lies in the closure of the
ridge span for every continuous non-polynomial activation. -/
theorem finiteCoordinate_mem_closure_ridgeSpan {β : ℝ → ℝ} (hβ : Continuous β)
    (hpoly : ¬ IsPolynomialFun β) {n : ℕ} (L : H →L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : C(EuclideanSpace ℝ (Fin n), ℝ)) :
    f.comp ⟨L, L.continuous⟩ ∈
      closure (Submodule.span ℝ (ridgeSet (H := H) β) : Set C(H, ℝ)) := by
  have hnp : ¬ UniversalApproximation.Leshno.IsAEPolynomial β := by
    intro hp
    obtain ⟨p, hp⟩ :=
      UniversalApproximation.Leshno.isPolynomialFun_of_continuous_of_aePolynomial hβ hp
    exact hpoly ⟨p, fun x => congrFun hp x⟩
  have hd : UniversalApproximation.Leshno.DenselyApproximates β :=
    UniversalApproximation.Leshno.leshno_dense
    (UniversalApproximation.Leshno.ClassM.of_continuous hβ) hnp
  apply ContinuousMap.mem_closure_of_forall_isCompact
  intro K hK ε hε
  obtain ⟨g, hg, he⟩ := hd (L '' K) (hK.image L.continuous)
    (f.comp ⟨Subtype.val, continuous_subtype_val⟩) hε
  obtain ⟨G, hG, hGe⟩ := exists_ridgeSpan_lift hβ L (L '' K) hg
  refine ⟨G, hG, fun x hx => ?_⟩
  have hLx : L x ∈ L '' K := ⟨x, hx, rfl⟩
  rw [hGe x hLx]
  exact he ⟨L x, hLx⟩

/-- The scalar ridge span is dense for uniform convergence on compact sets. -/
theorem dense_ridgeSpan [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) :
    Dense (Submodule.span ℝ (ridgeSet (H := H) β) : Set C(H, ℝ)) := by
  intro f
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq H
  let P : ℕ → C(H, H) := fun n =>
    ⟨(spanFirst u n).starProjection, (spanFirst u n).starProjection.continuous⟩
  have hP : Tendsto P atTop (𝓝 (ContinuousMap.id H)) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    exact tendstoUniformlyOn_of_lipschitzWith_of_tendsto
      (fun n => lipschitzWith_one_starProjection (spanFirst u n))
      LipschitzWith.id (tendsto_starProjection_spanFirst hu) hK
  have hfP : Tendsto (fun n => f.comp (P n)) atTop (𝓝 f) := by
    simpa only [ContinuousMap.comp_id, Function.comp_def] using
      (ContinuousMap.continuous_postcomp f).tendsto _ |>.comp hP
  apply isClosed_closure.mem_of_tendsto hfP
  apply Eventually.of_forall
  intro n
  let V := spanFirst u n
  let b := stdOrthonormalBasis ℝ V
  let L : H →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    b.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L V.orthogonalProjectionOnto
  let g : C(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℝ) :=
    ⟨fun x => f (b.repr.symm x : H), f.continuous.comp
      (continuous_subtype_val.comp b.repr.symm.continuous)⟩
  have he : f.comp (P n) = g.comp ⟨L, L.continuous⟩ := by
    ext x
    change f ((V.orthogonalProjectionOnto x : V) : H) =
      f ((b.repr.symm (b.repr (V.orthogonalProjectionOnto x)) : V) : H)
    rw [b.repr.symm_apply_apply]
  rw [he]
  exact finiteCoordinate_mem_closure_ridgeSpan hβ hpoly L g

/-- The rank-one section embeds every scalar ridge into the Hilbert–Schmidt operator
neuron family. -/
theorem ridgeSet_subset_operatorNeuronSet {β : ℝ → ℝ} {ψ z : H}
    (hψ : ψ ≠ 0) (hz : z ≠ 0) :
    ridgeSet β ⊆ operatorNeuronSet (rankOneActivation β ψ z) {A | IsHilbertSchmidt A} := by
  rintro f ⟨a, c, hf⟩
  let ℓ := (‖z‖ ^ 2)⁻¹ • z
  have hℓ : inner ℝ ℓ z = 1 := by
    simp only [ℓ, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  refine ⟨ℓ, biasLift ψ c, rankOneLift ψ a, isHilbertSchmidt_rankOneLift ψ a, ?_⟩
  funext x
  rw [congrFun hf x, operatorNeuron_rankOneActivation_section β hψ hℓ]

/-- Continuous non-polynomial rank-one activations give compact-open universality with
Hilbert–Schmidt operator parameters. -/
theorem dense_operatorNeuronSpan [SecondCountableTopology H] {β : ℝ → ℝ}
    (hβ : Continuous β) (hpoly : ¬ IsPolynomialFun β) {ψ z : H}
    (hψ : ψ ≠ 0) (hz : z ≠ 0) :
    Dense (Submodule.span ℝ
      (operatorNeuronSet (rankOneActivation β ψ z) {A | IsHilbertSchmidt A}) : Set C(H, ℝ)) :=
  (dense_ridgeSpan hβ hpoly).mono
    (Submodule.span_mono (ridgeSet_subset_operatorNeuronSet hψ hz))

end OperatorRidgelet
