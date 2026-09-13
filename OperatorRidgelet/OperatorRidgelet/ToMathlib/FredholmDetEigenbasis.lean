import OperatorRidgelet.ToMathlib.TraceBasisIndependent

/-!
# The Fredholm determinant does not depend on the orthonormal eigenbasis

Let `M` be a positive self-adjoint operator on a real Hilbert space whose trace converges, and
let `e` be an orthonormal basis of eigenvectors of `M` with eigenvalues `w`.  The product
`∏ (1 + w_i)` is the same for every such basis.  The proof identifies the multiplicity of a
nonzero eigenvalue `λ` with the trace of the orthogonal projection onto the `λ`-eigenspace,
which is basis independent by
`ContinuousLinearMap.tsum_ofReal_inner_map_self_eq`; the eigenindices with the same eigenvalue
are then matched by a bijection and the two products are compared with
`Equiv.tprod_eq_tprod_of_mulSupport`.

* `ContinuousLinearMap.inner_eigen_self`: `⟪M e_i, e_i⟫ = w_i`;
* `ContinuousLinearMap.nonempty_equiv_eigenIndex`: the eigenindices of a nonzero eigenvalue are
  in bijection;
* `ContinuousLinearMap.tprod_one_add_inner_eigen_eq`: the Fredholm determinant along two
  orthonormal eigenbases.
-/

open scoped RealInnerProductSpace ENNReal

/-- A summable real family takes a nonzero value only finitely often. -/
theorem Summable.finite_setOf_eq_of_ne_zero {ι : Type*} {w : ι → ℝ} (hw : Summable w) {lam : ℝ}
    (hlam : lam ≠ 0) : Set.Finite {i | w i = lam} := by
  have hball : w ⁻¹' Metric.ball (0 : ℝ) ‖lam‖ ∈ Filter.cofinite :=
    hw.tendsto_cofinite_zero (Metric.ball_mem_nhds 0 (norm_pos_iff.mpr hlam))
  refine Set.Finite.subset (Filter.mem_cofinite.mp hball) fun i hi => ?_
  simp only [Set.mem_setOf_eq] at hi
  simp [Set.mem_compl_iff, Set.mem_preimage, hi]

namespace ContinuousLinearMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {M : H →L[ℝ] H}

omit [CompleteSpace H] in
/-- The eigenvalues are read off the diagonal of an orthonormal eigenbasis. -/
theorem inner_eigen_self {ι : Type*} {e : HilbertBasis ι ℝ H} {w : ι → ℝ}
    (he : ∀ i, M (e i) = w i • e i) (i : ι) : ⟪M (e i), e i⟫ = w i := by
  rw [he i, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i, one_pow, mul_one]

/-- An eigenvector of a self-adjoint operator is orthogonal to the eigenspaces of the other
eigenvalues. -/
theorem inner_eigenspace_eq_zero (hM : IsSelfAdjoint M) {x : H} {μ lam : ℝ} (hx : M x = μ • x)
    (hne : μ ≠ lam) {y : H} (hy : y ∈ Module.End.eigenspace (M : H →ₗ[ℝ] H) lam) :
    ⟪y, x⟫ = 0 := by
  have hMy : M y = lam • y := Module.End.mem_eigenspace_iff.mp hy
  have h := hM.isSymmetric y x
  rw [show ((M : H →ₗ[ℝ] H) y) = M y from rfl, show ((M : H →ₗ[ℝ] H) x) = M x from rfl,
    hMy, hx, real_inner_smul_left, real_inner_smul_right] at h
  have hz : (lam - μ) * ⟪y, x⟫ = 0 := by linarith
  rcases mul_eq_zero.mp hz with h' | h'
  · exact absurd (sub_eq_zero.mp h').symm hne
  · exact h'

/-- The eigenspace of a continuous operator is a complete subspace. -/
theorem completeSpace_eigenspace (M : H →L[ℝ] H) (lam : ℝ) :
    CompleteSpace (Module.End.eigenspace (M : H →ₗ[ℝ] H) lam) := by
  have hker : Module.End.eigenspace (M : H →ₗ[ℝ] H) lam
      = LinearMap.ker ((M - lam • (1 : H →L[ℝ] H) : H →L[ℝ] H) : H →ₗ[ℝ] H) := by
    ext x
    simp [sub_eq_zero]
  rw [hker]
  exact (ContinuousLinearMap.isClosed_ker _).completeSpace_coe

omit [CompleteSpace H] in
/-- The orthogonal projection onto an eigenspace is positive. -/
theorem inner_starProjection_self_nonneg (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    0 ≤ ⟪K.starProjection x, x⟫ := by
  have hidem : K.starProjection (K.starProjection x) = K.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  have hsymm := K.starProjection_isSymmetric (K.starProjection x) x
  simp only [ContinuousLinearMap.coe_coe, hidem] at hsymm
  rw [hsymm, real_inner_self_eq_norm_sq]
  positivity

/-- The trace of the orthogonal projection onto the `lam`-eigenspace, computed along an
orthonormal eigenbasis, counts the indices whose eigenvalue is `lam`. -/
private theorem tsum_inner_starProjection_eigen (hM : IsSelfAdjoint M) {lam : ℝ}
    {ι : Type*} {e : HilbertBasis ι ℝ H} {w : ι → ℝ} (he : ∀ i, M (e i) = w i • e i)
    (hfin : Set.Finite {i | w i = lam}) :
    ∑' i, ENNReal.ofReal
        ⟪(Module.End.eigenspace (M : H →ₗ[ℝ] H) lam).starProjection (e i), e i⟫
      = ({i | w i = lam}.ncard : ℝ≥0∞) := by
  classical
  haveI := completeSpace_eigenspace M lam
  set K := Module.End.eigenspace (M : H →ₗ[ℝ] H) lam with hK
  have hterm : ∀ i, ENNReal.ofReal ⟪K.starProjection (e i), e i⟫
      = if w i = lam then (1 : ℝ≥0∞) else 0 := by
    intro i
    by_cases h : w i = lam
    · have hmem : e i ∈ K := Module.End.mem_eigenspace_iff.mpr (h ▸ he i)
      rw [if_pos h, Submodule.starProjection_eq_self_iff.mpr hmem, real_inner_self_eq_norm_sq,
        e.orthonormal.1 i]
      simp
    · have hperp : e i ∈ Kᗮ := (Submodule.mem_orthogonal K (e i)).mpr fun y hy =>
        inner_eigenspace_eq_zero hM (he i) h hy
      have hzero : K.starProjection (e i) = 0 := by
        have hmem : e i ∈ LinearMap.ker (K.starProjection : H →ₗ[ℝ] H) := by
          rw [Submodule.ker_starProjection K]
          exact hperp
        exact LinearMap.mem_ker.mp hmem
      rw [if_neg h, hzero]
      simp
  rw [tsum_congr hterm, tsum_eq_sum (s := hfin.toFinset) fun i hi => if_neg (by simpa using hi),
    Finset.sum_congr rfl fun i hi => if_pos (by simpa using hi),
    Set.ncard_eq_toFinset_card _ hfin]
  simp

/-- The eigenindices of a nonzero eigenvalue are in bijection for any two orthonormal
eigenbases of a positive self-adjoint operator with summable trace. -/
theorem nonempty_equiv_eigenIndex (hM : IsSelfAdjoint M) {ι κ : Type*} {e : HilbertBasis ι ℝ H}
    {w : ι → ℝ} {e' : HilbertBasis κ ℝ H} {w' : κ → ℝ}
    (he : ∀ i, M (e i) = w i • e i) (he' : ∀ j, M (e' j) = w' j • e' j) {lam : ℝ}
    (hfin : Set.Finite {i | w i = lam}) (hfin' : Set.Finite {j | w' j = lam}) :
    Nonempty ({i // w i = lam} ≃ {j // w' j = lam}) := by
  haveI := completeSpace_eigenspace M lam
  set K := Module.End.eigenspace (M : H →ₗ[ℝ] H) lam with hK
  have htrace := tsum_ofReal_inner_map_self_eq (isSelfAdjoint_starProjection K)
    (inner_starProjection_self_nonneg K) e e'
  rw [tsum_inner_starProjection_eigen hM he hfin,
    tsum_inner_starProjection_eigen hM he' hfin'] at htrace
  have hncard : {i | w i = lam}.ncard = {j | w' j = lam}.ncard := by exact_mod_cast htrace
  haveI hft : Fintype {i // w i = lam} := hfin.fintype
  haveI hft' : Fintype {j // w' j = lam} := hfin'.fintype
  refine ⟨Fintype.equivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact hncard

/-- **The Fredholm determinant does not depend on the orthonormal eigenbasis.**  For a positive
self-adjoint operator with summable trace, the product `∏ (1 + ⟪M e_i, e_i⟫)` along an
orthonormal basis of eigenvectors is the same for every such basis. -/
theorem tprod_one_add_inner_eigen_eq (hM : IsSelfAdjoint M) (hpos : ∀ x, 0 ≤ ⟪M x, x⟫)
    {ι κ : Type*} {e : HilbertBasis ι ℝ H} {w : ι → ℝ} {e' : HilbertBasis κ ℝ H} {w' : κ → ℝ}
    (he : ∀ i, M (e i) = w i • e i) (he' : ∀ j, M (e' j) = w' j • e' j)
    (hsum : Summable fun i => ⟪M (e i), e i⟫) :
    ∏' i, (1 + ⟪M (e i), e i⟫) = ∏' j, (1 + ⟪M (e' j), e' j⟫) := by
  classical
  have hw : ∀ i, ⟪M (e i), e i⟫ = w i := fun i => inner_eigen_self he i
  have hw' : ∀ j, ⟪M (e' j), e' j⟫ = w' j := fun j => inner_eigen_self he' j
  have hsumw : Summable w := by simpa only [hw] using hsum
  have hsumw' : Summable w' := by
    simpa only [hw'] using summable_inner_map_self_of_summable hM hpos e' hsum
  simp_rw [hw, hw']
  set f : ι → ℝ := fun i => 1 + w i with hf
  set g : κ → ℝ := fun j => 1 + w' j with hg
  have hmulf : ∀ x : ↥(Function.mulSupport f), w x ≠ 0 := by
    intro x
    have hx := Function.mem_mulSupport.mp x.2
    simpa [hf] using hx
  have hmulg : ∀ y : ↥(Function.mulSupport g), w' y ≠ 0 := by
    intro y
    have hy := Function.mem_mulSupport.mp y.2
    simpa [hg] using hy
  set φ : ↥(Function.mulSupport f) → ℝ := fun x => w x with hφ
  set φ' : ↥(Function.mulSupport g) → ℝ := fun y => w' y with hφ'
  have hfib : ∀ lam : ℝ, Nonempty ({x // φ x = lam} ≃ {y // φ' y = lam}) := by
    intro lam
    by_cases hlam : lam = 0
    · subst hlam
      haveI : IsEmpty {x : ↥(Function.mulSupport f) // φ x = 0} := ⟨fun x => hmulf x.1 x.2⟩
      haveI : IsEmpty {y : ↥(Function.mulSupport g) // φ' y = 0} := ⟨fun y => hmulg y.1 y.2⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
    · obtain ⟨eq⟩ := nonempty_equiv_eigenIndex hM he he'
        (hsumw.finite_setOf_eq_of_ne_zero hlam) (hsumw'.finite_setOf_eq_of_ne_zero hlam)
      refine ⟨((Equiv.subtypeSubtypeEquivSubtype ?_).trans eq).trans
        (Equiv.subtypeSubtypeEquivSubtype ?_).symm⟩
      · intro i hi
        simp [hf, hi, hlam]
      · intro j hj
        simp [hg, hj, hlam]
  let fib : ∀ lam : ℝ, {x // φ x = lam} ≃ {y // φ' y = lam} := fun lam => (hfib lam).some
  let ee : ↥(Function.mulSupport f) ≃ ↥(Function.mulSupport g) :=
    (Equiv.sigmaFiberEquiv φ).symm.trans
      ((Equiv.sigmaCongrRight fib).trans (Equiv.sigmaFiberEquiv φ'))
  refine Equiv.tprod_eq_tprod_of_mulSupport ee fun x => ?_
  have hx : φ' (ee x) = φ x := (fib (φ x) ⟨x, rfl⟩).2
  show 1 + w' ↑(ee x) = 1 + w ↑x
  exact congrArg (fun t => 1 + t) hx

end ContinuousLinearMap
