import OperatorRidgelet.ToMathlib.TraceClassEigenbasis
import Mathlib.Topology.Bases

/-!
# An orthonormal eigenbasis of a compact self-adjoint operator, kernel included

`ContinuousLinearMap.exists_hilbertBasis_eigenvector` of
`OperatorRidgelet.ToMathlib.TraceClassEigenbasis` produces a countable orthonormal eigenbasis of
an *injective* positive operator with summable trace.  Without injectivity the kernel is a
possibly infinite-dimensional eigenspace for the eigenvalue `0`, which the construction through
the finite-dimensional eigenspaces misses.  Here the orthonormal family of eigenvectors with
nonzero eigenvalues is extended to a maximal orthonormal set instead
(`Orthonormal.exists_hilbertBasis_extension`): the additional vectors are orthogonal to every
eigenspace with a nonzero eigenvalue, hence lie in the kernel, so that *every* element of the
extension is an eigenvector.  On a separable space the resulting Hilbert basis is countable
(`Orthonormal.countable_of_separableSpace`), so it can be reindexed by a subtype of `ℕ`, which is
the form `HasSummableTrace` and `fredholmDet` require.
-/

open Filter Topology
open scoped RealInnerProductSpace

/-- An orthonormal set in a separable inner product space is countable: the open balls of radius
`1/2` around its points are pairwise disjoint. -/
theorem Orthonormal.countable_of_separableSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [TopologicalSpace.SeparableSpace H] {s : Set H}
    (hs : Orthonormal ℝ ((↑) : s → H)) : s.Countable := by
  have hd : s.PairwiseDisjoint fun y : H => Metric.ball y (1 / 2) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hzx hzy => ?_
    have hxn : ‖x‖ = 1 := hs.1 ⟨x, hx⟩
    have hyn : ‖y‖ = 1 := hs.1 ⟨y, hy⟩
    have hne : (⟨x, hx⟩ : s) ≠ ⟨y, hy⟩ := by
      simpa [Subtype.ext_iff] using hxy
    have hxy0 : ⟪x, y⟫ = 0 := hs.2 hne
    have hsq : ‖x - y‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hxn, hyn, hxy0]
      norm_num
    have h1 : dist x z < 1 / 2 := by
      rw [dist_comm]; exact Metric.mem_ball.1 hzx
    have h2 : dist z y < 1 / 2 := Metric.mem_ball.1 hzy
    have h3 : dist x y < 1 := lt_of_le_of_lt (dist_triangle x z y) (by linarith)
    rw [dist_eq_norm] at h3
    nlinarith [norm_nonneg (x - y)]
  exact hd.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    fun i _ => ⟨i, Metric.mem_ball_self (by norm_num)⟩

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Spectral theorem for compact self-adjoint operators.**  A compact self-adjoint operator on a
separable real Hilbert space has a countable orthonormal basis of eigenvectors, the eigenvalue at
`e k` being `⟪P (e k), e k⟫`.  Unlike `exists_hilbertBasis_eigenvector` this does not assume
injectivity, so the eigenvalue `0` may occur. -/
theorem exists_hilbertBasis_eigenvector_of_isCompactOperator
    [TopologicalSpace.SeparableSpace H] {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hcompact : IsCompactOperator P) :
    ∃ (κ : Type) (_ : Countable κ) (e : HilbertBasis κ ℝ H),
      ∀ k, P (e k) = ⟪P (e k), e k⟫ • e k := by
  classical
  have hsymm : (P : H →ₗ[ℝ] H).IsSymmetric := hP.isSymmetric
  set E : ℝ → Submodule ℝ H := fun μ => Module.End.eigenspace (P : H →ₗ[ℝ] H) μ with hE
  haveI hfin : ∀ μ : {μ : ℝ // μ ≠ 0}, FiniteDimensional ℝ (E μ.1) := fun μ =>
    ContinuousLinearMap.finite_dimensional_eigenspace hcompact μ.1 μ.2
  -- the orthonormal family of eigenvectors with nonzero eigenvalues
  set v : (Σ μ : {μ : ℝ // μ ≠ 0}, Fin (Module.finrank ℝ (E μ.1))) → H :=
    fun a => (stdOrthonormalBasis ℝ (E a.1.1) a.2 : H) with hvdef
  have hv : Orthonormal ℝ v :=
    (hsymm.orthogonalFamily_eigenspaces.comp
      (Subtype.coe_injective (p := fun μ : ℝ => μ ≠ 0))).orthonormal_sigma_orthonormal
      fun μ => (stdOrthonormalBasis ℝ (E μ.1)).orthonormal
  -- each eigenspace with a nonzero eigenvalue is spanned by the family
  have hspanle : ∀ μ : {μ : ℝ // μ ≠ 0}, E μ.1 ≤ Submodule.span ℝ (Set.range v) := by
    intro μ
    have hsub : (Set.range fun k : Fin (Module.finrank ℝ (E μ.1)) =>
        (stdOrthonormalBasis ℝ (E μ.1) k : H)) ⊆ Set.range v := by
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨μ, k⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (Submodule.span_mono hsub)
    have himg : (Set.range fun k : Fin (Module.finrank ℝ (E μ.1)) =>
        (stdOrthonormalBasis ℝ (E μ.1) k : H)) =
        (E μ.1).subtype '' Set.range (stdOrthonormalBasis ℝ (E μ.1)) := by
      rw [← Set.range_comp]
      rfl
    rw [himg, Submodule.span_image, ← (stdOrthonormalBasis ℝ (E μ.1)).coe_toBasis,
      (stdOrthonormalBasis ℝ (E μ.1)).toBasis.span_eq, Submodule.map_subtype_top]
  -- the eigenvalue `0` eigenspace is the kernel, a complete subspace
  have hE0 : E 0 = LinearMap.ker (P : H →ₗ[ℝ] H) := Module.End.eigenspace_zero _
  haveI : CompleteSpace (E 0) := by
    rw [hE0]
    exact (P.isClosed_ker).completeSpace_coe
  -- a vector orthogonal to the family lies in the kernel
  have hker : ∀ y : H, (∀ a, ⟪v a, y⟫ = 0) → P y = 0 := by
    intro y hy
    have hyspan : ∀ u ∈ Submodule.span ℝ (Set.range v), ⟪u, y⟫ = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hy a
      | zero => simp
      | add x z _ _ hx hz => rw [inner_add_left, hx, hz, add_zero]
      | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
    set A : Submodule ℝ H := ⨆ μ : {μ : ℝ // μ ≠ 0}, E μ.1 with hA
    have hyA : y ∈ Aᗮ :=
      (Submodule.mem_orthogonal _ _).2 fun u hu => hyspan u (iSup_le hspanle hu)
    have hE0A : E 0 ≤ Aᗮ := by
      rw [hA, ← Submodule.iInf_orthogonal]
      refine le_iInf fun μ => ?_
      intro x hx
      exact (Submodule.mem_orthogonal _ _).2 fun u hu =>
        hsymm.orthogonalFamily_eigenspaces μ.2 ⟨u, hu⟩ ⟨x, hx⟩
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := (E 0).exists_add_mem_mem_orthogonal y
    have hy₁A : y₁ ∈ Aᗮ := by
      have h := Submodule.sub_mem Aᗮ hyA (hE0A hy₀)
      simpa using h
    have hle : (⨆ μ : ℝ, E μ) ≤ E 0 ⊔ A := by
      refine iSup_le fun μ => ?_
      by_cases hμ : μ = 0
      · rw [hμ]; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun ν : {ν : ℝ // ν ≠ 0} => E ν.1) ⟨μ, hμ⟩)
    have hy₁bot : y₁ = 0 := by
      have hmem : y₁ ∈ (⨆ μ : ℝ, E μ)ᗮ := by
        refine Submodule.orthogonal_le hle ?_
        rw [← Submodule.inf_orthogonal]
        exact ⟨hy₁, hy₁A⟩
      rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm] at hmem
      simpa using hmem
    have hPy₀ : P y₀ = 0 := by
      rw [hE0] at hy₀
      exact hy₀
    rw [map_add, hPy₀, hy₁bot, map_zero, add_zero]
  -- extend the family to a Hilbert basis; every element of the extension is an eigenvector
  obtain ⟨w, b, hsubw, hbcoe⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  have hwortho : Orthonormal ℝ ((↑) : w → H) := hbcoe ▸ b.orthonormal
  have heig : ∀ y ∈ w, P y = ⟪P y, y⟫ • y := by
    intro y hy
    by_cases hyr : y ∈ Set.range v
    · obtain ⟨a, rfl⟩ := hyr
      have h1 : P (v a) = a.1.1 • v a :=
        Module.End.mem_eigenspace_iff.mp (stdOrthonormalBasis ℝ (E a.1.1) a.2).2
      have h2 : ⟪P (v a), v a⟫ = a.1.1 := by
        rw [h1, real_inner_smul_left, real_inner_self_eq_norm_sq, hv.1 a, one_pow, mul_one]
      rw [h2]
      exact h1
    · have h0 : P y = 0 := by
        refine hker y fun a => ?_
        have hva : v a ∈ w := hsubw ⟨a, rfl⟩
        have hne : (⟨v a, hva⟩ : w) ≠ ⟨y, hy⟩ := by
          simp only [ne_eq, Subtype.mk.injEq]
          intro h
          exact hyr ⟨a, h⟩
        exact hwortho.2 hne
      rw [h0, inner_zero_left, zero_smul]
  -- reindex the basis by a countable type in `Type`
  have hwc : w.Countable := hwortho.countable_of_separableSpace
  haveI : Countable w := hwc.to_subtype
  have key : ∀ κ : Type, Countable κ → (κ ≃ w) →
      ∃ (κ' : Type) (_ : Countable κ') (e : HilbertBasis κ' ℝ H),
        ∀ k, P (e k) = ⟪P (e k), e k⟫ • e k := by
    intro κ hκ eqv
    set e : κ → H := fun k => ((eqv k : w) : H) with hedef
    have heortho : Orthonormal ℝ e := hwortho.comp _ eqv.injective
    have herange : Set.range e = w := by
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        exact (eqv k).2
      · intro hz
        exact ⟨eqv.symm ⟨z, hz⟩, by simp [hedef]⟩
    have hbot : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      have h0 : ∀ i : w, ⟪(b i : H), y⟫ = 0 := by
        intro i
        refine (Submodule.mem_orthogonal _ _).1 hy _ (Submodule.subset_span ?_)
        rw [herange, hbcoe]
        exact i.2
      have hzero : b.repr y = 0 := by
        ext i
        rw [b.repr_apply_apply, h0 i]
        simp
      exact b.repr.injective (by rw [hzero, map_zero] : b.repr y = b.repr 0)
    refine ⟨κ, hκ, HilbertBasis.mkOfOrthogonalEqBot heortho hbot, fun k => ?_⟩
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact heig (e k) (herange ▸ Set.mem_range_self k)
  obtain ⟨f, hf⟩ := exists_injective_nat w
  exact key (Set.range f) inferInstance (Equiv.ofInjective f hf).symm

end ContinuousLinearMap
