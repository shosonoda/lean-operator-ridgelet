import OperatorRidgelet.ToMathlib.TraceClassEigenbasis

/-!
# The trace of a positive operator does not depend on the Hilbert basis

For a positive self-adjoint operator `P` on a real Hilbert space the sum `∑ ⟪P e_i, e_i⟫` has
the same value along every Hilbert basis.  The proof does not use a square root of `P` (the
continuous functional calculus of Mathlib is not available for `H →L[ℝ] H`): if the sum
converges along one basis then `P` is compact
(`ContinuousLinearMap.isCompactOperator_of_summable_inner`), hence has an orthonormal basis of
eigenvectors, and `ContinuousLinearMap.tsum_ofReal_inner_map_eq_of_eigen` evaluates the sum
along *any* basis as the sum of the eigenvalues.

* `ContinuousLinearMap.exists_hilbertBasis_eigenvector_of_summable`: the orthonormal eigenbasis,
  without the injectivity hypothesis of
  `ContinuousLinearMap.exists_hilbertBasis_eigenvector` (the kernel contributes the eigenvalue
  `0`);
* `ContinuousLinearMap.tsum_ofReal_inner_map_self_eq`: basis independence as an identity in
  `ℝ≥0∞`, so that no summability hypothesis is needed;
* `ContinuousLinearMap.summable_inner_map_self_of_summable` and
  `ContinuousLinearMap.tsum_inner_map_self_eq`: the real-valued consequences.
-/

open scoped RealInnerProductSpace ENNReal

namespace ContinuousLinearMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A positive self-adjoint operator whose trace converges along some Hilbert basis has an
orthonormal basis of eigenvectors with nonnegative eigenvalues.  Unlike
`ContinuousLinearMap.exists_hilbertBasis_eigenvector` this does not assume that `P` is
injective: the kernel of `P` contributes the eigenvalue `0`. -/
theorem exists_hilbertBasis_eigenvector_of_summable {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι : Type*} (b : HilbertBasis ι ℝ H)
    (hsum : Summable fun i => ⟪P (b i), b i⟫) :
    ∃ (κ : Type u) (e : HilbertBasis κ ℝ H) (p : κ → ℝ),
      (∀ k, 0 ≤ p k) ∧ ∀ k, P (e k) = p k • e k := by
  classical
  have hsymm : (P : H →ₗ[ℝ] H).IsSymmetric := hP.isSymmetric
  have hcompact : IsCompactOperator P := isCompactOperator_of_summable_inner hsymm hpos b hsum
  set E : ℝ → Submodule ℝ H := fun μ => Module.End.eigenspace (P : H →ₗ[ℝ] H) μ with hEdef
  have hker : ∀ μ : ℝ, E μ = LinearMap.ker ((P - μ • (1 : H →L[ℝ] H) : H →L[ℝ] H) : H →ₗ[ℝ] H) := by
    intro μ
    ext x
    simp [hEdef, sub_eq_zero]
  haveI hcomplete : ∀ μ : ℝ, CompleteSpace (E μ) := by
    intro μ
    rw [hker μ]
    exact (ContinuousLinearMap.isClosed_ker _).completeSpace_coe
  choose W bW hbW using fun μ : ℝ => exists_hilbertBasis ℝ (E μ)
  set v : (Σ μ : ℝ, W μ) → H := fun a => ((bW a.1 a.2 : E a.1) : H) with hvdef
  have hv : Orthonormal ℝ v :=
    hsymm.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun μ => (bW μ).orthonormal
  have hmem : ∀ a : Σ μ : ℝ, W μ, v a ∈ E a.1 := fun a => (bW a.1 a.2).2
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm,
      ← Submodule.iInf_orthogonal]
    intro x hx
    have hv0 : ∀ a, ⟪v a, x⟫ = 0 := fun a =>
      (Submodule.mem_orthogonal _ x).mp hx (v a) (Submodule.subset_span (Set.mem_range_self a))
    refine Submodule.mem_iInf _ |>.mpr fun μ => (Submodule.mem_orthogonal _ x).mpr ?_
    intro y hy
    have h1 := ((bW μ).hasSum_repr ⟨y, hy⟩).mapL (E μ).subtypeL
    have h2 := h1.mapL (innerSL ℝ x)
    have h3 : (fun i => (innerSL ℝ x) ((E μ).subtypeL ((bW μ).repr ⟨y, hy⟩ i • bW μ i)))
        = fun _ => (0 : ℝ) := by
      funext i
      have := hv0 ⟨μ, i⟩
      simp only [hvdef] at this
      simp only [innerSL_apply_apply, Submodule.subtypeL_apply, Submodule.coe_smul,
        real_inner_smul_right]
      rw [real_inner_comm] at this
      rw [this, mul_zero]
    rw [h3] at h2
    have h4 : ⟪x, y⟫ = 0 := by
      have := hasSum_zero.unique h2
      simpa using this.symm
    rw [real_inner_comm] at h4
    exact h4
  refine ⟨Σ μ : ℝ, W μ, HilbertBasis.mkOfOrthogonalEqBot hv hsp, fun a => a.1, ?_, ?_⟩
  · intro a
    have hnorm : ‖v a‖ = 1 := hv.1 a
    have hP' : P (v a) = a.1 • v a := Module.End.mem_eigenspace_iff.mp (hmem a)
    have := hpos (v a)
    rw [hP', real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm] at this
    simpa using this
  · intro a
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact Module.End.mem_eigenspace_iff.mp (hmem a)

/-- The basis independence of the trace when the sum along the first basis is finite: then `P`
has an orthonormal eigenbasis and both sums are the sum of the eigenvalues. -/
private theorem tsum_ofReal_inner_map_self_eq_of_ne_top {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι κ : Type*} (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (hfin : (∑' i, ENNReal.ofReal ⟪P (b i), b i⟫) ≠ ∞) :
    ∑' i, ENNReal.ofReal ⟪P (b i), b i⟫ = ∑' k, ENNReal.ofReal ⟪P (c k), c k⟫ := by
  have hs : Summable fun i => ⟪P (b i), b i⟫ := by
    have h := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (hpos _)] using h
  obtain ⟨τ, e, p, hp, hPe⟩ := exists_hilbertBasis_eigenvector_of_summable hP hpos b hs
  rw [tsum_ofReal_inner_map_eq_of_eigen b e p hp hPe,
    tsum_ofReal_inner_map_eq_of_eigen c e p hp hPe]

/-- **The trace of a positive operator is basis independent.**  For a positive self-adjoint
operator the sum `∑ ⟪P e_i, e_i⟫`, taken in `ℝ≥0∞` so that no summability hypothesis is needed,
has the same value along every Hilbert basis. -/
theorem tsum_ofReal_inner_map_self_eq {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι κ : Type*} (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H) :
    ∑' i, ENNReal.ofReal ⟪P (b i), b i⟫ = ∑' k, ENNReal.ofReal ⟪P (c k), c k⟫ := by
  by_cases h : (∑' i, ENNReal.ofReal ⟪P (b i), b i⟫) = ∞
  · have hc : (∑' k, ENNReal.ofReal ⟪P (c k), c k⟫) = ∞ := by
      by_contra hne
      have hcb := tsum_ofReal_inner_map_self_eq_of_ne_top hP hpos c b hne
      rw [h] at hcb
      exact hne hcb
    rw [h, hc]
  · exact tsum_ofReal_inner_map_self_eq_of_ne_top hP hpos b c h

/-- If the trace of a positive operator converges along one Hilbert basis, it converges along
every Hilbert basis. -/
theorem summable_inner_map_self_of_summable {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι κ : Type*} {b : HilbertBasis ι ℝ H} (c : HilbertBasis κ ℝ H)
    (hsum : Summable fun i => ⟪P (b i), b i⟫) : Summable fun k => ⟪P (c k), c k⟫ := by
  have hb : (∑' i, ENNReal.ofReal ⟪P (b i), b i⟫) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hpos _) hsum]
    exact ENNReal.ofReal_ne_top
  have hc := (tsum_ofReal_inner_map_self_eq hP hpos b c) ▸ hb
  have h := ENNReal.summable_toReal hc
  simpa [ENNReal.toReal_ofReal (hpos _)] using h

/-- **The trace of a positive operator is basis independent**, as a real number: if the trace
converges along one Hilbert basis, the value `∑ ⟪P e_i, e_i⟫` is the same along every Hilbert
basis. -/
theorem tsum_inner_map_self_eq {P : H →L[ℝ] H} (hP : IsSelfAdjoint P) (hpos : ∀ x, 0 ≤ ⟪P x, x⟫)
    {ι κ : Type*} (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (hsum : Summable fun i => ⟪P (b i), b i⟫) :
    ∑' i, ⟪P (b i), b i⟫ = ∑' k, ⟪P (c k), c k⟫ := by
  have hsc := summable_inner_map_self_of_summable hP hpos c hsum
  have h := tsum_ofReal_inner_map_self_eq hP hpos b c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hpos _) hsum,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => hpos _) hsc] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun i => hpos _)
    (tsum_nonneg fun k => hpos _)).mp h

end ContinuousLinearMap
