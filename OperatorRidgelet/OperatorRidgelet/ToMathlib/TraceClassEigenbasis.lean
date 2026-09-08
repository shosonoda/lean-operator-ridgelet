import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Eigenbasis of a positive operator with summable trace

Let `P` be a positive self-adjoint operator on a real Hilbert space `H` whose trace
`∑ ⟪P e_i, e_i⟫` converges along some Hilbert basis `e`.  Then

* `ContinuousLinearMap.isCompactOperator_of_summable_inner`: `P` is a compact operator (it is
  the operator-norm limit of the finite-rank operators `x ↦ ∑_{i ∈ F} ⟪e_i, x⟫ P e_i`, with
  `‖P - P_F‖² ≤ ‖P‖ ∑_{i ∉ F} ⟪P e_i, e_i⟫`);
* `ContinuousLinearMap.exists_hilbertBasis_eigenvector`: if moreover `P` is injective, `H` has a
  countable Hilbert basis of eigenvectors of `P` with positive summable eigenvalues (the spectral
  theorem for compact self-adjoint operators, together with the basis independence of the trace
  of a positive operator).

The intermediate inequalities are the Cauchy–Schwarz inequality for the positive form
`(x, y) ↦ ⟪P x, y⟫` (`inner_map_mul_le`) and `‖P x‖² ≤ ‖P‖ ⟪P x, x⟫` (`norm_map_sq_le`).
-/

open Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cauchy–Schwarz for the positive form of a symmetric positive operator:
`⟪P x, y⟫² ≤ ⟪P x, x⟫ ⟪P y, y⟫`. -/
theorem inner_map_mul_le {P : H →L[ℝ] H} (hP : (P : H →ₗ[ℝ] H).IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) (x y : H) :
    ⟪P x, y⟫ ^ 2 ≤ ⟪P x, x⟫ * ⟪P y, y⟫ := by
  have key : ∀ t : ℝ, 0 ≤ ⟪P y, y⟫ * (t * t) + (2 * ⟪P x, y⟫) * t + ⟪P x, x⟫ := by
    intro t
    have h0 := hpos (x + t • y)
    have h1 : ⟪P y, x⟫ = ⟪P x, y⟫ := by
      rw [show ⟪P y, x⟫ = ⟪(P : H →ₗ[ℝ] H) y, x⟫ from rfl, hP y x]
      exact real_inner_comm _ _
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      h1] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-- For a symmetric positive operator, `‖P x‖² ≤ ‖P‖ ⟪P x, x⟫`. -/
theorem norm_map_sq_le {P : H →L[ℝ] H} (hP : (P : H →ₗ[ℝ] H).IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) (x : H) : ‖P x‖ ^ 2 ≤ ‖P‖ * ⟪P x, x⟫ := by
  have h1 := inner_map_mul_le hP hpos x (P x)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : ⟪P (P x), P x⟫ ≤ ‖P‖ * ‖P x‖ ^ 2 := by
    calc ⟪P (P x), P x⟫ ≤ ‖P (P x)‖ * ‖P x‖ := real_inner_le_norm _ _
      _ ≤ ‖P‖ * ‖P x‖ * ‖P x‖ := by gcongr; exact P.le_opNorm _
      _ = ‖P‖ * ‖P x‖ ^ 2 := by ring
  by_cases hx : ‖P x‖ = 0
  · rw [hx]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (norm_nonneg _) (hpos x)
  · have hpos' : 0 < ‖P x‖ ^ 2 := by positivity
    have h3 : ‖P x‖ ^ 2 * ‖P x‖ ^ 2 ≤ (‖P‖ * ⟪P x, x⟫) * ‖P x‖ ^ 2 := by
      nlinarith [hpos x, h1, h2]
    exact le_of_mul_le_mul_right h3 hpos'

/-- The form of a symmetric operator is symmetric: `⟪P u, v⟫ = ⟪P v, u⟫`. -/
theorem inner_map_comm {P : H →L[ℝ] H} (hP : (P : H →ₗ[ℝ] H).IsSymmetric) (u v : H) :
    ⟪P u, v⟫ = ⟪P v, u⟫ := by
  rw [show ⟪P u, v⟫ = ⟪(P : H →ₗ[ℝ] H) u, v⟫ from rfl, hP u v]
  exact real_inner_comm _ _

/-- The quadratic form of a symmetric positive operator on a finite combination of orthonormal
vectors is controlled by the coefficients and the diagonal values `⟪P b_i, b_i⟫`. -/
theorem inner_map_sum_smul_le {P : H →L[ℝ] H} (hP : (P : H →ₗ[ℝ] H).IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι : Type*} {b : ι → H} (c : ι → ℝ) (G : Finset ι) :
    ⟪P (∑ i ∈ G, c i • b i), ∑ i ∈ G, c i • b i⟫ ≤
      (∑ i ∈ G, c i ^ 2) * ∑ i ∈ G, ⟪P (b i), b i⟫ := by
  have hterm : ∀ i j, c i * c j * ⟪P (b i), b j⟫ ≤
      (|c i| * √⟪P (b i), b i⟫) * (|c j| * √⟪P (b j), b j⟫) := by
    intro i j
    have h1 : |⟪P (b i), b j⟫| ≤ √⟪P (b i), b i⟫ * √⟪P (b j), b j⟫ := by
      rw [← Real.sqrt_mul (hpos _)]
      exact Real.abs_le_sqrt (inner_map_mul_le hP hpos _ _)
    calc c i * c j * ⟪P (b i), b j⟫ ≤ |c i * c j * ⟪P (b i), b j⟫| := le_abs_self _
      _ = |c i| * |c j| * |⟪P (b i), b j⟫| := by rw [abs_mul, abs_mul]
      _ ≤ |c i| * |c j| * (√⟪P (b i), b i⟫ * √⟪P (b j), b j⟫) := by
          gcongr
      _ = (|c i| * √⟪P (b i), b i⟫) * (|c j| * √⟪P (b j), b j⟫) := by ring
  calc ⟪P (∑ i ∈ G, c i • b i), ∑ i ∈ G, c i • b i⟫
      = ∑ i ∈ G, ∑ j ∈ G, c i * c j * ⟪P (b i), b j⟫ := by
        simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
          real_inner_smul_right]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [inner_map_comm hP (b j) (b i)]
        ring
    _ ≤ ∑ i ∈ G, ∑ j ∈ G, (|c i| * √⟪P (b i), b i⟫) * (|c j| * √⟪P (b j), b j⟫) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i ∈ G, |c i| * √⟪P (b i), b i⟫) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
    _ ≤ (∑ i ∈ G, |c i| ^ 2) * ∑ i ∈ G, (√⟪P (b i), b i⟫) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i ∈ G, c i ^ 2) * ∑ i ∈ G, ⟪P (b i), b i⟫ := by
        congr 1
        · exact Finset.sum_congr rfl fun i _ => sq_abs _
        · exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hpos _)

/-- The tail of the quadratic form: for `z = x - ∑_{i ∈ F} ⟪b_i, x⟫ b_i`,
`⟪P z, z⟫ ≤ ‖x‖² ∑_{i ∉ F} ⟪P b_i, b_i⟫`. -/
theorem inner_map_sub_sum_le {P : H →L[ℝ] H} (hP : (P : H →ₗ[ℝ] H).IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι : Type*} (b : HilbertBasis ι ℝ H)
    (hsum : Summable fun i => ⟪P (b i), b i⟫) (F : Finset ι) (x : H) :
    ⟪P (x - ∑ i ∈ F, ⟪b i, x⟫ • b i), x - ∑ i ∈ F, ⟪b i, x⟫ • b i⟫ ≤
      ‖x‖ ^ 2 * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫ := by
  set z := x - ∑ i ∈ F, ⟪b i, x⟫ • b i with hz
  have hHasSum : HasSum (fun i : {i // i ∉ F} => ⟪b i, x⟫ • b i) z := by
    refine (Finset.hasSum_compl_iff (f := fun i => ⟪b i, x⟫ • b i) F).mpr ?_
    rw [hz, sub_add_cancel]
    simpa only [b.repr_apply_apply] using b.hasSum_repr x
  have hcont : Continuous fun w : H => ⟪P w, w⟫ := by fun_prop
  have hlim : Tendsto (fun G : Finset {i // i ∉ F} =>
      ⟪P (∑ i ∈ G, ⟪b i, x⟫ • b i), ∑ i ∈ G, ⟪b i, x⟫ • b i⟫) atTop (𝓝 ⟪P z, z⟫) :=
    (hcont.tendsto z).comp hHasSum
  refine le_of_tendsto' hlim fun G => ?_
  have hsub : Summable fun i : {i // i ∉ F} => ⟪P (b i), b i⟫ := hsum.subtype _
  set G' : Finset ι := G.map (Function.Embedding.subtype _) with hG'
  have h1 : ∑ i ∈ G, ⟪b i, x⟫ • b i = ∑ i ∈ G', ⟪b i, x⟫ • b i := by
    rw [hG', Finset.sum_map]
    rfl
  rw [h1]
  calc ⟪P (∑ i ∈ G', ⟪b i, x⟫ • b i), ∑ i ∈ G', ⟪b i, x⟫ • b i⟫
      ≤ (∑ i ∈ G', ⟪b i, x⟫ ^ 2) * ∑ i ∈ G', ⟪P (b i), b i⟫ :=
        inner_map_sum_smul_le hP hpos _ _
    _ ≤ ‖x‖ ^ 2 * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫ := by
        gcongr
        · exact Finset.sum_nonneg fun i _ => hpos _
        · have := b.orthonormal.sum_inner_products_le (s := G') x
          simpa only [Real.norm_eq_abs, sq_abs] using this
        · rw [hG', Finset.sum_map]
          exact hsub.sum_le_tsum G (fun i _ => hpos _)

/-- A positive self-adjoint operator whose trace `∑ ⟪P e_i, e_i⟫` converges along a Hilbert
basis is a compact operator. -/
theorem isCompactOperator_of_summable_inner [CompleteSpace H] {P : H →L[ℝ] H}
    (hP : (P : H →ₗ[ℝ] H).IsSymmetric) (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) {ι : Type*}
    (b : HilbertBasis ι ℝ H) (hsum : Summable fun i => ⟪P (b i), b i⟫) :
    IsCompactOperator P := by
  -- the finite-rank approximants `x ↦ ∑_{i ∈ F} ⟪b_i, x⟫ P b_i`
  let S : Finset ι → H →L[ℝ] H := fun F => ∑ i ∈ F, (innerSL ℝ (b i)).smulRight (P (b i))
  have hS_apply : ∀ F x, S F x = P (∑ i ∈ F, ⟪b i, x⟫ • b i) := by
    intro F x
    simp only [S, _root_.sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_sum, map_smul]
  have hS_compact : ∀ F, IsCompactOperator (S F) := by
    intro F
    have hcoe : ⇑(S F) = ∑ i ∈ F, ⇑((innerSL ℝ (b i)).smulRight (P (b i))) := by
      funext x
      rw [Finset.sum_apply]
      exact _root_.sum_apply _ _ _
    rw [hcoe]
    refine Finset.sum_induction _ IsCompactOperator (fun f g hf hg => hf.add hg)
      isCompactOperator_zero fun i _ => ?_
    have h1 : IsCompactOperator (innerSL ℝ (b i)) :=
      isCompactOperator_of_locallyCompactSpace_dom _
    have h2 := h1.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (P (b i)))
    have h3 : ⇑((innerSL ℝ (b i)).smulRight (P (b i))) =
        ⇑((ContinuousLinearMap.id ℝ ℝ).smulRight (P (b i))) ∘ ⇑(innerSL ℝ (b i)) := by
      funext x
      simp only [ContinuousLinearMap.smulRight_apply, Function.comp_apply,
        ContinuousLinearMap.id_apply]
    rw [h3]
    exact h2
  -- the norm estimate
  have hbound : ∀ F, ‖S F - P‖ ≤ √(‖P‖ * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫) := by
    intro F
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    rw [_root_.sub_apply, hS_apply, ← map_sub, ← norm_neg, ← map_neg, neg_sub]
    set z := x - ∑ i ∈ F, ⟪b i, x⟫ • b i
    have h1 : ‖P z‖ ^ 2 ≤ ‖P‖ * (‖x‖ ^ 2 * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫) :=
      (norm_map_sq_le hP hpos z).trans
        (mul_le_mul_of_nonneg_left (inner_map_sub_sum_le hP hpos b hsum F x) (norm_nonneg _))
    have h2 : ‖P z‖ ≤ √(‖P‖ * (‖x‖ ^ 2 * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫)) :=
      Real.le_sqrt_of_sq_le h1
    refine h2.trans (le_of_eq ?_)
    have htail : 0 ≤ ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫ := tsum_nonneg fun i => hpos _
    rw [show ‖P‖ * (‖x‖ ^ 2 * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫) =
        (‖P‖ * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫) * ‖x‖ ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg (norm_nonneg _) htail), Real.sqrt_sq (norm_nonneg _)]
  have htail : Tendsto (fun F : Finset ι => ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫) atTop
      (𝓝 0) := tendsto_tsum_compl_atTop_zero fun i => ⟪P (b i), b i⟫
  have hlim : Tendsto S atTop (𝓝 P) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun F => norm_nonneg _) hbound ?_
    have : Tendsto (fun F : Finset ι => √(‖P‖ * ∑' i : {i // i ∉ F}, ⟪P (b i), b i⟫)) atTop
        (𝓝 (√(‖P‖ * 0))) :=
      (Real.continuous_sqrt.tendsto _).comp (htail.const_mul _)
    simpa using this
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall hS_compact)

/-- The eigen-expansion of the diagonal values: `⟪P x, x⟫ = ∑ p_k ⟪e_k, x⟫²` for a Hilbert
basis `e` of eigenvectors of `P` with eigenvalues `p`. -/
theorem hasSum_inner_map_self_of_eigen {P : H →L[ℝ] H} {κ : Type*} (e : HilbertBasis κ ℝ H)
    (p : κ → ℝ) (hPe : ∀ k, P (e k) = p k • e k) (x : H) :
    HasSum (fun k => p k * ⟪e k, x⟫ ^ 2) ⟪P x, x⟫ := by
  have h1 := (e.hasSum_repr x).mapL P
  have h2 := h1.mapL (innerSL ℝ x)
  have h3 : (fun k => (innerSL ℝ x) (P (e.repr x k • e k))) = fun k => p k * ⟪e k, x⟫ ^ 2 := by
    funext k
    rw [innerSL_apply_apply, map_smul, hPe, e.repr_apply_apply, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm]
    ring
  rw [h3, innerSL_apply_apply] at h2
  rw [← real_inner_comm (P x) x]
  exact h2

/-- The trace of a positive operator is basis independent: along a Hilbert basis `e` of
eigenvectors with eigenvalues `p`, the sum `∑ ⟪P b_i, b_i⟫` along any Hilbert basis `b` equals
`∑ p_k`, as an identity in `ℝ≥0∞`. -/
theorem tsum_ofReal_inner_map_eq_of_eigen {P : H →L[ℝ] H}
    {ι κ : Type*} (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ H) (p : κ → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hPe : ∀ k, P (e k) = p k • e k) :
    ∑' i, ENNReal.ofReal ⟪P (b i), b i⟫ = ∑' k, ENNReal.ofReal (p k) := by
  have h1 : ∀ i, ENNReal.ofReal ⟪P (b i), b i⟫ =
      ∑' k, ENNReal.ofReal (p k) * ENNReal.ofReal (⟪e k, b i⟫ ^ 2) := by
    intro i
    have h := hasSum_inner_map_self_of_eigen e p hPe (b i)
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hp k) (sq_nonneg _))
      h.summable]
    exact tsum_congr fun k => ENNReal.ofReal_mul (hp k)
  have h2 : ∀ k, ∑' i, ENNReal.ofReal (⟪e k, b i⟫ ^ 2) = 1 := by
    intro k
    have h := b.hasSum_inner_mul_inner (e k) (e k)
    rw [real_inner_self_eq_norm_sq, e.orthonormal.1 k, one_pow] at h
    have h' : HasSum (fun i => ⟪e k, b i⟫ ^ 2) 1 := by
      have hfun : (fun i => ⟪e k, b i⟫ * ⟪b i, e k⟫) = fun i => ⟪e k, b i⟫ ^ 2 := by
        funext i
        rw [← real_inner_comm (b i) (e k), sq]
      rw [hfun] at h
      exact h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h'.summable, h'.tsum_eq,
      ENNReal.ofReal_one]
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [ENNReal.tsum_mul_left, h2 k, mul_one]

/-- **Spectral theorem for positive operators with summable trace.**  An injective, positive,
self-adjoint operator `P` whose trace converges along some Hilbert basis has a countable Hilbert
basis of eigenvectors with positive, summable eigenvalues. -/
theorem exists_hilbertBasis_eigenvector [CompleteSpace H] {P : H →L[ℝ] H} (hP : IsSelfAdjoint P)
    (hpos : ∀ x, 0 ≤ ⟪P x, x⟫) (hinj : Function.Injective P) {ι : Type*}
    (b : HilbertBasis ι ℝ H) (hsum : Summable fun i => ⟪P (b i), b i⟫) :
    ∃ (κ : Type) (_ : Countable κ) (e : HilbertBasis κ ℝ H) (p : κ → ℝ),
      (∀ k, 0 < p k) ∧ Summable p ∧ ∀ k, P (e k) = p k • e k := by
  have hsymm : (P : H →ₗ[ℝ] H).IsSymmetric := hP.isSymmetric
  have hcompact : IsCompactOperator P := isCompactOperator_of_summable_inner hsymm hpos b hsum
  set E : ℝ → Submodule ℝ H := fun μ => Module.End.eigenspace (P : H →ₗ[ℝ] H) μ with hE
  have hE0 : E 0 = ⊥ := by
    rw [hE]
    simp only
    rw [Module.End.eigenspace_zero, LinearMap.ker_eq_bot]
    exact hinj
  haveI hfin : ∀ μ, FiniteDimensional ℝ (E μ) := by
    intro μ
    by_cases hμ : μ = 0
    · rw [hμ, hE0]
      infer_instance
    · exact ContinuousLinearMap.finite_dimensional_eigenspace hcompact μ hμ
  -- the orthonormal family of eigenvectors, indexed by eigenvalue and basis index
  let κ : Type := Σ μ : ℝ, Fin (Module.finrank ℝ (E μ))
  let v : κ → H := fun a => (stdOrthonormalBasis ℝ (E a.1) a.2 : H)
  have hv : Orthonormal ℝ v :=
    hsymm.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      fun μ => (stdOrthonormalBasis ℝ (E μ)).orthonormal
  have hspan : Submodule.span ℝ (Set.range v) = ⨆ μ, E μ := by
    have hrange : Set.range v =
        ⋃ μ, Set.range fun k : Fin (Module.finrank ℝ (E μ)) =>
          (stdOrthonormalBasis ℝ (E μ) k : H) :=
      Set.range_sigma_eq_iUnion_range _
    rw [hrange, Submodule.span_iUnion]
    refine iSup_congr fun μ => ?_
    have : (Set.range fun k : Fin (Module.finrank ℝ (E μ)) =>
        (stdOrthonormalBasis ℝ (E μ) k : H)) =
        (E μ).subtype '' Set.range (stdOrthonormalBasis ℝ (E μ)) := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, ← (stdOrthonormalBasis ℝ (E μ)).coe_toBasis,
      (stdOrthonormalBasis ℝ (E μ)).toBasis.span_eq, Submodule.map_subtype_top]
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [hspan]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm
  let e : HilbertBasis κ ℝ H := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  have he : ⇑e = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp
  let p : κ → ℝ := fun a => a.1
  have hPe : ∀ a, P (e a) = p a • e a := by
    intro a
    rw [he]
    have hmem : v a ∈ E a.1 := (stdOrthonormalBasis ℝ (E a.1) a.2).2
    exact Module.End.mem_eigenspace_iff.mp hmem
  have hp_pos : ∀ a, 0 < p a := by
    intro a
    have hne : e a ≠ 0 := by
      rw [he]
      exact hv.ne_zero a
    have hinner : ⟪P (e a), e a⟫ = p a := by
      rw [hPe, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 a, one_pow,
        mul_one]
    rcases (hpos (e a)).lt_or_eq with h | h
    · rwa [hinner] at h
    · exfalso
      apply hne
      apply hinj
      rw [map_zero, hPe, ← hinner, ← h, zero_smul]
  have hp_nonneg : ∀ a, 0 ≤ p a := fun a => (hp_pos a).le
  -- the trace along `e` is the trace along `b`
  have htrace : ∑' a, ENNReal.ofReal (p a) ≠ ∞ := by
    rw [← tsum_ofReal_inner_map_eq_of_eigen b e p hp_nonneg hPe,
      ← ENNReal.ofReal_tsum_of_nonneg (fun i => hpos _) hsum]
    exact ENNReal.ofReal_ne_top
  have hcount : Countable κ := by
    have h := Summable.countable_support_ennreal htrace
    have hsupp : Function.support (fun a => ENNReal.ofReal (p a)) = Set.univ := by
      ext a
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_univ,
        iff_true]
      exact hp_pos a
    rw [hsupp] at h
    exact Set.countable_univ_iff.mp h
  have hsummable : Summable p := by
    have h := ENNReal.summable_toReal htrace
    refine h.congr fun a => ?_
    exact ENNReal.toReal_ofReal (hp_nonneg a)
  exact ⟨κ, hcount, e, p, hp_pos, hsummable, hPe⟩

end ContinuousLinearMap
