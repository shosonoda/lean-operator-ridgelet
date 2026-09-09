import OperatorRidgelet.Sampling.Spectral
import OperatorRidgelet.Reconstruction.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Constructive universal approximation

The material behind Theorem `thm:D`.  Two independent ingredients are proved here.

*Step 1 (Stone--Weierstrass).*  The characters `χ_ξ(x) = e^{i⟪x,ξ⟫}`, restricted to a compact
`K ⊆ H`, span a self-conjugate subalgebra of `C(K;ℂ)`: they are closed under multiplication
(`charOn_mul`), under conjugation (`star_charOn`), and contain the constants, and they separate
the points of `K` because `ξ = π‖x - x'‖^{-2}(x - x')` gives `χ_ξ(x) = -χ_ξ(x')`.  The
`RCLike` Stone--Weierstrass theorem therefore makes their span dense, which is
`exists_character_approx`: every continuous `f` is uniformly approximated on `K` by a finite
combination `∑_j w_j χ_{ξ_j}`.

*Step 2 (characters have spectral densities).*  For a direction measure `ν` with full support
that is finite on bounded sets, the normalized radial bump
`G_{ξ₀,δ}(ξ) = φ(‖ξ - ξ₀‖²/δ²)/Z` of `bumpDensity` has `∫ G dν = 1` and vanishes outside the
ball of radius `δ` around `ξ₀`, so `|χ_{ξ₀}(x) - g_{G_{ξ₀,δ}}(x)| ≤ ‖x‖δ` by the 1-Lipschitz
bound `‖e^{iu} - e^{iv}‖ ≤ |u - v|` (`norm_exp_ofReal_mul_I_sub_exp_ofReal_mul_I_le`); it is
regular along rays by `isRegularAlongRays_radialBump`.

Combining the two steps, `exists_isRegularAlongRays_norm_sub_spectralTarget_le` produces, for
every continuous `f`, compact `K` and `ε > 0`, a density `G` that is smooth, vanishes outside a
bounded set, is regular along rays, and satisfies `‖f - g_G‖ ≤ ε` on `K`.  Feeding it to
Theorem `thm:A`(iii) and to the moment bounds of Theorem `thm:E` gives Theorem `thm:D` for a
direction measure that is finite on bounded sets.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Complex Filter Topology Metric

open scoped ENNReal NNReal RealInnerProductSpace Pointwise BoundedContinuousFunction

/-! ### The characters of a compact set -/

section Characters

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The circle map `t ↦ e^{it}` is 1-Lipschitz. -/
theorem lipschitzWith_exp_ofReal_mul_I :
    LipschitzWith 1 fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)) t := fun t =>
    HasDerivAt.cexp (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I)
  refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt) fun t => ?_
  have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul, Complex.norm_I]
  have hdt : ‖deriv (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) t‖ = 1 := by
    rw [(hd t).deriv, hnorm]
  simp [← NNReal.coe_le_coe, coe_nnnorm, hdt]

/-- `‖e^{iu} - e^{iv}‖ ≤ |u - v|`. -/
theorem norm_exp_ofReal_mul_I_sub_exp_ofReal_mul_I_le (u v : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ ≤ |u - v| := by
  have h := lipschitzWith_exp_ofReal_mul_I.dist_le_mul u v
  rwa [dist_eq_norm, Real.dist_eq, NNReal.coe_one, one_mul] at h

/-- The character `χ_ξ(x) = e^{i⟪x,ξ⟫}` restricted to `K`, as a continuous function on `K`. -/
def charOn (K : Set H) (ξ : H) : C(K, ℂ) :=
  ⟨fun x => Complex.exp ((⟪(x : H), ξ⟫ : ℝ) * Complex.I), by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp (continuous_subtype_val.inner continuous_const)⟩

@[simp]
theorem charOn_apply (K : Set H) (ξ : H) (x : K) :
    charOn K ξ x = Complex.exp ((⟪(x : H), ξ⟫ : ℝ) * Complex.I) := rfl

theorem charOn_mul (K : Set H) (ξ ζ : H) : charOn K ξ * charOn K ζ = charOn K (ξ + ζ) := by
  ext x
  simp only [ContinuousMap.mul_apply, charOn_apply, ← Complex.exp_add, inner_add_right]
  push_cast
  ring_nf

theorem charOn_zero (K : Set H) : charOn K (0 : H) = 1 := by
  ext x
  simp

theorem star_charOn (K : Set H) (ξ : H) : star (charOn K ξ) = charOn K (-ξ) := by
  ext x
  simp only [ContinuousMap.star_apply, charOn_apply, inner_neg_right, RCLike.star_def,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- The set of characters of `K`. -/
def charSet (K : Set H) : Set C(K, ℂ) := Set.range (charOn K)

theorem charSet_mul_subset (K : Set H) : charSet K * charSet K ⊆ charSet K := by
  refine Set.mul_subset_iff.2 ?_
  rintro _ ⟨ξ, rfl⟩ _ ⟨ζ, rfl⟩
  exact ⟨ξ + ζ, (charOn_mul K ξ ζ).symm⟩

theorem one_mem_span_charSet (K : Set H) :
    (1 : C(K, ℂ)) ∈ Submodule.span ℂ (charSet K) :=
  Submodule.subset_span ⟨0, charOn_zero K⟩

theorem mul_mem_span_charSet (K : Set H) {x y : C(K, ℂ)}
    (hx : x ∈ Submodule.span ℂ (charSet K)) (hy : y ∈ Submodule.span ℂ (charSet K)) :
    x * y ∈ Submodule.span ℂ (charSet K) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono (charSet_mul_subset K) h

theorem star_mem_span_charSet (K : Set H) {x : C(K, ℂ)}
    (hx : x ∈ Submodule.span ℂ (charSet K)) : star x ∈ Submodule.span ℂ (charSet K) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ξ, rfl⟩ := hy
      exact Submodule.subset_span ⟨-ξ, (star_charOn K ξ).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy

/-- The self-conjugate subalgebra of `C(K;ℂ)` spanned by the characters. -/
def charAlgebra (K : Set H) : StarSubalgebra ℂ C(K, ℂ) where
  toSubalgebra :=
    (Submodule.span ℂ (charSet K)).toSubalgebra (one_mem_span_charSet K)
      fun _ _ hx hy => mul_mem_span_charSet K hx hy
  star_mem' := fun hx => star_mem_span_charSet K hx

theorem charAlgebra_separatesPoints (K : Set H) : (charAlgebra K).SeparatesPoints := by
  rintro x y hxy
  have hne : (x : H) - (y : H) ≠ 0 := sub_ne_zero.2 fun h => hxy (Subtype.ext h)
  have hnorm : (0 : ℝ) < ‖(x : H) - (y : H)‖ ^ 2 := by positivity
  set ξ : H := (Real.pi / ‖(x : H) - (y : H)‖ ^ 2) • ((x : H) - (y : H)) with hξ
  have hinner : (⟪(x : H), ξ⟫ : ℝ) - (⟪(y : H), ξ⟫ : ℝ) = Real.pi := by
    rw [← inner_sub_left, hξ, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  refine ⟨charOn K ξ, ⟨charOn K ξ, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩, ?_⟩
  have hx : Complex.exp ((⟪(x : H), ξ⟫ : ℝ) * Complex.I) =
      -Complex.exp ((⟪(y : H), ξ⟫ : ℝ) * Complex.I) := by
    have h1 : ((⟪(x : H), ξ⟫ : ℝ) : ℂ) =
        ((⟪(y : H), ξ⟫ : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add]
      norm_cast
      linarith [hinner]
    rw [h1, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  intro hcon
  simp only [charOn_apply] at hcon
  rw [hx] at hcon
  exact Complex.exp_ne_zero ((⟪(y : H), ξ⟫ : ℝ) * Complex.I) (by linear_combination -hcon / 2)

/-- **Step 1 of Theorem `thm:D`.**  Every continuous `F` on a compact `K` is uniformly
approximated by a finite linear combination of characters.  The statement is for a continuous
map on the subtype `K`, so that it applies to functions defined only on `K`. -/
theorem exists_character_approx_continuousMap {K : Set H} (hK : IsCompact K) (F : C(K, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℂ) (ξ : Fin n → H), ∀ x : K,
      ‖F x - ∑ i, w i * Complex.exp ((⟪(x : H), ξ i⟫ : ℝ) * Complex.I)‖ ≤ ε := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have htop : (charAlgebra K).topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (charAlgebra_separatesPoints K)
  have hdense : Dense ((charAlgebra K : Set C(K, ℂ))) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe, htop]
    rfl
  obtain ⟨g, hgmem, hgdist⟩ := Metric.mem_closure_iff.1 (hdense.closure_eq ▸ Set.mem_univ F) ε hε
  obtain ⟨n, c, h, hsum⟩ := Submodule.mem_span_set'.1 hgmem
  have hchar : ∀ i : Fin n, ∃ ξ : H, (h i : C(K, ℂ)) = charOn K ξ := by
    intro i
    obtain ⟨ξ, hξ⟩ := (h i).2
    exact ⟨ξ, hξ.symm⟩
  choose ξ hξ using hchar
  refine ⟨n, c, ξ, fun x => ?_⟩
  have happ : g x = ∑ i, c i * Complex.exp ((⟪(x : H), ξ i⟫ : ℝ) * Complex.I) := by
    rw [← hsum]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hξ i]; rfl
  have hpt : ‖(F - g) x‖ ≤ ‖F - g‖ := ContinuousMap.norm_coe_le_norm (F - g) x
  rw [ContinuousMap.sub_apply, happ] at hpt
  refine hpt.trans ?_
  rw [← dist_eq_norm]
  exact hgdist.le

/-- **Step 1 of Theorem `thm:D`.**  Every continuous `f : H → ℂ` is uniformly approximated on a
compact `K` by a finite linear combination of characters. -/
theorem exists_character_approx {K : Set H} (hK : IsCompact K) {f : H → ℂ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℂ) (ξ : Fin n → H), ∀ x ∈ K,
      ‖f x - ∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I)‖ ≤ ε := by
  obtain ⟨n, w, ξ, h⟩ :=
    exists_character_approx_continuousMap hK ((⟨f, hf⟩ : C(H, ℂ)).restrict K) hε
  exact ⟨n, w, ξ, fun x hx => h ⟨x, hx⟩⟩

end Characters

/-! ### `Y`-valued approximation by characters -/

section CharactersVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Step 1 of Theorem `thm:D`, vector-valued, first half.**  A continuous `Y`-valued map is
uniformly approximated on a compact `K` by a finite combination `∑ g_k • y_k` of continuous
scalar functions with constant weights in `Y`: the compact set of values `f(K)` is covered by
finitely many `ε`-balls, and the bumps `max(0, ε − ‖f(x) − y_k‖)` of their centres normalize
into a partition of unity on `K`. -/
theorem exists_scalar_smul_approx {K : Set H} (hK : IsCompact K) {f : H → Y} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (y : Fin m → Y) (g : Fin m → C(K, ℂ)), ∀ x : K,
      ‖f x - ∑ k, g k x • y k‖ ≤ ε := by
  classical
  obtain ⟨t, -, hcov⟩ := (hK.image hf).elim_nhds_subcover (fun z : Y => Metric.ball z ε)
    fun z _ => Metric.ball_mem_nhds z hε
  set y : Fin t.card → Y := fun k => ((t.equivFin.symm k : { z // z ∈ t }) : Y) with hy
  have hcov' : ∀ x : K, ∃ k : Fin t.card, ‖f (x : H) - y k‖ < ε := by
    intro x
    obtain ⟨z, hz, hzx⟩ := Set.mem_iUnion₂.mp (hcov ⟨(x : H), x.2, rfl⟩)
    refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
    have hyk : y (t.equivFin ⟨z, hz⟩) = z := by rw [hy]; simp
    rw [hyk, ← dist_eq_norm]
    exact Metric.mem_ball.mp hzx
  set lam : Fin t.card → H → ℝ := fun k x => max 0 (ε - ‖f x - y k‖) with hlamdef
  have hlam_cont : ∀ k, Continuous (lam k) := fun k =>
    continuous_const.max (continuous_const.sub (hf.sub continuous_const).norm)
  have hlam_nonneg : ∀ k x, 0 ≤ lam k x := fun k x => le_max_left _ _
  set Lam : H → ℝ := fun x => ∑ k, lam k x with hLamdef
  have hLam_cont : Continuous Lam := continuous_finsetSum _ fun k _ => hlam_cont k
  have hLam_pos : ∀ x : K, 0 < Lam (x : H) := by
    intro x
    obtain ⟨k, hk⟩ := hcov' x
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun k => lam k (x : H)) (fun k _ => hlam_nonneg k _) (Finset.mem_univ k))
    exact lt_max_of_lt_right (by linarith)
  refine ⟨t.card, y, fun k => ⟨fun x : K => ((lam k (x : H) / Lam (x : H) : ℝ) : ℂ), ?_⟩,
    fun x => ?_⟩
  · exact Complex.continuous_ofReal.comp
      (((hlam_cont k).comp continuous_subtype_val).div (hLam_cont.comp continuous_subtype_val)
        fun x => (hLam_pos x).ne')
  · simp only [ContinuousMap.coe_mk]
    have hcnn : ∀ k, 0 ≤ lam k (x : H) / Lam (x : H) := fun k =>
      div_nonneg (hlam_nonneg k _) (hLam_pos x).le
    have hcsum : ∑ k, lam k (x : H) / Lam (x : H) = 1 := by
      rw [← Finset.sum_div]
      exact div_self (hLam_pos x).ne'
    have hkey : ∑ k, ((lam k (x : H) / Lam (x : H) : ℝ) : ℂ) • (f (x : H) - y k) =
        f (x : H) - ∑ k, ((lam k (x : H) / Lam (x : H) : ℝ) : ℂ) • y k := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum, hcsum,
        Complex.ofReal_one, one_smul]
    rw [← hkey]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k, ‖((lam k (x : H) / Lam (x : H) : ℝ) : ℂ) • (f (x : H) - y k)‖ ≤
        lam k (x : H) / Lam (x : H) * ε := by
      intro k
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hcnn k)]
      by_cases h0 : lam k (x : H) = 0
      · simp [h0]
      · have hlt : ‖f (x : H) - y k‖ < ε := by
          by_contra hcon
          exact h0 (by rw [hlamdef]; exact max_eq_left (by linarith [not_lt.mp hcon]))
        exact mul_le_mul_of_nonneg_left hlt.le (hcnn k)
    refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
    rw [← Finset.sum_mul, hcsum, one_mul]

/-- **Step 1 of Theorem `thm:D`, vector-valued.**  Every continuous `f : H → Y` is uniformly
approximated on a compact `K` by a finite combination of characters with constant weights in
`Y`. -/
theorem exists_character_approx_vec {K : Set H} (hK : IsCompact K) {f : H → Y}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → Y) (ξ : Fin n → H), ∀ x ∈ K,
      ‖f x - ∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i‖ ≤ ε := by
  classical
  obtain ⟨m, y, g, hg⟩ := exists_scalar_smul_approx hK hf (half_pos hε)
  set W : ℝ := ∑ k, ‖y k‖ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hη : 0 < ε / (2 * (1 + W)) := by positivity
  choose nn c ζ hc using fun k : Fin m => exists_character_approx_continuousMap hK (g k) hη
  obtain ⟨N, e⟩ : Σ' N : ℕ, Fin N ≃ Σ k : Fin m, Fin (nn k) :=
    ⟨Fintype.card (Σ k : Fin m, Fin (nn k)), (Fintype.equivFin _).symm⟩
  refine ⟨N, fun j => c (e j).1 (e j).2 • y (e j).1, fun j => ζ (e j).1 (e j).2, fun x hx => ?_⟩
  have hsum : ∑ j : Fin N, Complex.exp ((⟪x, ζ (e j).1 (e j).2⟫ : ℝ) * Complex.I) •
        (c (e j).1 (e j).2 • y (e j).1) =
      ∑ k : Fin m, (∑ i : Fin (nn k),
        c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k := by
    rw [Equiv.sum_comp e fun p : Σ k : Fin m, Fin (nn k) =>
      Complex.exp ((⟪x, ζ p.1 p.2⟫ : ℝ) * Complex.I) • (c p.1 p.2 • y p.1),
      ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  rw [hsum]
  have hA : ‖f x - ∑ k, g k ⟨x, hx⟩ • y k‖ ≤ ε / 2 := hg ⟨x, hx⟩
  have hB : ‖∑ k : Fin m, g k ⟨x, hx⟩ • y k -
      ∑ k : Fin m, (∑ i, c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k‖ ≤ ε / 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k : Fin m, ‖g k ⟨x, hx⟩ • y k -
        (∑ i, c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k‖ ≤
        ε / (2 * (1 + W)) * ‖y k‖ := by
      intro k
      rw [← sub_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right (hc k ⟨x, hx⟩) (norm_nonneg _)
    refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
    rw [← Finset.mul_sum, ← hW, div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  calc ‖f x - ∑ k : Fin m, (∑ i, c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k‖
      = ‖(f x - ∑ k, g k ⟨x, hx⟩ • y k) + (∑ k : Fin m, g k ⟨x, hx⟩ • y k -
          ∑ k : Fin m, (∑ i, c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖f x - ∑ k, g k ⟨x, hx⟩ • y k‖ + ‖∑ k : Fin m, g k ⟨x, hx⟩ • y k -
          ∑ k : Fin m, (∑ i, c k i * Complex.exp ((⟪x, ζ k i⟫ : ℝ) * Complex.I)) • y k‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hA hB
    _ = ε := by ring

end CharactersVec

/-! ### Normalized radial bumps -/

section Bump

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- The fixed profile: a smooth bump on `ℝ`, nonnegative, positive exactly on `(-1, 1)`. -/
def bumpProfile : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

@[simp] theorem bumpProfile_rOut : bumpProfile.rOut = 1 := rfl

theorem bumpProfile_nonneg (t : ℝ) : 0 ≤ bumpProfile t := bumpProfile.nonneg' t

theorem bumpProfile_le_one (t : ℝ) : bumpProfile t ≤ 1 := bumpProfile.le_one

theorem bumpProfile_pos_of_abs_lt_one {t : ℝ} (ht : |t| < 1) : 0 < bumpProfile t := by
  refine bumpProfile.pos_of_mem_ball ?_
  simpa [Real.dist_eq, bumpProfile_rOut] using ht

theorem bumpProfile_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : bumpProfile t = 0 := by
  refine bumpProfile.zero_of_le_dist ?_
  simpa [Real.dist_eq, bumpProfile_rOut] using ht

/-- The scaled and normalized profile `t ↦ φ(t/δ²)/Z`, as a complex-valued function. -/
def bumpProfileScaled (Z δ t : ℝ) : ℂ := ((Z⁻¹ : ℝ) : ℂ) * ((bumpProfile (t / δ ^ 2) : ℝ) : ℂ)

theorem contDiff_bumpProfileScaled (Z δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (bumpProfileScaled Z δ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => bumpProfile (t / δ ^ 2) :=
    bumpProfile.contDiff.comp (contDiff_id.div_const _)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => ((bumpProfile (t / δ ^ 2) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact ContDiff.mul contDiff_const h2

theorem hasCompactSupport_bumpProfileScaled (Z : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (bumpProfileScaled Z δ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(δ ^ 2)) (b := δ ^ 2)) fun t ht => ?_
  have habs : δ ^ 2 < |t| := by
    by_contra hcon
    rw [not_lt] at hcon
    exact ht (Set.mem_Icc.2 ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
  have h1 : 1 ≤ |t / δ ^ 2| := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ ^ 2), le_div_iff₀ (by positivity)]
    linarith
  simp [bumpProfileScaled, bumpProfile_eq_zero_of_one_le_abs h1]

/-- The unnormalized radial bump `ξ ↦ φ(‖ξ - ξ₀‖²/δ²)`. -/
def radialBump (ξ₀ : H) (δ : ℝ) (ξ : H) : ℝ := bumpProfile (‖ξ - ξ₀‖ ^ 2 / δ ^ 2)

theorem radialBump_nonneg (ξ₀ : H) (δ : ℝ) (ξ : H) : 0 ≤ radialBump ξ₀ δ ξ :=
  bumpProfile_nonneg _

theorem radialBump_le_one (ξ₀ : H) (δ : ℝ) (ξ : H) : radialBump ξ₀ δ ξ ≤ 1 :=
  bumpProfile_le_one _

theorem continuous_radialBump (ξ₀ : H) (δ : ℝ) : Continuous (radialBump ξ₀ δ) :=
  bumpProfile.continuous.comp (by fun_prop)

theorem radialBump_eq_zero_of_le {ξ₀ : H} {δ : ℝ} (hδ : 0 < δ) {ξ : H} (hξ : δ ≤ ‖ξ - ξ₀‖) :
    radialBump ξ₀ δ ξ = 0 := by
  refine bumpProfile_eq_zero_of_one_le_abs ?_
  rw [abs_of_nonneg (by positivity), le_div_iff₀ (by positivity), one_mul]
  nlinarith [norm_nonneg (ξ - ξ₀)]

theorem norm_sub_lt_of_radialBump_ne_zero {ξ₀ : H} {δ : ℝ} (hδ : 0 < δ) {ξ : H}
    (hξ : radialBump ξ₀ δ ξ ≠ 0) : ‖ξ - ξ₀‖ < δ := by
  by_contra hcon
  exact hξ (radialBump_eq_zero_of_le hδ (not_lt.1 hcon))

theorem radialBump_self_pos (ξ₀ : H) (δ : ℝ) : 0 < radialBump ξ₀ δ ξ₀ := by
  refine bumpProfile_pos_of_abs_lt_one ?_
  simp

theorem integrable_radialBump (ν : Measure H) (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤)
    (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) : Integrable (radialBump ξ₀ δ) ν := by
  refine Integrable.mono'
    (g := Set.indicator (closedBall (0 : H) (‖ξ₀‖ + δ)) fun _ => (1 : ℝ)) ?_
    (continuous_radialBump ξ₀ δ).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  · rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (hfin _).ne
  · by_cases hmem : ξ ∈ closedBall (0 : H) (‖ξ₀‖ + δ)
    · rw [Set.indicator_of_mem hmem, Real.norm_of_nonneg (radialBump_nonneg _ _ _)]
      exact radialBump_le_one _ _ _
    · rw [Set.indicator_of_notMem hmem]
      have hlarge : ‖ξ₀‖ + δ < ‖ξ‖ := by
        simpa [mem_closedBall, dist_zero_right, not_le] using hmem
      have hd : δ ≤ ‖ξ - ξ₀‖ := by
        have := norm_sub_norm_le ξ ξ₀
        linarith
      simp [radialBump_eq_zero_of_le hδ hd]

/-- The normalizing constant `Z = ∫ φ(‖ξ - ξ₀‖²/δ²) dν(ξ)`. -/
def bumpWeight (ν : Measure H) (ξ₀ : H) (δ : ℝ) : ℝ := ∫ ξ, radialBump ξ₀ δ ξ ∂ν

theorem bumpWeight_pos (ν : Measure H) [ν.IsOpenPosMeasure]
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) :
    0 < bumpWeight ν ξ₀ δ :=
  integral_pos_of_integrable_nonneg_nonzero (x := ξ₀) (continuous_radialBump ξ₀ δ)
    (integrable_radialBump ν hfin ξ₀ hδ) (fun ξ => radialBump_nonneg _ _ ξ)
    (radialBump_self_pos ξ₀ δ).ne'

/-- The normalized radial bump density `G_{ξ₀,δ}(ξ) = φ(‖ξ - ξ₀‖²/δ²)/Z`. -/
def bumpDensity (ν : Measure H) (ξ₀ : H) (δ : ℝ) (ξ : H) : ℂ :=
  bumpProfileScaled (bumpWeight ν ξ₀ δ) δ (‖ξ - ξ₀‖ ^ 2)

theorem bumpDensity_eq (ν : Measure H) (ξ₀ : H) (δ : ℝ) (ξ : H) :
    bumpDensity ν ξ₀ δ ξ = (((bumpWeight ν ξ₀ δ)⁻¹ : ℝ) : ℂ) * ((radialBump ξ₀ δ ξ : ℝ) : ℂ) :=
  rfl

theorem norm_bumpDensity (ν : Measure H) [ν.IsOpenPosMeasure]
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) (ξ : H) :
    ‖bumpDensity ν ξ₀ δ ξ‖ = (bumpWeight ν ξ₀ δ)⁻¹ * radialBump ξ₀ δ ξ := by
  have hZ : 0 < bumpWeight ν ξ₀ δ := bumpWeight_pos ν hfin ξ₀ hδ
  rw [bumpDensity_eq, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (inv_pos.2 hZ).le, Real.norm_of_nonneg (radialBump_nonneg _ _ _)]

theorem contDiff_bumpDensity (ν : Measure H) (ξ₀ : H) (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (bumpDensity ν ξ₀ δ) :=
  (contDiff_bumpProfileScaled _ _).comp
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem bumpDensity_eq_zero_of_lt (ν : Measure H) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) {ξ : H}
    (hξ : ‖ξ₀‖ + δ < ‖ξ‖) : bumpDensity ν ξ₀ δ ξ = 0 := by
  have hd : δ ≤ ‖ξ - ξ₀‖ := by
    have := norm_sub_norm_le ξ ξ₀
    linarith
  rw [bumpDensity_eq, radialBump_eq_zero_of_le hδ hd]
  simp

theorem integrable_bumpDensity (ν : Measure H)
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (bumpDensity ν ξ₀ δ) ν :=
  ((integrable_radialBump ν hfin ξ₀ hδ).ofReal).const_mul _

theorem integral_bumpDensity (ν : Measure H) [ν.IsOpenPosMeasure]
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) :
    ∫ ξ, bumpDensity ν ξ₀ δ ξ ∂ν = 1 := by
  have hZ := bumpWeight_pos ν hfin ξ₀ hδ
  simp only [bumpDensity_eq]
  rw [integral_const_mul, integral_complex_ofReal, ← bumpWeight, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hZ.ne']
  norm_num

theorem integral_norm_bumpDensity (ν : Measure H) [ν.IsOpenPosMeasure]
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) :
    ∫ ξ, ‖bumpDensity ν ξ₀ δ ξ‖ ∂ν = 1 := by
  have hZ := bumpWeight_pos ν hfin ξ₀ hδ
  have hcongr : ∀ ξ : H, ‖bumpDensity ν ξ₀ δ ξ‖ = (bumpWeight ν ξ₀ δ)⁻¹ * radialBump ξ₀ δ ξ :=
    fun ξ => norm_bumpDensity ν hfin ξ₀ hδ ξ
  rw [integral_congr_ae (Eventually.of_forall hcongr), integral_const_mul, ← bumpWeight,
    inv_mul_cancel₀ hZ.ne']

theorem isRegularAlongRays_bumpDensity (ν : Measure H)
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) : IsRegularAlongRays ν I (bumpDensity ν ξ₀ δ) :=
  isRegularAlongRays_radialBump ν hfin ξ₀ (contDiff_bumpProfileScaled _ _)
    (hasCompactSupport_bumpProfileScaled _ hδ) hI hI0

end Bump

/-! ### Elementary properties of the spectral target -/

section SpectralTargetAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

theorem continuous_expInner (x : H) :
    Continuous fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).mul continuous_const)

theorem spectralTarget_eq_integral_mul (ν : Measure H) (G : H → ℂ) (x : H) :
    spectralTarget ν G x = ∫ ξ, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * G ξ ∂ν := rfl

theorem integrable_expInner_mul {ν : Measure H} {g : H → ℂ} (hg : Integrable g ν) (x : H) :
    Integrable (fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * g ξ) ν := by
  refine Integrable.mono' hg.norm
    ((continuous_expInner x).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]

theorem spectralTarget_finset_sum (ν : Measure H) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (G : ι → H → ℂ) (hG : ∀ i ∈ s, Integrable (G i) ν) (x : H) :
    spectralTarget ν (fun ξ => ∑ i ∈ s, c i * G i ξ) x =
      ∑ i ∈ s, c i * spectralTarget ν (G i) x := by
  rw [spectralTarget_eq_integral_mul]
  have h1 : ∀ ξ : H, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * (∑ i ∈ s, c i * G i ξ) =
      ∑ i ∈ s, c i * (Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * G i ξ) := by
    intro ξ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (Eventually.of_forall h1),
    integral_finsetSum _ fun i hi => (integrable_expInner_mul (hG i hi) x).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_const_mul, spectralTarget_eq_integral_mul]

/-- **Step 2 of Theorem `thm:D`.**  A character is uniformly close to the target with the
normalized radial bump as spectral density. -/
theorem norm_char_sub_spectralTarget_bumpDensity_le (ν : Measure H) [ν.IsOpenPosMeasure]
    (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) (ξ₀ : H) {δ : ℝ} (hδ : 0 < δ) (x : H) :
    ‖Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) - spectralTarget ν (bumpDensity ν ξ₀ δ) x‖ ≤
      ‖x‖ * δ := by
  have hint : Integrable (bumpDensity ν ξ₀ δ) ν := integrable_bumpDensity ν hfin ξ₀ hδ
  have hint1 : Integrable
      (fun ξ : H => Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ) ν :=
    hint.const_mul _
  have hint2 : Integrable
      (fun ξ : H => Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ) ν :=
    integrable_expInner_mul hint x
  have hchar : Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) =
      ∫ ξ, Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ ∂ν := by
    rw [integral_const_mul, integral_bumpDensity ν hfin ξ₀ hδ, mul_one]
  rw [spectralTarget_eq_integral_mul]
  rw [hchar, ← integral_sub hint1 hint2]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ ξ : H,
      ‖Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ -
          Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ‖ ≤
        ‖x‖ * δ * ‖bumpDensity ν ξ₀ δ ξ‖ := by
    intro ξ
    by_cases hz : bumpDensity ν ξ₀ δ ξ = 0
    · simp [hz]
    · rw [← sub_mul, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hne : radialBump ξ₀ δ ξ ≠ 0 := by
        intro hzero
        exact hz (by rw [bumpDensity_eq, hzero]; simp)
      have hlt : ‖ξ - ξ₀‖ < δ := norm_sub_lt_of_radialBump_ne_zero hδ hne
      refine (norm_exp_ofReal_mul_I_sub_exp_ofReal_mul_I_le _ _).trans ?_
      have hsub : (⟪x, ξ₀⟫ : ℝ) - (⟪x, ξ⟫ : ℝ) = (⟪x, ξ₀ - ξ⟫ : ℝ) := (inner_sub_right _ _ _).symm
      rw [hsub]
      refine (abs_real_inner_le_norm x (ξ₀ - ξ)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
      rw [← norm_neg, neg_sub]
      exact hlt.le
  calc ∫ ξ, ‖Complex.exp ((⟪x, ξ₀⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ -
          Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * bumpDensity ν ξ₀ δ ξ‖ ∂ν
      ≤ ∫ ξ, ‖x‖ * δ * ‖bumpDensity ν ξ₀ δ ξ‖ ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hint.norm.const_mul _) (Eventually.of_forall hpt)
    _ = ‖x‖ * δ := by
        rw [integral_const_mul, integral_norm_bumpDensity ν hfin ξ₀ hδ, mul_one]

end SpectralTargetAux

/-! ### The approximating spectral density -/

section Approx

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- **Steps 1--3 of Theorem `thm:D`.**  For a direction measure with full support that is finite
on bounded sets, every continuous `f` is uniformly approximated on a compact `K` by the target
`g_G` of a spectral density `G` that is smooth, vanishes outside a bounded set, and is regular
along rays. -/
theorem exists_isRegularAlongRays_norm_sub_spectralTarget_le (ν : Measure H)
    [ν.IsOpenPosMeasure] (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) {f : H → ℂ} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → ℂ, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      (∀ x ∈ K, ‖f x - spectralTarget ν G x‖ ≤ ε) := by
  obtain ⟨n, w, ξ, hw⟩ := exists_character_approx hK hf (half_pos hε)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : H)
  set W : ℝ := ∑ i, ‖w i‖ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => norm_nonneg _
  set ρ₀ : ℝ := max r 0 with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  have hxr : ∀ x ∈ K, ‖x‖ ≤ ρ₀ := by
    intro x hx
    have hmem := hr hx
    rw [mem_closedBall, dist_zero_right] at hmem
    exact hmem.trans (le_max_left _ _)
  set δ : ℝ := ε / (2 * (1 + ρ₀) * (1 + W)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  refine ⟨fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ, ?_, ?_, ?_, ?_⟩
  · exact IsRegularAlongRays.finset_sum Finset.univ w (fun i => bumpDensity ν (ξ i) δ)
      fun i _ => isRegularAlongRays_bumpDensity ν hfin (ξ i) hδ hI hI0
  · exact ContDiff.sum fun i _ =>
      ContDiff.mul contDiff_const (contDiff_bumpDensity ν (ξ i) δ)
  · refine ⟨∑ i, (‖(ξ i : H)‖ + δ), fun ζ hζ => ?_⟩
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : ‖(ξ i : H)‖ + δ ≤ ∑ j, (‖(ξ j : H)‖ + δ) :=
      Finset.single_le_sum (f := fun j => ‖(ξ j : H)‖ + δ)
        (fun j _ => by positivity) (Finset.mem_univ i)
    rw [bumpDensity_eq_zero_of_lt ν (ξ i) hδ (lt_of_le_of_lt hle hζ), mul_zero]
  · intro x hx
    have hsplit : spectralTarget ν (fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ) x =
        ∑ i, w i * spectralTarget ν (bumpDensity ν (ξ i) δ) x :=
      spectralTarget_finset_sum ν Finset.univ w (fun i => bumpDensity ν (ξ i) δ)
        (fun i _ => integrable_bumpDensity ν hfin (ξ i) hδ) x
    have hbound : ‖∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) -
        spectralTarget ν (fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ) x‖ ≤ ε / 2 := by
      rw [hsplit, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ i : Fin n,
          ‖w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) -
            w i * spectralTarget ν (bumpDensity ν (ξ i) δ) x‖ ≤ ‖w i‖ * (ρ₀ * δ) := by
        intro i
        rw [← mul_sub, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (norm_char_sub_spectralTarget_bumpDensity_le ν hfin (ξ i) hδ x).trans ?_
        exact mul_le_mul_of_nonneg_right (hxr x hx) hδ.le
      refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
      rw [← Finset.sum_mul, ← hW]
      have h3 : W * ρ₀ ≤ (1 + ρ₀) * (1 + W) := by nlinarith
      calc W * (ρ₀ * δ) = W * ρ₀ * δ := by ring
        _ ≤ (1 + ρ₀) * (1 + W) * δ := mul_le_mul_of_nonneg_right h3 hδ.le
        _ = ε / 2 := by
            have h4 : (1 + ρ₀) ≠ 0 := by positivity
            have h5 : (1 + W) ≠ 0 := by positivity
            rw [hδdef]
            field_simp
    calc ‖f x - spectralTarget ν (fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ) x‖
        = ‖(f x - ∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I)) +
            (∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) -
              spectralTarget ν (fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ) x)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖f x - ∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I)‖ +
            ‖∑ i, w i * Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) -
              spectralTarget ν (fun ζ => ∑ i, w i * bumpDensity ν (ξ i) δ ζ) x‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hw x hx) hbound
      _ = ε := by ring

end Approx

/-! ### The approximating `Y`-valued spectral density -/

section ApproxVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The spectral target of a finite combination of scalar densities with constant weights in
`Y` is the combination of the scalar targets. -/
theorem spectralTarget_finset_sum_smul (ν : Measure H) {ι : Type*} (s : Finset ι)
    (G : ι → H → ℂ) (w : ι → Y) (hG : ∀ i ∈ s, Integrable (G i) ν) (x : H) :
    spectralTarget ν (fun ξ => ∑ i ∈ s, G i ξ • w i) x =
      ∑ i ∈ s, spectralTarget ν (G i) x • w i := by
  have h1 : ∀ ξ : H, Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) • (∑ i ∈ s, G i ξ • w i) =
      ∑ i ∈ s, (Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * G i ξ) • w i := fun ξ => by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  calc spectralTarget ν (fun ξ => ∑ i ∈ s, G i ξ • w i) x
      = ∫ ξ, ∑ i ∈ s, (Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * G i ξ) • w i ∂ν :=
        integral_congr_ae (Eventually.of_forall h1)
    _ = ∑ i ∈ s, ∫ ξ, (Complex.exp ((⟪x, ξ⟫ : ℝ) * Complex.I) * G i ξ) • w i ∂ν :=
        integral_finsetSum _ fun i hi => (integrable_expInner_mul (hG i hi) x).smul_const (w i)
    _ = ∑ i ∈ s, spectralTarget ν (G i) x • w i :=
        Finset.sum_congr rfl fun i _ => by
          rw [integral_smul_const, spectralTarget_eq_integral_mul]

/-- **Steps 1--3 of Theorem `thm:D`, vector-valued.**  For a direction measure with full support
that is finite on bounded sets, every continuous `f : H → Y` is uniformly approximated on a
compact `K` by the target `g_G` of a `Y`-valued spectral density `G` that is smooth, vanishes
outside a bounded set, and is regular along rays. -/
theorem exists_isRegularAlongRays_norm_sub_spectralTarget_leVec (ν : Measure H)
    [ν.IsOpenPosMeasure] (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) {I : Set ℝ}
    (hI : IsCompact I) (hI0 : (0 : ℝ) ∉ I) {f : H → Y} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → Y, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      (∀ x ∈ K, ‖f x - spectralTarget ν G x‖ ≤ ε) := by
  obtain ⟨n, w, ξ, hw⟩ := exists_character_approx_vec hK hf (half_pos hε)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : H)
  set W : ℝ := ∑ i, ‖w i‖ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => norm_nonneg _
  set ρ₀ : ℝ := max r 0 with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  have hxr : ∀ x ∈ K, ‖x‖ ≤ ρ₀ := by
    intro x hx
    have hmem := hr hx
    rw [mem_closedBall, dist_zero_right] at hmem
    exact hmem.trans (le_max_left _ _)
  set δ : ℝ := ε / (2 * (1 + ρ₀) * (1 + W)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  refine ⟨fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i, ?_, ?_, ?_, ?_⟩
  · exact IsRegularAlongRays.finset_sum_smul Finset.univ (fun i => bumpDensity ν (ξ i) δ) w
      fun i _ => isRegularAlongRays_bumpDensity ν hfin (ξ i) hδ hI hI0
  · exact ContDiff.sum fun i _ => (contDiff_bumpDensity ν (ξ i) δ).smul_const (w i)
  · refine ⟨∑ i, (‖(ξ i : H)‖ + δ), fun ζ hζ => ?_⟩
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : ‖(ξ i : H)‖ + δ ≤ ∑ j, (‖(ξ j : H)‖ + δ) :=
      Finset.single_le_sum (f := fun j => ‖(ξ j : H)‖ + δ)
        (fun j _ => by positivity) (Finset.mem_univ i)
    rw [bumpDensity_eq_zero_of_lt ν (ξ i) hδ (lt_of_le_of_lt hle hζ), zero_smul]
  · intro x hx
    have hsplit : spectralTarget ν (fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i) x =
        ∑ i, spectralTarget ν (bumpDensity ν (ξ i) δ) x • w i :=
      spectralTarget_finset_sum_smul ν Finset.univ (fun i => bumpDensity ν (ξ i) δ) w
        (fun i _ => integrable_bumpDensity ν hfin (ξ i) hδ) x
    have hbound : ‖∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i -
        spectralTarget ν (fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i) x‖ ≤ ε / 2 := by
      rw [hsplit, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ i : Fin n,
          ‖Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i -
            spectralTarget ν (bumpDensity ν (ξ i) δ) x • w i‖ ≤ ρ₀ * δ * ‖w i‖ := by
        intro i
        rw [← sub_smul, norm_smul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (norm_char_sub_spectralTarget_bumpDensity_le ν hfin (ξ i) hδ x).trans ?_
        exact mul_le_mul_of_nonneg_right (hxr x hx) hδ.le
      refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
      rw [← Finset.mul_sum, ← hW]
      have h3 : W * ρ₀ ≤ (1 + ρ₀) * (1 + W) := by nlinarith
      calc ρ₀ * δ * W = W * ρ₀ * δ := by ring
        _ ≤ (1 + ρ₀) * (1 + W) * δ := mul_le_mul_of_nonneg_right h3 hδ.le
        _ = ε / 2 := by
            have h4 : (1 + ρ₀) ≠ 0 := by positivity
            have h5 : (1 + W) ≠ 0 := by positivity
            rw [hδdef]
            field_simp
    calc ‖f x - spectralTarget ν (fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i) x‖
        = ‖(f x - ∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i) +
            (∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i -
              spectralTarget ν (fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i) x)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖f x - ∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i‖ +
            ‖∑ i, Complex.exp ((⟪x, ξ i⟫ : ℝ) * Complex.I) • w i -
              spectralTarget ν (fun ζ => ∑ i, bumpDensity ν (ξ i) δ ζ • w i) x‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hw x hx) hbound
      _ = ε := by ring

end ApproxVec

/-! ### Theorem `thm:D` for a direction measure finite on bounded sets -/

section Universal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The target with a density regular along rays is the integral network of the explicit
coefficient; Theorem `thm:E`(iii) without the Lipschitz hypothesis on the activation. -/
theorem spectralTarget_eq_integralNetworkDensity (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ}
    (hβ : IsTemperedFunction β b) {G : H → ℂ} (hG : IsRegularAlongRays ν I G) (x : H) :
    temperedAdmissibilityConst α β ρ * spectralTarget ν G x =
      integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
        (coefficientFormula ρ G) x := by
  have hint : Integrable (fun θ : H × ℝ =>
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ) (ν.prod volume) := by
    refine (integrable_prod_smul_coefficientFormulaVec hρ hI hG hβ.continuous
      hβ.polynomialGrowth x).congr (Eventually.of_forall fun θ => ?_)
    show (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G (θ.1, θ.2) =
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormula ρ G θ
    rw [Prod.mk.eta, coefficientFormulaVec_eq_coefficientFormula]
  rw [← integral_integral_coefficientFormula_mul_activation hν hρ hI hG hβ x,
    integralNetworkDensity, parameterMeasure, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  show coefficientFormula ρ G (a, c) * (b (⟪a, x⟫ + c) : ℂ) =
    (b (⟪a, x⟫ + c) : ℂ) * coefficientFormula ρ G (a, c)
  ring

/-- **Theorem `thm:D`** for a direction measure that is finite on bounded sets: a constructive
universal approximation with the rate of Theorem `thm:lipschitz-barron`. -/
theorem exists_spectralDensity_universal_approx (ν : Measure H) [SigmaFinite ν]
    [ν.IsOpenPosMeasure] (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) {α : ℝ}
    (hν : IsHomogeneous α ν) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    {f : H → ℂ} (hf : Continuous f) {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → ℂ, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      compactSupNorm K (fun x => f x - spectralTarget ν G x) < ε ∧
      spectralTarget ν G =
        integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
          (coefficientFormula ρ G) ∧
      (∀ m : ℕ, Integrable
        (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormula ρ G θ‖)
        (parameterMeasure ν)) ∧
      (∀ L : ℝ≥0, LipschitzWith L b → ∀ N : ℕ, 0 < N →
        (∫ θ, compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) ≤
          ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormula ρ G) / Real.sqrt N *
            (|b 0| + (L : ℝ) * compactRadius K *
              Real.sqrt
                (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))))) ∧
        ∃ θ : Fin N → H × ℝ,
          compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x) ≤
            ε + 8 * densityWeight (parameterMeasure ν) (coefficientFormula ρ G) / Real.sqrt N *
              (|b 0| + (L : ℝ) * compactRadius K *
                Real.sqrt
                  (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))))) := by
  obtain ⟨G, hGreg, hGsmooth, hGsupp, hGapp⟩ :=
    exists_isRegularAlongRays_norm_sub_spectralTarget_le ν hfin hI.isCompact hI.zero_notMem hf hK
      (half_pos hε)
  have hfun : coefficientFormulaVec (Y := ℂ) ρ G = coefficientFormula ρ G :=
    coefficientFormulaVec_eq_coefficientFormula' ρ G
  have hγ : Integrable (coefficientFormula ρ G) (parameterMeasure ν) :=
    hfun ▸ integrable_coefficientFormulaVec hρ hI hGreg
  have hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2)
      (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) :=
    hfun ▸ integrable_sq_densityLaw_coefficientFormulaVec hρ hI hGreg
  have hgeq : spectralTarget ν G =
      integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
        (coefficientFormula ρ G) := by
    funext x
    rw [← spectralTarget_eq_integralNetworkDensity ν hν ρ hρ hI hβ hGreg x, hC, one_mul]
  have hA : ∀ x ∈ K, ‖f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
      (coefficientFormula ρ G) x‖ ≤ ε / 2 := by
    intro x hx
    rw [← hgeq]
    exact hGapp x hx
  refine ⟨G, hGreg, hGsmooth, hGsupp, ?_, hgeq, ?_, ?_⟩
  · exact lt_of_le_of_lt (compactSupNorm_le (by positivity) hGapp) (by linarith)
  · intro m
    exact hfun ▸ integrable_moment_norm_coefficientFormulaVec (Y := ℂ) hρ hI hGreg m
  · intro L hb N hN
    set W : ℝ := densityWeight (parameterMeasure ν) (coefficientFormula ρ G) with hWdef
    set bnd : ℝ := 8 * W / Real.sqrt N *
      (|b 0| + (L : ℝ) * compactRadius K *
        Real.sqrt (secondMoment (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))))
      with hbnddef
    by_cases hV : W = 0
    · have hcoeff : ∀ᵐ θ ∂parameterMeasure ν, coefficientFormula ρ G θ = 0 := by
        have h := (integral_eq_zero_iff_of_nonneg (fun θ => norm_nonneg (coefficientFormula ρ G θ))
          hγ.norm).mp hV
        filter_upwards [h] with θ hθ using norm_eq_zero.mp hθ
      have hnet : ∀ x : H, integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
          (coefficientFormula ρ G) x = 0 := by
        intro x
        refine (integral_congr_ae (g := fun _ : H × ℝ => (0 : ℂ)) ?_).trans (integral_zero _ _)
        filter_upwards [hcoeff] with θ hθ using by rw [hθ, smul_zero]
      have hbnd0 : bnd = 0 := by rw [hbnddef, hV]; simp
      have hsampled : ∀ (θ : Fin N → H × ℝ) (x : H),
          densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
            (coefficientFormula ρ G) θ x = 0 := by
        intro θ x
        simp [densitySampledNetwork, sampledNetwork, finiteNetwork, ← hWdef, hV]
      constructor
      · rw [densityLaw_eq_zero hγ hV, sampleLaw_zero hN, integral_zero_measure, hbnd0]
        linarith
      · refine ⟨fun _ => (0, 0), ?_⟩
        rw [hbnd0, add_zero]
        refine compactSupNorm_le hε.le fun x hx => ?_
        rw [hsampled, sub_zero]
        have := hA x hx
        rw [hnet, sub_zero] at this
        linarith
    · haveI := isProbabilityMeasure_densityLaw hγ hV
      have hDint := integrable_compactSupNorm_densitySampledNetwork_sub hK hb hγ hV hM hN
      have hptw : ∀ θ : Fin N → H × ℝ,
          compactSupNorm K (fun x => f x - densitySampledNetwork (fun t => (b t : ℂ))
              (parameterMeasure ν) (coefficientFormula ρ G) θ x) ≤
            ε / 2 + compactSupNorm K (fun x =>
              densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x -
              integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) x) := by
        intro θ
        refine compactSupNorm_le (add_nonneg (by positivity) (compactSupNorm_nonneg _ _))
          fun x hx => ?_
        calc ‖f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormula ρ G) θ x‖
            = ‖(f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x) +
                (integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x -
                  densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                    (coefficientFormula ρ G) θ x)‖ := by
              rw [sub_add_sub_cancel]
          _ ≤ ‖f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x‖ +
                ‖integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x -
                  densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                    (coefficientFormula ρ G) θ x‖ := norm_add_le _ _
          _ ≤ ε / 2 + _ := by
              refine add_le_add (hA x hx) ?_
              rw [norm_sub_rev]
              exact norm_densitySampledNetwork_sub_le_compactSupNorm hK hb hγ hV hM hN θ hx
      constructor
      · calc ∫ θ, compactSupNorm K (fun x => f x - densitySampledNetwork (fun t => (b t : ℂ))
                (parameterMeasure ν) (coefficientFormula ρ G) θ x)
              ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G))
            ≤ ∫ θ, (ε / 2 + compactSupNorm K (fun x =>
                densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) θ x -
                integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x))
              ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => compactSupNorm_nonneg _ _)
                (Integrable.add (integrable_const _) hDint) (Eventually.of_forall hptw)
          _ = ε / 2 + ∫ θ, compactSupNorm K (fun x =>
                densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) θ x -
                integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormula ρ G) x)
              ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormula ρ G)) := by
              rw [integral_add (integrable_const _) hDint, integral_const]
              simp
          _ ≤ ε / 2 + bnd :=
              add_le_add le_rfl
                (integral_compactSupNorm_densitySampledNetwork_sub_le hK hb hγ hM hN)
          _ ≤ ε + bnd := by linarith
      · obtain ⟨θ, hθ⟩ := exists_compactSupNorm_densitySampledNetwork_sub_le hK hb hγ hM hN
        refine ⟨θ, (hptw θ).trans ?_⟩
        have h2 : ε / 2 + compactSupNorm K (fun x =>
            densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) θ x -
            integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
              (coefficientFormula ρ G) x) ≤ ε / 2 + bnd := add_le_add le_rfl hθ
        linarith

end Universal


/-! ### `Y`-valued ridge atoms -/

section VectorAtoms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {K : Set H}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The `Y`-valued ridge atom `x ↦ β(⟪a, x⟫ + c) • y` of a continuous complex activation,
restricted to the compact set `K`, as a bounded continuous function on `K`.  The parameter and
the outer weight are taken as a single argument so that the atom is a continuous function of
the pair, which is what makes the atoms of a measurable phase strongly measurable. -/
def ridgeAtomVec (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) (q : (H × ℝ) × Y) :
    K →ᵇ Y :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K => β (⟪q.1.1, (x : H)⟫ + q.1.2) • q.2, by fun_prop⟩

theorem ridgeAtomVec_apply (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β)
    (q : (H × ℝ) × Y) (x : K) :
    ridgeAtomVec hK hβ q x = β (⟪q.1.1, (x : H)⟫ + q.1.2) • q.2 :=
  rfl

/-- The `Y`-valued ridge atoms depend continuously on the parameter and the outer weight. -/
theorem continuous_ridgeAtomVec (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β) :
    Continuous (ridgeAtomVec (Y := Y) hK hβ) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(((H × ℝ) × Y) × K, Y) :=
    ⟨fun r => β (⟪r.1.1.1, (r.2 : H)⟫ + r.1.1.2) • r.1.2, by fun_prop⟩
  have hF : ridgeAtomVec (Y := Y) hK hβ = fun q =>
      ContinuousMap.isometryEquivBoundedOfCompact K Y (ContinuousMap.curry F q) := rfl
  rw [hF]
  exact (ContinuousMap.isometryEquivBoundedOfCompact K Y).continuous.comp
    (ContinuousMap.curry F).continuous

/-- The norm of a `Y`-valued ridge atom is at most the norm of the scalar ridge atom times the
norm of the outer weight. -/
theorem norm_ridgeAtomVec_le (hK : IsCompact K) {β : ℝ → ℂ} (hβ : Continuous β)
    (q : (H × ℝ) × Y) : ‖ridgeAtomVec hK hβ q‖ ≤ ‖ridgeAtom hK hβ q.1‖ * ‖q.2‖ := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr fun x => ?_
  rw [ridgeAtomVec_apply, norm_smul]
  exact mul_le_mul_of_nonneg_right
    (BoundedContinuousFunction.norm_coe_le_norm (ridgeAtom hK hβ q.1) x) (norm_nonneg _)

end VectorAtoms

section VectorAtomsMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] {K : Set H} {Ω : Type*} [MeasurableSpace Ω]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The `C(K;Y)`-valued atoms `ω ↦ β(⟪a(ω), ·⟫ + c(ω)) • h(ω)` of a `Y`-valued sampled network
with `‖h‖ ≤ 1` are Bochner integrable under the second-moment condition. -/
theorem integrable_ridgeAtomVec (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure Ω) [IsProbabilityMeasure p] {π : Ω → H × ℝ}
    (hπ : Measurable π) {h : Ω → Y} (hh : AEStronglyMeasurable h p) (hh1 : ∀ᵐ ω ∂p, ‖h ω‖ ≤ 1)
    (hM : Integrable (fun ω => ‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2) p) :
    Integrable (fun ω => ridgeAtomVec hK (continuous_ofReal_comp hβ) (π ω, h ω)) p := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hmeas : AEStronglyMeasurable
      (fun ω => ridgeAtomVec hK (continuous_ofReal_comp hβ) (π ω, h ω)) p :=
    (continuous_ridgeAtomVec hK (continuous_ofReal_comp hβ)).comp_aestronglyMeasurable
      (hπ.aestronglyMeasurable.prodMk hh)
  set C : ℝ := |β 0| + L * max r 1 with hC
  have hC0 : 0 ≤ C :=
    add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg (zero_le_one.trans (le_max_right r 1)))
  have hbound : Integrable (fun ω => C * (3 + (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2))) p :=
    ((integrable_const 3).add hM).const_mul C
  refine hbound.mono' hmeas ?_
  filter_upwards [hh1] with ω hω
  calc ‖ridgeAtomVec hK (continuous_ofReal_comp hβ) (π ω, h ω)‖
      ≤ ‖ridgeAtom hK (continuous_ofReal_comp hβ) (π ω)‖ * ‖h ω‖ :=
        norm_ridgeAtomVec_le hK (continuous_ofReal_comp hβ) (π ω, h ω)
    _ ≤ (C * (1 + ‖(π ω).1‖ + |(π ω).2|)) * 1 :=
        mul_le_mul (norm_ridgeAtom_le hK hβ hr _) hω (norm_nonneg _)
          (mul_nonneg hC0 (by positivity))
    _ ≤ C * (3 + (‖(π ω).1‖ ^ 2 + |(π ω).2| ^ 2)) := by
        rw [mul_one]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        nlinarith [sq_nonneg (‖(π ω).1‖ - 1), sq_nonneg (|(π ω).2| - 1)]

end VectorAtomsMeasurable


/-! ### The `Y`-valued sampled network and its Rademacher bound -/

section VectorSampling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {K : Set H}
  {Ω : Type*} [MeasurableSpace Ω]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Evaluation of the scaled, centred sum of the `Y`-valued atoms
`Φ(ω) = β(⟪π(ω)_1, ·⟫ + π(ω)_2) • h(ω)` at a point of `K`: it is the sampled-network error. -/
theorem smul_sum_sub_applyVec (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → Y) {Φ : Ω → (K →ᵇ Y)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) • h ω) (hint : Integrable Φ p)
    (V : ℝ) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) (x : K) :
    ((V / N : ℝ) • (∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p)) x =
      ∑ j, β (⟪(π (ω j)).1, (x : H)⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
        V • ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) • h ω' ∂p := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have heval : (∫ ω', Φ ω' ∂p) x = ∫ ω', β (⟪(π ω').1, (x : H)⟫ + (π ω').2) • h ω' ∂p := by
    change (BoundedContinuousFunction.evalCLM ℂ x) (∫ ω', Φ ω' ∂p) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    exact integral_congr_ae (Eventually.of_forall fun ω' => hΦ ω' x)
  change (V / N : ℝ) • ((BoundedContinuousFunction.evalCLM ℂ x) (∑ j, Φ (ω j)) -
    (N : ℝ) • (∫ ω', Φ ω' ∂p) x) = _
  rw [map_sum, heval, smul_sub, smul_smul, div_mul_cancel₀ V hN', Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change (V / N : ℝ) • Φ (ω j) x = _
  rw [hΦ, Complex.coe_smul, smul_comm]

/-- The `Y`-valued sampled-network error on `K` is `V/N` times the `C(K;Y)`-norm of the centred
sum of the atoms. -/
theorem compactSupNorm_sampled_sub_eqVec (p : Measure Ω) [IsProbabilityMeasure p] (β : ℝ → ℂ)
    (π : Ω → H × ℝ) (h : Ω → Y) {Φ : Ω → (K →ᵇ Y)}
    (hΦ : ∀ ω (x : K), Φ ω x = β (⟪(π ω).1, (x : H)⟫ + (π ω).2) • h ω) (hint : Integrable Φ p)
    {V : ℝ} (hV : 0 ≤ V) {N : ℕ} (hN : 0 < N) (ω : Fin N → Ω) :
    compactSupNorm K (fun x =>
        ∑ j, β (⟪(π (ω j)).1, x⟫ + (π (ω j)).2) • (((V / N : ℝ) : ℂ) • h (ω j)) -
          V • ∫ ω', β (⟪(π ω').1, x⟫ + (π ω').2) • h ω' ∂p) =
      V / N * ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖ := by
  conv_rhs => rw [← abs_of_nonneg (div_nonneg hV (Nat.cast_nonneg N)), ← Real.norm_eq_abs,
    ← norm_smul]
  exact compactSupNorm_eq_norm_of_forall _ (smul_sum_sub_applyVec p β π h hΦ hint V hN ω)

/-- The `Y`-valued Rademacher complexity `𝔑^Y_N(K; p, β)` as the uniform average over the `2ᴺ`
sign vectors of `N⁻¹ 𝔼_θ ‖∑_j σ_j Φ(θ_j)‖_{C(K;Y)}`. -/
theorem rademacherComplexity_eq_sum_signsVec [MeasurableSpace H] (N : ℕ)
    (p : Measure (H × ℝ)) [IsProbabilityMeasure p] (β : ℝ → ℂ) (h : H × ℝ → Y)
    {Φ : H × ℝ → (K →ᵇ Y)}
    (hΦ : ∀ θ (x : K), Φ θ x = β (⟪θ.1, (x : H)⟫ + θ.2) • h θ) (hint : Integrable Φ p) :
    rademacherComplexity N K p β h =
      (N : ℝ)⁻¹ * ((2 ^ N : ℝ)⁻¹ *
        ∑ σ : Signs N, ∫ θ, ‖∑ j, signVector σ j • Φ (θ j)‖ ∂sampleLaw N p) := by
  have hpt : ∀ z : (Fin N → H × ℝ) × (Fin N → ℝ),
      compactSupNorm K (fun x => (N : ℂ)⁻¹ •
        ∑ j, ((z.2 j : ℝ) : ℂ) • (β (⟪(z.1 j).1, x⟫ + (z.1 j).2) • h (z.1 j))) =
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖ := by
    intro z
    have hNinv : |(N : ℝ)⁻¹| = (N : ℝ)⁻¹ := abs_of_nonneg (by positivity)
    rw [← hNinv, ← Real.norm_eq_abs, ← norm_smul]
    refine compactSupNorm_eq_norm_of_forall _ fun x => ?_
    have hcast : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.coe_smul]
    show (N : ℝ)⁻¹ • (∑ j, z.2 j • Φ (z.1 j)) x = _
    rw [BoundedContinuousFunction.coe_sum, Finset.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.coe_smul]
    show (N : ℝ)⁻¹ • (z.2 j • Φ (z.1 j) x) = _
    rw [hΦ]
  have hfun : (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) => compactSupNorm K (fun x => (N : ℂ)⁻¹ •
        ∑ j, ((z.2 j : ℝ) : ℂ) • (β (⟪(z.1 j).1, x⟫ + (z.1 j).2) • h (z.1 j)))) =
      fun z => (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖ := funext hpt
  have hΦj : ∀ j, Integrable (fun θ : Fin N → H × ℝ => Φ (θ j)) (sampleLaw N p) := fun j =>
    (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hint
  have hfst : MeasurePreserving Prod.fst ((sampleLaw N p).prod (rademacherMeasure N))
      (sampleLaw N p) := ⟨measurable_fst, Measure.fst_prod⟩
  have hsnd : MeasurePreserving Prod.snd ((sampleLaw N p).prod (rademacherMeasure N))
      (rademacherMeasure N) := ⟨measurable_snd, Measure.snd_prod⟩
  have hae : ∀ᵐ z ∂((sampleLaw N p).prod (rademacherMeasure N)), ∀ j, z.2 j = 1 ∨ z.2 j = -1 :=
    ae_of_ae_map measurable_snd.aemeasurable
      (by rw [hsnd.map_eq]; exact ae_rademacherMeasure_forall N)
  have hmeas : AEStronglyMeasurable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) =>
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖) ((sampleLaw N p).prod (rademacherMeasure N)) := by
    refine AEStronglyMeasurable.const_mul ?_ _
    have hsum := Finset.aestronglyMeasurable_sum (μ := (sampleLaw N p).prod (rademacherMeasure N))
      Finset.univ (f := fun j (z : (Fin N → H × ℝ) × (Fin N → ℝ)) => z.2 j • Φ (z.1 j))
      fun j _ => ((measurable_pi_apply j).comp measurable_snd).aestronglyMeasurable.smul
        ((hΦj j).aestronglyMeasurable.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving)
    exact (hsum.congr (Eventually.of_forall fun z => Finset.sum_apply z Finset.univ _)).norm
  have hbound : Integrable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) => (N : ℝ)⁻¹ * ∑ j, ‖Φ (z.1 j)‖)
      ((sampleLaw N p).prod (rademacherMeasure N)) :=
    (hfst.integrable_comp_of_integrable (integrable_finsetSum Finset.univ
      (f := fun j (θ : Fin N → H × ℝ) => ‖Φ (θ j)‖) fun j _ => (hΦj j).norm)).const_mul _
  have hintprod : Integrable (fun z : (Fin N → H × ℝ) × (Fin N → ℝ) =>
      (N : ℝ)⁻¹ * ‖∑ j, z.2 j • Φ (z.1 j)‖) ((sampleLaw N p).prod (rademacherMeasure N)) := by
    refine hbound.mono' hmeas ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      (by positivity)
    rw [norm_smul, Real.norm_eq_abs]
    rcases hz j with h1 | h1 <;> simp [h1]
  unfold rademacherComplexity
  rw [hfun, rademacherMeasure_eq, integral_prod_pi_rademacherSign _ _ hintprod]
  simp_rw [integral_const_mul]
  rw [smul_eq_mul, ← Finset.mul_sum]
  ring

end VectorSampling


/-! ### The Rademacher bound for a `Y`-valued coefficient measure with a density -/

section VectorDensityRademacher

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] {K : Set H}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The phase of a `Y`-valued coefficient density is measurable for the parameter law. -/
theorem aestronglyMeasurable_densityPhaseVec {Θ : Type*} [MeasurableSpace Θ] {lam : Measure Θ}
    {γ : Θ → Y} (hγ : Integrable γ lam) :
    AEStronglyMeasurable (densityPhase γ) (densityLaw lam γ) := by
  have h1 : AEStronglyMeasurable (densityPhase γ) lam :=
    (hγ.aestronglyMeasurable.norm.aemeasurable.inv).aestronglyMeasurable.smul
      hγ.aestronglyMeasurable
  exact h1.mono_ac (densityLaw_absolutelyContinuous lam γ)

/-- The `C(K;Y)`-valued atoms of a `Y`-valued coefficient measure with a density are Bochner
integrable. -/
theorem integrable_density_atomVec (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → Y} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) :
    Integrable (fun θ => ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ, densityPhase γ θ))
      (densityLaw lam γ) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  exact integrable_ridgeAtomVec hK hβ (densityLaw lam γ) measurable_id
    (aestronglyMeasurable_densityPhaseVec hγ)
    (Eventually.of_forall fun θ => norm_densityPhase_le_one γ θ) hM

/-- The error of the sampled network of a `Y`-valued coefficient density on `K`, as `V/N` times
the `C(K;Y)`-norm of the centred sum of the atoms. -/
theorem compactSupNorm_densitySampledNetwork_sub_eqVec (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → Y} (hγ : Integrable γ lam)
    (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) :
    compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x) =
      densityWeight lam γ / N *
        ‖∑ j, ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ j, densityPhase γ (θ j)) -
          (N : ℝ) • ∫ θ', ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ', densityPhase γ θ')
            ∂densityLaw lam γ‖ := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  calc compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
      = compactSupNorm K (fun x =>
          ∑ j, (β (⟪(id (θ j)).1, x⟫ + (id (θ j)).2) : ℂ) •
              (((densityWeight lam γ / N : ℝ) : ℂ) • densityPhase γ (θ j)) -
            densityWeight lam γ • ∫ θ', (β (⟪(id θ').1, x⟫ + (id θ').2) : ℂ) •
              densityPhase γ θ' ∂densityLaw lam γ) := by
        refine compactSupNorm_congr fun x _ => ?_
        rw [show integralNetworkDensity (fun t => (β t : ℂ)) lam γ x =
            densityWeight lam γ • ∫ θ', (β (⟪θ'.1, x⟫ + θ'.2) : ℂ) • densityPhase γ θ'
              ∂densityLaw lam γ from
          (densityWeight_smul_integral_smul_densityPhase hγ
            fun θ' => (β (⟪θ'.1, x⟫ + θ'.2) : ℂ)).symm]
        simp only [densitySampledNetwork, sampledNetwork, finiteNetwork, id]
    _ = _ := compactSupNorm_sampled_sub_eqVec (densityLaw lam γ) (fun t => (β t : ℂ)) id
        (densityPhase γ) (fun θ' x => rfl) (integrable_density_atomVec hK hβ hγ hV hM)
        (densityWeight_nonneg lam γ) hN θ

/-- **The vector-valued Rademacher bound of Corollary `cor:vector-rates`(ii)** for a coefficient
measure with a density: the mean compact-open error of the sampled network of `γ λ` is at most
`2V 𝔑^Y_N(K; p, β)`. -/
theorem integral_compactSupNorm_densitySampledNetwork_sub_le_rademacherVec (hK : IsCompact K)
    {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → Y}
    (hγ : Integrable γ lam)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) :
    ∫ θ, compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
            integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
        ∂sampleLaw N (densityLaw lam γ) ≤
      2 * densityWeight lam γ *
        rademacherComplexity N K (densityLaw lam γ) (fun t => (β t : ℂ)) (densityPhase γ) := by
  by_cases hV : densityWeight lam γ = 0
  · rw [densityLaw_eq_zero hγ hV, sampleLaw_zero hN, integral_zero_measure, hV]
    simp
  haveI := isProbabilityMeasure_densityLaw hγ hV
  set Φ : H × ℝ → (K →ᵇ Y) := fun θ =>
    ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ, densityPhase γ θ) with hΦdef
  have hint : Integrable Φ (densityLaw lam γ) := integrable_density_atomVec hK hβ hγ hV hM
  have hΦ : ∀ θ (x : K), Φ θ x = (β (⟪θ.1, (x : H)⟫ + θ.2) : ℂ) • densityPhase γ θ :=
    fun _ _ => rfl
  have hsym := integral_norm_sum_sub_le (densityLaw lam γ) hint (signVector (N := N))
    (fun _ => (2 ^ N : ℝ)⁻¹) (fun _ => by positivity) (sum_signs_inv_pow_two N)
    fun σ j => signVector_eq_one_or_neg_one σ j
  rw [rademacherComplexity_eq_sum_signsVec N (densityLaw lam γ) (fun t => (β t : ℂ))
    (densityPhase γ) hΦ hint]
  calc ∫ θ, compactSupNorm K (fun x =>
          densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
            integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
        ∂sampleLaw N (densityLaw lam γ)
      = ∫ θ, densityWeight lam γ / N *
          ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂densityLaw lam γ‖
          ∂sampleLaw N (densityLaw lam γ) :=
        integral_congr_ae (Eventually.of_forall
          (compactSupNorm_densitySampledNetwork_sub_eqVec hK hβ hγ hV hM hN))
    _ = densityWeight lam γ / N *
          ∫ θ, ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂densityLaw lam γ‖
            ∂sampleLaw N (densityLaw lam γ) := integral_const_mul _ _
    _ ≤ densityWeight lam γ / N * (2 * ∑ σ : Signs N, (2 ^ N : ℝ)⁻¹ *
          ∫ θ, ‖∑ j, signVector σ j • Φ (θ j)‖ ∂sampleLaw N (densityLaw lam γ)) :=
        mul_le_mul_of_nonneg_left hsym
          (div_nonneg (densityWeight_nonneg lam γ) (Nat.cast_nonneg N))
    _ = _ := by
        rw [← Finset.mul_sum]
        ring

end VectorDensityRademacher

/-! ### Theorem `thm:D` for `Y`-valued targets -/

section UniversalVec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {K : Set H}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The `Y`-valued target with a density regular along rays is the integral network of the
explicit coefficient; Theorem `thm:A`(iii) without the Lipschitz hypothesis on the
activation. -/
theorem spectralTarget_eq_integralNetworkDensityVec (ν : Measure H) [SigmaFinite ν] {α : ℝ}
    (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ) {I : Set ℝ}
    (hI : IsFrequencyWindow ρ I) {β : TemperedDistribution ℝ ℂ} {b : ℝ → ℝ}
    (hβ : IsTemperedFunction β b) {G : H → Y} (hG : IsRegularAlongRays ν I G) (x : H) :
    temperedAdmissibilityConst α β ρ • spectralTarget ν G x =
      integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
        (coefficientFormulaVec ρ G) x := by
  have hint : Integrable (fun θ : H × ℝ =>
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G θ) (ν.prod volume) := by
    refine (integrable_prod_smul_coefficientFormulaVec hρ hI hG hβ.continuous
      hβ.polynomialGrowth x).congr (Eventually.of_forall fun θ => ?_)
    show (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G (θ.1, θ.2) =
      (b (⟪θ.1, x⟫ + θ.2) : ℂ) • coefficientFormulaVec ρ G θ
    rw [Prod.mk.eta]
  rw [← integral_integral_smul_coefficientFormulaVec_activation hν hρ hI hG hβ x,
    integralNetworkDensity, parameterMeasure, integral_prod _ hint]

/-- The centred sum of `C(K;Y)`-valued atoms is an integrable function of the sample. -/
theorem integrable_norm_sum_subVec {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] {Φ : Ω → (K →ᵇ Y)} (hint : Integrable Φ p) (N : ℕ) :
    Integrable (fun ω : Fin N → Ω => ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖)
      (sampleLaw N p) :=
  ((integrable_finsetSum Finset.univ (f := fun j (ω : Fin N → Ω) => Φ (ω j)) fun j _ =>
    (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hint).sub
    (integrable_const _)).norm

/-- The compact-open error of the sampled network of a `Y`-valued coefficient density is an
integrable function of the sample. -/
theorem integrable_compactSupNorm_densitySampledNetwork_subVec (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) :
    Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x))
      (sampleLaw N (densityLaw lam γ)) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  exact ((integrable_norm_sum_subVec (densityLaw lam γ)
    (integrable_density_atomVec hK hβ hγ hV hM) N).const_mul (densityWeight lam γ / N)).congr
    (Eventually.of_forall fun θ =>
      (compactSupNorm_densitySampledNetwork_sub_eqVec hK hβ hγ hV hM hN θ).symm)

/-- The error of the sampled network of a `Y`-valued coefficient density at a point of `K` is
bounded by its compact sup norm. -/
theorem norm_densitySampledNetwork_sub_le_compactSupNormVec (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) {lam : Measure (H × ℝ)} {γ : H × ℝ → Y}
    (hγ : Integrable γ lam) (hV : densityWeight lam γ ≠ 0)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (densityLaw lam γ)) {N : ℕ}
    (hN : 0 < N) (θ : Fin N → H × ℝ) {x : H} (hx : x ∈ K) :
    ‖densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
        integralNetworkDensity (fun t => (β t : ℂ)) lam γ x‖ ≤
      compactSupNorm K (fun x =>
        densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
          integralNetworkDensity (fun t => (β t : ℂ)) lam γ x) := by
  haveI := isProbabilityMeasure_densityLaw hγ hV
  have hΦint : Integrable
      (fun θ' => ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ', densityPhase γ θ'))
      (densityLaw lam γ) := integrable_density_atomVec hK hβ hγ hV hM
  refine le_compactSupNorm_of_forall (g := fun x =>
      densitySampledNetwork (fun t => (β t : ℂ)) lam γ θ x -
        integralNetworkDensity (fun t => (β t : ℂ)) lam γ x)
    ((densityWeight lam γ / N : ℝ) •
      (∑ j, ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ j, densityPhase γ (θ j)) -
        (N : ℝ) • ∫ θ', ridgeAtomVec hK (continuous_ofReal_comp hβ) (θ', densityPhase γ θ')
          ∂densityLaw lam γ))
    (fun y => ?_) hx
  refine (smul_sum_sub_applyVec (densityLaw lam γ) (fun t => (β t : ℂ)) id
    (densityPhase γ) (fun θ' x => rfl) hΦint (densityWeight lam γ) hN θ y).trans ?_
  rw [show integralNetworkDensity (fun t => (β t : ℂ)) lam γ (y : H) =
      densityWeight lam γ • ∫ θ', ((β (⟪θ'.1, (y : H)⟫ + θ'.2) : ℝ) : ℂ) • densityPhase γ θ'
        ∂densityLaw lam γ from
    (densityWeight_smul_integral_smul_densityPhase hγ
      fun θ' => ((β (⟪θ'.1, (y : H)⟫ + θ'.2) : ℝ) : ℂ)).symm]
  simp only [densitySampledNetwork, sampledNetwork, finiteNetwork, id]

/-- **Theorem `thm:D`, vector-valued**, for a direction measure that is finite on bounded sets:
a constructive universal approximation of a continuous `f : H → Y` with the vector-valued
compact-open rate `2V 𝔑^Y_N(K; p, β)` of Corollary `cor:vector-rates`(ii). -/
theorem exists_spectralDensity_universal_approx_vec (ν : Measure H) [SigmaFinite ν]
    [ν.IsOpenPosMeasure] (hfin : ∀ R : ℝ, ν (closedBall (0 : H) R) < ⊤) {α : ℝ}
    (hν : IsHomogeneous α ν) (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (ρ : SchwartzMap ℝ ℝ) (hρ : IsBandPass ρ)
    (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ) (hI : IsFrequencyWindow ρ I)
    {f : H → Y} (hf : Continuous f) {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : H → Y, IsRegularAlongRays ν I G ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ R : ℝ, ∀ ξ : H, R < ‖ξ‖ → G ξ = 0) ∧
      compactSupNorm K (fun x => f x - spectralTarget ν G x) < ε ∧
      spectralTarget ν G =
        integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
          (coefficientFormulaVec ρ G) ∧
      (∀ m : ℕ, Integrable
        (fun θ : H × ℝ => (1 + ‖θ.1‖ + |θ.2|) ^ m * ‖coefficientFormulaVec ρ G θ‖)
        (parameterMeasure ν)) ∧
      (∀ L : ℝ≥0, LipschitzWith L b → ∀ N : ℕ, 0 < N →
        ∫ θ, compactSupNorm K (fun x =>
              f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) ≤
          ε + 2 * densityWeight (parameterMeasure ν) (coefficientFormulaVec ρ G) *
            rademacherComplexity N K
              (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))
              (fun t => (b t : ℂ)) (densityPhase (coefficientFormulaVec ρ G))) := by
  obtain ⟨G, hGreg, hGsmooth, hGsupp, hGapp⟩ :=
    exists_isRegularAlongRays_norm_sub_spectralTarget_leVec ν hfin hI.isCompact hI.zero_notMem
      hf hK (half_pos hε)
  have hγ : Integrable (coefficientFormulaVec ρ G) (parameterMeasure ν) :=
    integrable_coefficientFormulaVec hρ hI hGreg
  have hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2)
      (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) :=
    integrable_sq_densityLaw_coefficientFormulaVec hρ hI hGreg
  have hgeq : spectralTarget ν G =
      integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
        (coefficientFormulaVec ρ G) := by
    funext x
    rw [← spectralTarget_eq_integralNetworkDensityVec ν hν ρ hρ hI hβ hGreg x, hC, one_smul]
  have hA : ∀ x ∈ K, ‖f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
      (coefficientFormulaVec ρ G) x‖ ≤ ε / 2 := by
    intro x hx
    rw [← hgeq]
    exact hGapp x hx
  refine ⟨G, hGreg, hGsmooth, hGsupp, ?_, hgeq, ?_, ?_⟩
  · exact lt_of_le_of_lt (compactSupNorm_le (by positivity) hGapp) (by linarith)
  · intro m
    exact integrable_moment_norm_coefficientFormulaVec hρ hI hGreg m
  · intro L hb N hN
    set W : ℝ := densityWeight (parameterMeasure ν) (coefficientFormulaVec ρ G) with hWdef
    set R : ℝ := rademacherComplexity N K
      (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))
      (fun t => (b t : ℂ)) (densityPhase (coefficientFormulaVec ρ G)) with hRdef
    by_cases hV : W = 0
    · rw [densityLaw_eq_zero hγ hV, sampleLaw_zero hN, integral_zero_measure, hV, mul_zero,
        zero_mul, add_zero]
      exact hε.le
    · haveI := isProbabilityMeasure_densityLaw hγ hV
      have hDint := integrable_compactSupNorm_densitySampledNetwork_subVec hK hb hγ hV hM hN
      have hptw : ∀ θ : Fin N → H × ℝ,
          compactSupNorm K (fun x => f x - densitySampledNetwork (fun t => (b t : ℂ))
              (parameterMeasure ν) (coefficientFormulaVec ρ G) θ x) ≤
            ε / 2 + compactSupNorm K (fun x =>
              densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x -
              integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) x) := by
        intro θ
        refine compactSupNorm_le (add_nonneg (by positivity) (compactSupNorm_nonneg _ _))
          fun x hx => ?_
        calc ‖f x - densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x‖
            = ‖(f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormulaVec ρ G) x) +
                (integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormulaVec ρ G) x -
                  densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                    (coefficientFormulaVec ρ G) θ x)‖ := by
              rw [sub_add_sub_cancel]
          _ ≤ ‖f x - integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormulaVec ρ G) x‖ +
                ‖integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                  (coefficientFormulaVec ρ G) x -
                  densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                    (coefficientFormulaVec ρ G) θ x‖ := norm_add_le _ _
          _ ≤ ε / 2 + _ := by
              refine add_le_add (hA x hx) ?_
              rw [norm_sub_rev]
              exact norm_densitySampledNetwork_sub_le_compactSupNormVec hK hb hγ hV hM hN θ hx
      calc ∫ θ, compactSupNorm K (fun x => f x - densitySampledNetwork (fun t => (b t : ℂ))
              (parameterMeasure ν) (coefficientFormulaVec ρ G) θ x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G))
          ≤ ∫ θ, (ε / 2 + compactSupNorm K (fun x =>
              densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x -
              integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) x))
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => compactSupNorm_nonneg _ _)
              (Integrable.add (integrable_const _) hDint) (Eventually.of_forall hptw)
        _ = ε / 2 + ∫ θ, compactSupNorm K (fun x =>
              densitySampledNetwork (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) θ x -
              integralNetworkDensity (fun t => (b t : ℂ)) (parameterMeasure ν)
                (coefficientFormulaVec ρ G) x)
            ∂sampleLaw N (densityLaw (parameterMeasure ν) (coefficientFormulaVec ρ G)) := by
            rw [integral_add (integrable_const _) hDint, integral_const]
            simp
        _ ≤ ε / 2 + 2 * W * R :=
            add_le_add le_rfl
              (integral_compactSupNorm_densitySampledNetwork_sub_le_rademacherVec hK hb hγ hM hN)
        _ ≤ ε + 2 * W * R := by linarith

end UniversalVec

end OperatorRidgelet
