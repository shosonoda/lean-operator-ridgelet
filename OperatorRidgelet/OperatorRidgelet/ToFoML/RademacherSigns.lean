import FoML.Rademacher.Symmetrization
import FoML.Learning.Contraction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Rademacher signs as a product measure, and FoML's Rademacher tools over a set

FoML's Rademacher averages are finite averages over the sign vectors
`Signs N = Fin N → {-1, 1}`.  This file connects them with the law of `N` independent
Rademacher signs represented as real numbers, the product measure
`Measure.pi (fun _ : Fin N => rademacherSign)` on `Fin N → ℝ` with `rademacherSign = (δ₋₁ + δ₁)/2`:

* `signVector σ : Fin N → ℝ` is the real sign vector of `σ : Signs N`;
* `pi_rademacherSign_eq`: the product law is the uniform average `2⁻ᴺ ∑_σ δ_{signVector σ}`;
* `integral_pi_rademacherSign`, `integral_prod_pi_rademacherSign`: integrals against the
  product law, and against its product with another measure, are the corresponding finite
  averages;
* `sum_norm_sq_sum_signVector_smul`: the Hilbert-space identity
  `∑_σ ‖∑_j σ_j v_j‖² = 2ᴺ ∑_j ‖v_j‖²`;
* `sum_sSup_abs_contraction`: the contraction principle (Ledoux–Talagrand, Theorem 4.12) for
  the suprema over an arbitrary set `K` of `|∑_j σ_j φ_j(u_j(x))|`, with `φ_j` Lipschitz and
  `φ_j(0) = 0`, deduced from FoML's finite-class contraction theorem by choosing finitely many
  near-maximizers.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped ENNReal

/-! ### Sign vectors -/

/-- The real sign vector `(σ_1, …, σ_N) ∈ {-1, 1}^N ⊂ ℝ^N` of `σ : Signs N`. -/
def signVector {N : ℕ} (σ : Signs N) : Fin N → ℝ := fun j => ((σ j : ℤ) : ℝ)

/-- A real sign vector evaluates by coercing the corresponding integer sign. -/
theorem signVector_apply {N : ℕ} (σ : Signs N) (j : Fin N) :
    signVector σ j = ((σ j : ℤ) : ℝ) := rfl

/-- Every coordinate of a real sign vector is one or minus one. -/
theorem signVector_eq_one_or_neg_one {N : ℕ} (σ : Signs N) (j : Fin N) :
    signVector σ j = 1 ∨ signVector σ j = -1 := by
  have h := (σ j).property
  rw [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Or.inr (by simp [signVector, h])
  · exact Or.inl (by simp [signVector, h])

/-- Every coordinate of a real sign vector has absolute value one. -/
theorem abs_signVector {N : ℕ} (σ : Signs N) (j : Fin N) : |signVector σ j| = 1 := by
  rcases signVector_eq_one_or_neg_one σ j with h | h <;> simp [h]

/-- Every coordinate of a real sign vector has square one. -/
theorem sq_signVector {N : ℕ} (σ : Signs N) (j : Fin N) : signVector σ j ^ 2 = 1 := by
  rcases signVector_eq_one_or_neg_one σ j with h | h <;> simp [h]

/-- The all-positive sign vector witnesses nonemptiness of the sign space. -/
instance instNonemptySigns (N : ℕ) : Nonempty (Signs N) := ⟨fun _ => ⟨1, by simp⟩⟩

/-! ### The law of the signs as a product measure -/

/-- The law `(δ₋₁ + δ₁)/2` of one Rademacher sign, as a measure on `ℝ`. -/
def rademacherSign : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

/-- The symmetric two-point sign law has total mass one. -/
instance instIsProbabilityMeasureRademacherSign : IsProbabilityMeasure rademacherSign := by
  refine ⟨?_⟩
  rw [rademacherSign, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The law of `N` independent Rademacher signs is the uniform average of the Dirac masses at
the `2ᴺ` sign vectors. -/
theorem pi_rademacherSign_eq (N : ℕ) :
    (Measure.pi fun _ : Fin N => rademacherSign) =
      (2 ^ N : ℝ≥0∞)⁻¹ • ∑ σ : Signs N, Measure.dirac (signVector σ) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : ∀ σ : Signs N, Measure.dirac (signVector σ) (Set.pi Set.univ s) =
      ∏ j, (s j).indicator (fun _ => (1 : ℝ≥0∞)) (signVector σ j) := by
    intro σ
    classical
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
    simp only [Set.indicator_apply]
    rw [Fintype.prod_boole]
    by_cases h : signVector σ ∈ Set.univ.pi s
    · rw [if_pos h, if_pos (Set.mem_univ_pi.mp h)]
      rfl
    · rw [if_neg h, if_neg fun h' => h (Set.mem_univ_pi.mpr h')]
  have hsign : ∀ j, rademacherSign (s j) =
      2⁻¹ * ∑ v : ({-1, 1} : Finset ℤ), (s j).indicator (fun _ => (1 : ℝ≥0∞)) ((v : ℤ) : ℝ) := by
    intro j
    rw [rademacherSign, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ (hs j),
      Measure.dirac_apply' _ (hs j), smul_eq_mul,
      Finset.sum_coe_sort ({-1, 1} : Finset ℤ)
        (fun z : ℤ => (s j).indicator (fun _ => (1 : ℝ≥0∞)) ((z : ℤ) : ℝ)),
      Finset.sum_pair (by norm_num)]
    push_cast
    rfl
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp_rw [hbox, hsign]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- Integration against the law of `N` Rademacher signs is the uniform average over the sign
vectors. -/
theorem integral_pi_rademacherSign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (N : ℕ) (g : (Fin N → ℝ) → E) :
    ∫ ε, g ε ∂(Measure.pi fun _ : Fin N => rademacherSign) =
      (2 ^ N : ℝ)⁻¹ • ∑ σ : Signs N, g (signVector σ) := by
  rw [pi_rademacherSign_eq, integral_smul_measure,
    integral_finsetSum_measure fun σ _ => (integrable_const _).congr (ae_eq_dirac g).symm,
    Finset.sum_congr rfl fun σ _ => integral_dirac g (signVector σ)]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- A property holding almost everywhere for the law of `N` Rademacher signs holds at every
sign vector. -/
theorem of_ae_pi_rademacherSign {N : ℕ} {P : (Fin N → ℝ) → Prop}
    (h : ∀ᵐ ε ∂(Measure.pi fun _ : Fin N => rademacherSign), P ε) (σ : Signs N) :
    P (signVector σ) := by
  rw [pi_rademacherSign_eq, ← Measure.sum_fintype, ae_iff, Measure.smul_apply,
    smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  · have h' := (Measure.ae_sum_iff.mp (ae_iff.mpr h)) σ
    rwa [ae_dirac_eq, Filter.eventually_pure] at h'

/-- Fubini for the product of a measure with the law of `N` Rademacher signs: the integral is
the uniform average over the sign vectors of the integrals of the sections. -/
theorem integral_prod_pi_rademacherSign {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure Ω) [SFinite μ] (N : ℕ)
    {g : Ω × (Fin N → ℝ) → E}
    (hg : Integrable g (μ.prod (Measure.pi fun _ : Fin N => rademacherSign))) :
    ∫ z, g z ∂(μ.prod (Measure.pi fun _ : Fin N => rademacherSign)) =
      (2 ^ N : ℝ)⁻¹ • ∑ σ : Signs N, ∫ ω, g (ω, signVector σ) ∂μ := by
  have hσ : ∀ σ : Signs N, Integrable (fun ω => g (ω, signVector σ)) μ :=
    of_ae_pi_rademacherSign hg.prod_left_ae
  rw [integral_prod _ hg]
  simp_rw [integral_pi_rademacherSign]
  rw [integral_smul, integral_finsetSum _ fun σ _ => hσ σ]

/-! ### The Hilbert-space Rademacher identity -/

/-- `∑_σ ‖∑_j σ_j v_j‖² = 2ᴺ ∑_j ‖v_j‖²` in a real inner product space. -/
theorem sum_norm_sq_sum_signVector_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (v : Fin N → E) :
    ∑ σ : Signs N, ‖∑ j, signVector σ j • v j‖ ^ 2 = 2 ^ N * ∑ j, ‖v j‖ ^ 2 := by
  have hexp : ∀ σ : Signs N, ‖∑ j, signVector σ j • v j‖ ^ 2 =
      ∑ j, ∑ k, signVector σ j * signVector σ k * inner ℝ (v j) (v k) := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have horth : ∀ j k : Fin N, ∑ σ : Signs N, signVector σ j * signVector σ k =
      if j = k then (2 : ℝ) ^ N else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      simp only [← sq, sq_signVector, Finset.sum_const, Finset.card_univ, Signs.card,
        nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    · exact rademacher_orthogonality N j k hjk
  calc ∑ j, ∑ σ : Signs N, ∑ k, signVector σ j * signVector σ k * inner ℝ (v j) (v k)
      = ∑ j, ∑ k, (∑ σ : Signs N, signVector σ j * signVector σ k) * inner ℝ (v j) (v k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ j, (2 : ℝ) ^ N * ‖v j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp_rw [horth, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), real_inner_self_eq_norm_sq]
    _ = 2 ^ N * ∑ j, ‖v j‖ ^ 2 := by rw [Finset.mul_sum]

/-! ### The contraction principle over a set -/

/-- FoML's finite-class contraction theorem, without the normalization `N⁻¹`. -/
theorem sum_iSup_abs_contraction {H : Type*} [Fintype H] [Nonempty H] {N : ℕ}
    (u : H → Fin N → ℝ) (φ : Fin N → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ0 : ∀ j, φ j 0 = 0)
    (hφ : ∀ j x y, |φ j x - φ j y| ≤ L * |x - y|) :
    ∑ σ : Signs N, ⨆ h, |∑ j, signVector σ j * φ j (u h j)| ≤
      2 * L * ∑ σ : Signs N, ⨆ h, |∑ j, signVector σ j * u h j| := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have h := empiricalRademacherComplexity_contraction_finite N u (fun j t => φ j t)
    (id : Fin N → Fin N) hL (fun j => hφ0 j) (fun j x y => hφ j x y)
  have hpull : ∀ (F : H → ℝ), (⨆ h, |(N : ℝ)⁻¹ * F h|) = (N : ℝ)⁻¹ * ⨆ h, |F h| := by
    intro F
    rw [Real.mul_iSup_of_nonneg (by positivity)]
    congr 1
    ext h
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hconv : ∀ (F : H → Fin N → ℝ), empiricalRademacherComplexity N F id =
      (2 ^ N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ σ : Signs N, ⨆ h, |∑ j, signVector σ j * F h j|) := by
    intro F
    unfold empiricalRademacherComplexity
    rw [Signs.card]
    simp_rw [hpull, id_eq]
    rw [← Finset.mul_sum]
    push_cast
    rfl
  rw [hconv, hconv] at h
  set S1 := ∑ σ : Signs N, ⨆ h, |∑ j, signVector σ j * φ j (u h j)| with hS1
  set S2 := ∑ σ : Signs N, ⨆ h, |∑ j, signVector σ j * u h j| with hS2
  have hc : 0 < (2 ^ N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by positivity
  have key : (2 ^ N : ℝ)⁻¹ * (N : ℝ)⁻¹ * S1 ≤ (2 ^ N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (2 * L * S2) := by
    calc (2 ^ N : ℝ)⁻¹ * (N : ℝ)⁻¹ * S1 = (2 ^ N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * S1) := by ring
      _ ≤ 2 * L * ((2 ^ N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * S2)) := h
      _ = (2 ^ N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (2 * L * S2) := by ring
  exact le_of_mul_le_mul_left key hc

/-- **Contraction principle** over an arbitrary set: for `L`-Lipschitz `φ_j` with `φ_j(0) = 0`
and functions `u_j` bounded on `K`,
`∑_σ sup_{x ∈ K} |∑_j σ_j φ_j(u_j(x))| ≤ 2 L ∑_σ sup_{x ∈ K} |∑_j σ_j u_j(x)|`. -/
theorem sum_sSup_abs_contraction {X : Type*} (K : Set X) {N : ℕ} (u : Fin N → X → ℝ)
    (φ : Fin N → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ0 : ∀ j, φ j 0 = 0)
    (hφ : ∀ j x y, |φ j x - φ j y| ≤ L * |x - y|)
    (hbdd : ∀ j, BddAbove ((fun x => |u j x|) '' K)) :
    ∑ σ : Signs N, sSup ((fun x => |∑ j, signVector σ j * φ j (u j x)|) '' K) ≤
      2 * L * ∑ σ : Signs N, sSup ((fun x => |∑ j, signVector σ j * u j x|) '' K) := by
  classical
  rcases K.eq_empty_or_nonempty with hK | hK
  · simp [hK]
  choose M hM using hbdd
  have hφu : ∀ j x, |φ j (u j x)| ≤ L * |u j x| := fun j x => by
    have := hφ j (u j x) 0
    rwa [hφ0, sub_zero, sub_zero] at this
  have hbddφ : ∀ σ : Signs N,
      BddAbove ((fun x => |∑ j, signVector σ j * φ j (u j x)|) '' K) := by
    intro σ
    refine ⟨L * ∑ j, M j, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    calc |∑ j, signVector σ j * φ j (u j x)| ≤ ∑ j, |signVector σ j * φ j (u j x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |φ j (u j x)| := by simp [abs_mul, abs_signVector]
      _ ≤ ∑ j, L * M j := Finset.sum_le_sum fun j _ =>
          (hφu j x).trans (mul_le_mul_of_nonneg_left (hM j ⟨x, hx, rfl⟩) hL)
      _ = L * ∑ j, M j := by rw [Finset.mul_sum]
  have hbddu : ∀ σ : Signs N, BddAbove ((fun x => |∑ j, signVector σ j * u j x|) '' K) := by
    intro σ
    refine ⟨∑ j, M j, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    calc |∑ j, signVector σ j * u j x| ≤ ∑ j, |signVector σ j * u j x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |u j x| := by simp [abs_mul, abs_signVector]
      _ ≤ ∑ j, M j := Finset.sum_le_sum fun j _ => hM j ⟨x, hx, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε' : ℝ := ε / 2 ^ N with hε'
  have hε'pos : 0 < ε' := by positivity
  have hnear : ∀ σ : Signs N, ∃ x ∈ K,
      sSup ((fun x => |∑ j, signVector σ j * φ j (u j x)|) '' K) ≤
        |∑ j, signVector σ j * φ j (u j x)| + ε' := by
    intro σ
    obtain ⟨_, ⟨x, hx, rfl⟩, hy⟩ :=
      exists_lt_of_lt_csSup (hK.image _) (sub_lt_self _ hε'pos :
        sSup ((fun x => |∑ j, signVector σ j * φ j (u j x)|) '' K) - ε' < _)
    exact ⟨x, hx, by linarith⟩
  choose xσ hxσK hxσ using hnear
  let F : Finset X := Finset.univ.image xσ
  haveI : Nonempty F :=
    ⟨⟨xσ (Classical.arbitrary _), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩⟩
  have hF : ∀ x ∈ F, x ∈ K := by
    intro x hx
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hxσK σ
  have hfin := sum_iSup_abs_contraction (H := F) (fun h j => u j h) φ hL hφ0 hφ
  calc ∑ σ : Signs N, sSup ((fun x => |∑ j, signVector σ j * φ j (u j x)|) '' K)
      ≤ ∑ σ : Signs N, (|∑ j, signVector σ j * φ j (u j (xσ σ))| + ε') :=
        Finset.sum_le_sum fun σ _ => hxσ σ
    _ = ∑ σ : Signs N, |∑ j, signVector σ j * φ j (u j (xσ σ))| + ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Signs.card, nsmul_eq_mul,
          hε']
        congr 1
        push_cast
        field_simp
    _ ≤ ∑ σ : Signs N, (⨆ h : F, |∑ j, signVector σ j * φ j (u j h)|) + ε := by
        refine add_le_add (Finset.sum_le_sum fun σ _ => ?_) le_rfl
        exact le_ciSup (f := fun h : F => |∑ j, signVector σ j * φ j (u j h)|)
          (Finite.bddAbove_range _) ⟨xσ σ, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    _ ≤ 2 * L * ∑ σ : Signs N, (⨆ h : F, |∑ j, signVector σ j * u j h|) + ε :=
        add_le_add hfin le_rfl
    _ ≤ 2 * L * ∑ σ : Signs N, sSup ((fun x => |∑ j, signVector σ j * u j x|) '' K) + ε := by
        refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_)
          (mul_nonneg (by norm_num) hL)) le_rfl
        exact ciSup_le fun h => le_csSup (hbddu σ) ⟨h, hF h h.2, rfl⟩

end OperatorRidgelet
