import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import OperatorRidgelet.ToMathlib.MeasurePi

/-!
# Symmetrization of the empirical mean in a Banach space

For a probability measure `p` on `Ω`, a Bochner-integrable `Φ : Ω → E` with values in a normed
space, and the law `p^{⊗N} = Measure.pi (fun _ : Fin N => p)` of `N` independent samples
`ω_1, …, ω_N`, the **symmetrization inequality** `integral_norm_sum_sub_le` bounds the
deviation of `∑_j Φ(ω_j)` from its mean `N ∫ Φ dp` by twice the Rademacher average of any
finite family of sign vectors `s_σ ∈ {±1}^N` with weights `w_σ ≥ 0`, `∑_σ w_σ = 1`:

`∫ ‖∑_j Φ(ω_j) − N ∫ Φ dp‖ dp^{⊗N} ≤ 2 ∑_σ w_σ ∫ ‖∑_j s_σ(j) • Φ(ω_j)‖ dp^{⊗N}`.

The proof introduces an independent ghost sample `ω'`, uses Jensen's inequality
`‖∑_j (Φ(ω_j) − ∫ Φ)‖ ≤ ∫ ‖∑_j (Φ(ω_j) − Φ(ω'_j))‖ dp^{⊗N}(ω')`, and observes that exchanging
`ω_j` and `ω'_j` for the coordinates `j` with `s_σ(j) = −1` preserves `p^{⊗N} ⊗ p^{⊗N}`
(`measurePreserving_swapSample`), so that the double integral is unchanged when
`Φ(ω_j) − Φ(ω'_j)` is replaced by `s_σ(j) • (Φ(ω_j) − Φ(ω'_j))`; the triangle inequality
gives the factor two.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- The integral of a function of the first coordinate against a product with a probability
measure. -/
theorem integral_comp_fst_prod {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [IsProbabilityMeasure ν] {g : α → E} (hg : AEStronglyMeasurable g μ) :
    ∫ z, g z.1 ∂(μ.prod ν) = ∫ x, g x ∂μ := by
  have h : MeasurePreserving Prod.fst (μ.prod ν) μ := ⟨measurable_fst, Measure.fst_prod⟩
  conv_rhs => rw [← h.map_eq]
  rw [integral_map measurable_fst.aemeasurable (by rw [h.map_eq]; exact hg)]

/-- The integral of a function of the second coordinate against a product with a probability
measure. -/
theorem integral_comp_snd_prod {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [SFinite ν] {g : β → E} (hg : AEStronglyMeasurable g ν) :
    ∫ z, g z.2 ∂(μ.prod ν) = ∫ y, g y ∂ν := by
  have h : MeasurePreserving Prod.snd (μ.prod ν) ν := ⟨measurable_snd, Measure.snd_prod⟩
  conv_rhs => rw [← h.map_eq]
  rw [integral_map measurable_snd.aemeasurable (by rw [h.map_eq]; exact hg)]

/-- The measurable bijection of `(Fin N → Ω) × (Fin N → Ω)` exchanging, for the coordinates
`j` with `s j ≠ 1`, the entries of the two samples. -/
noncomputable def swapSample (s : Fin N → ℝ) :
    (Fin N → Ω) × (Fin N → Ω) ≃ᵐ (Fin N → Ω) × (Fin N → Ω) :=
  (MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin N)).symm.trans
    ((MeasurableEquiv.piCongrRight fun j =>
      if s j = 1 then MeasurableEquiv.refl (Ω × Ω) else MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin N)))

theorem swapSample_apply (s : Fin N → ℝ) (z : (Fin N → Ω) × (Fin N → Ω)) :
    swapSample s z = (fun j => if s j = 1 then z.1 j else z.2 j,
      fun j => if s j = 1 then z.2 j else z.1 j) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · show ((if s j = 1 then MeasurableEquiv.refl (Ω × Ω) else MeasurableEquiv.prodComm)
      (z.1 j, z.2 j)).1 = if s j = 1 then z.1 j else z.2 j
    split_ifs <;> rfl
  · show ((if s j = 1 then MeasurableEquiv.refl (Ω × Ω) else MeasurableEquiv.prodComm)
      (z.1 j, z.2 j)).2 = if s j = 1 then z.2 j else z.1 j
    split_ifs <;> rfl

/-- Exchanging entries between two independent samples of the same law preserves the joint
law `p^{⊗N} ⊗ p^{⊗N}`. -/
theorem measurePreserving_swapSample (p : Measure Ω) [IsProbabilityMeasure p]
    (s : Fin N → ℝ) :
    MeasurePreserving (swapSample s)
      ((Measure.pi fun _ : Fin N => p).prod (Measure.pi fun _ : Fin N => p))
      ((Measure.pi fun _ : Fin N => p).prod (Measure.pi fun _ : Fin N => p)) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin N) (fun _ => p) (fun _ => p)
  have h2 : MeasurePreserving (fun a : Fin N → Ω × Ω => fun j =>
      (if s j = 1 then MeasurableEquiv.refl (Ω × Ω) else MeasurableEquiv.prodComm) (a j))
      (Measure.pi fun _ : Fin N => p.prod p) (Measure.pi fun _ : Fin N => p.prod p) := by
    refine measurePreserving_pi _ _ fun j => ?_
    split_ifs
    · exact MeasurePreserving.id _
    · exact Measure.measurePreserving_swap
  unfold swapSample
  rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans]
  exact (h1.comp h2).comp (MeasurePreserving.symm _ h1)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Symmetrization inequality.**  For `N` independent samples `ω_j ∼ p` of a
Bochner-integrable `Φ`, and any finite family of sign vectors `s_σ ∈ {±1}^N` with weights
`w_σ ≥ 0` summing to one,
`∫ ‖∑_j Φ(ω_j) − N ∫ Φ dp‖ dp^{⊗N} ≤ 2 ∑_σ w_σ ∫ ‖∑_j s_σ(j) • Φ(ω_j)‖ dp^{⊗N}`. -/
theorem integral_norm_sum_sub_le (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → E}
    (hΦ : Integrable Φ p) {S : Type*} [Fintype S] (s : S → Fin N → ℝ) (w : S → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hw1 : ∑ σ, w σ = 1) (hs : ∀ σ j, s σ j = 1 ∨ s σ j = -1) :
    ∫ ω, ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ x, Φ x ∂p‖ ∂(Measure.pi fun _ : Fin N => p) ≤
      2 * ∑ σ, w σ * ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂(Measure.pi fun _ : Fin N => p) := by
  set μN : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => p with hμN
  haveI : IsProbabilityMeasure μN := by rw [hμN]; infer_instance
  have hΦj : ∀ j : Fin N, Integrable (fun ω : Fin N → Ω => Φ (ω j)) μN := fun j =>
    ((measurePreserving_eval (fun _ : Fin N => p) j).integrable_comp
      hΦ.aestronglyMeasurable).mpr hΦ
  set m : E := ∫ x, Φ x ∂p with hm
  have hfst : MeasurePreserving Prod.fst (μN.prod μN) μN := ⟨measurable_fst, Measure.fst_prod⟩
  have hsnd : MeasurePreserving Prod.snd (μN.prod μN) μN := ⟨measurable_snd, Measure.snd_prod⟩
  have hΦ1 : ∀ j, Integrable (fun z : (Fin N → Ω) × (Fin N → Ω) => Φ (z.1 j)) (μN.prod μN) :=
    fun j => (hfst.integrable_comp (hΦj j).aestronglyMeasurable).mpr (hΦj j)
  have hΦ2 : ∀ j, Integrable (fun z : (Fin N → Ω) × (Fin N → Ω) => Φ (z.2 j)) (μN.prod μN) :=
    fun j => (hsnd.integrable_comp (hΦj j).aestronglyMeasurable).mpr (hΦj j)
  -- the ghost-sample integrand
  set G : (Fin N → Ω) × (Fin N → Ω) → ℝ := fun z => ‖∑ j, (Φ (z.1 j) - Φ (z.2 j))‖ with hG
  have hGint : Integrable G (μN.prod μN) :=
    (integrable_finsetSum _ fun j _ => (hΦ1 j).sub (hΦ2 j)).norm
  -- Jensen's inequality with respect to the ghost sample
  have hjensen : ∀ ω : Fin N → Ω, ‖∑ j, Φ (ω j) - (N : ℝ) • m‖ ≤ ∫ ω', G (ω, ω') ∂μN := by
    intro ω
    have h1 : ∫ ω', ∑ j, (Φ (ω j) - Φ (ω' j)) ∂μN = ∑ j, Φ (ω j) - (N : ℝ) • m := by
      rw [integral_finsetSum Finset.univ
        (f := fun (j : Fin N) (ω' : Fin N → Ω) => Φ (ω j) - Φ (ω' j))
        fun j _ => (integrable_const _).sub (hΦj j)]
      have h2 : ∀ j : Fin N, ∫ ω', (Φ (ω j) - Φ (ω' j)) ∂μN = Φ (ω j) - m := by
        intro j
        rw [integral_sub (integrable_const _) (hΦj j), integral_const, probReal_univ, one_smul,
          hμN, integral_eval_pi p hΦ.aestronglyMeasurable j]
      simp_rw [h2]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ]
    rw [← h1]
    exact norm_integral_le_integral_norm _
  -- pass to the product of the two samples
  have hstep2 : ∫ ω, ‖∑ j, Φ (ω j) - (N : ℝ) • m‖ ∂μN ≤ ∫ z, G z ∂(μN.prod μN) := by
    rw [integral_prod _ hGint]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      hGint.integral_prod_left (Eventually.of_forall hjensen)
  -- exchanging entries between the two samples
  have hswap : ∀ σ, ∫ z, G z ∂(μN.prod μN) =
      ∫ z, ‖∑ j, s σ j • (Φ (z.1 j) - Φ (z.2 j))‖ ∂(μN.prod μN) := by
    intro σ
    rw [← (measurePreserving_swapSample p (s σ)).integral_comp' G]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hG, swapSample_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases hs σ j with h | h
    · simp [h]
    · have h' : s σ j ≠ 1 := by rw [h]; norm_num
      simp only [if_neg h']
      rw [h, neg_one_smul, neg_sub]
  -- the triangle inequality
  have htri : ∀ σ, ∫ z, ‖∑ j, s σ j • (Φ (z.1 j) - Φ (z.2 j))‖ ∂(μN.prod μN) ≤
      2 * ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN := by
    intro σ
    have hA : Integrable (fun z : (Fin N → Ω) × (Fin N → Ω) => ‖∑ j, s σ j • Φ (z.1 j)‖)
        (μN.prod μN) :=
      (integrable_finsetSum _ fun j _ => (hΦ1 j).smul (s σ j)).norm
    have hB : Integrable (fun z : (Fin N → Ω) × (Fin N → Ω) => ‖∑ j, s σ j • Φ (z.2 j)‖)
        (μN.prod μN) :=
      (integrable_finsetSum _ fun j _ => (hΦ2 j).smul (s σ j)).norm
    have hmeas : AEStronglyMeasurable (fun ω : Fin N → Ω => ‖∑ j, s σ j • Φ (ω j)‖) μN :=
      (integrable_finsetSum _ fun j _ => (hΦj j).smul (s σ j)).norm.aestronglyMeasurable
    calc ∫ z, ‖∑ j, s σ j • (Φ (z.1 j) - Φ (z.2 j))‖ ∂(μN.prod μN)
        ≤ ∫ z, (‖∑ j, s σ j • Φ (z.1 j)‖ + ‖∑ j, s σ j • Φ (z.2 j)‖) ∂(μN.prod μN) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hA.add hB) (Eventually.of_forall fun z => ?_)
          simp only [smul_sub, Finset.sum_sub_distrib]
          exact norm_sub_le _ _
      _ = ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN + ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN := by
          rw [integral_add hA hB, integral_comp_fst_prod μN μN hmeas,
            integral_comp_snd_prod μN μN hmeas]
      _ = 2 * ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN := by ring
  calc ∫ ω, ‖∑ j, Φ (ω j) - (N : ℝ) • m‖ ∂μN ≤ ∫ z, G z ∂(μN.prod μN) := hstep2
    _ = ∑ σ, w σ * ∫ z, G z ∂(μN.prod μN) := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ σ, w σ * (2 * ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (by rw [hswap σ]; exact htri σ) (hw σ)
    _ = 2 * ∑ σ, w σ * ∫ ω, ‖∑ j, s σ j • Φ (ω j)‖ ∂μN := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring

end MeasureTheory
