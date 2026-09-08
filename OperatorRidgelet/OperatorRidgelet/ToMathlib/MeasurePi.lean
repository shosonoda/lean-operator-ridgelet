import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinates of a finite product of probability measures, and the variance of an empirical mean

For a probability measure `p` and the product `p^{⊗ι} = Measure.pi (fun _ : ι => p)`:

* `integral_eval_pi`, `memLp_eval_pi`: a function of one coordinate has the same integral and
  the same `L^q`-membership as under `p`;
* `integral_inner_eval_eval_eq_zero`: distinct coordinates of a centred square-integrable
  Hilbert-valued function are uncorrelated;
* `integral_norm_sq_sampleMean`: the variance identity
  `∫ ‖(V/N) ∑_j Y(ω_j) − V ∫ Y dp‖² dp^{⊗N} = (V²/N) (∫ ‖Y‖² dp − ‖∫ Y dp‖²)`
  for the empirical mean of `N` independent samples of `Y ∈ L²(p)`.
-/

open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

section Pi

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
  [IsProbabilityMeasure p]

/-- The integral of a function of one coordinate against `p^{⊗ι}` is its integral against
`p`. -/
theorem integral_eval_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Ω → E}
    (hg : AEStronglyMeasurable g p) (i : ι) :
    ∫ ω, g (ω i) ∂(Measure.pi fun _ : ι => p) = ∫ x, g x ∂p := by
  have hmp := measurePreserving_eval (fun _ : ι => p) i
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable (by rw [hmp.map_eq]; exact hg)]

theorem memLp_eval_pi {E : Type*} [NormedAddCommGroup E] {g : Ω → E} {q : ℝ≥0∞}
    (hg : MemLp g q p) (i : ι) : MemLp (fun ω => g (ω i)) q (Measure.pi fun _ : ι => p) :=
  hg.comp_measurePreserving (measurePreserving_eval (fun _ : ι => p) i)

end Pi

/-! ### The Hilbert-valued sampling identity -/

section Hilbert

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X] (p : Measure Ω) [IsProbabilityMeasure p]

/-- Independent centred coordinates are uncorrelated: for `j ≠ k`,
`∫ ⟪Z(ω_j), Z(ω_k)⟫ dp^{⊗(n+1)} = 0` when `∫ Z dp = 0`. -/
theorem integral_inner_eval_eval_eq_zero {Z : Ω → X} (hZ : MemLp Z 2 p)
    (hZ0 : ∫ ω, Z ω ∂p = 0) {n : ℕ} {j k : Fin (n + 1)} (hjk : j ≠ k) :
    ∫ ω, ⟪Z (ω j), Z (ω k)⟫ ∂(Measure.pi fun _ : Fin (n + 1) => p) = 0 := by
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hjk.symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) j with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => p) j
  rw [← (hmp.symm e).integral_comp']
  have hfun : (fun z : Ω × (Fin n → Ω) =>
      ⟪Z (e.symm z j), Z (e.symm z (j.succAbove k'))⟫) = fun z => ⟪Z z.1, Z (z.2 k')⟫ := by
    funext z
    simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hZint : Integrable Z p := hZ.integrable one_le_two
  have hZk' : MemLp (fun ω' : Fin n → Ω => Z (ω' k')) 2 (Measure.pi fun _ : Fin n => p) :=
    memLp_eval_pi p hZ k'
  have hint : Integrable (fun z : Ω × (Fin n → Ω) => ⟪Z z.1, Z (z.2 k')⟫)
      (p.prod (Measure.pi fun _ : Fin n => p)) := by
    have h1 : Integrable (fun z : Ω × (Fin n → Ω) => ‖Z z.1‖ * ‖Z (z.2 k')‖)
        (p.prod (Measure.pi fun _ : Fin n => p)) :=
      Integrable.mul_prod hZint.norm (hZk'.integrable one_le_two).norm
    refine h1.mono' ?_ (Eventually.of_forall fun z => norm_inner_le_norm _ _)
    exact (hZ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
      (hZk'.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  rw [hfun, integral_prod _ hint]
  have hinner : ∀ a : Ω,
      ∫ ω' : Fin n → Ω, ⟪Z a, Z (ω' k')⟫ ∂(Measure.pi fun _ : Fin n => p) = 0 := by
    intro a
    rw [integral_inner (hZk'.integrable one_le_two), integral_eval_pi p hZ.1, hZ0, inner_zero_right]
  simp only [hinner, integral_zero]

/-- The variance identity for the empirical mean of `N` independent square-integrable
Hilbert-valued samples: `𝔼‖(V/N) ∑_j Y_j − V 𝔼Y‖² = (V²/N)(𝔼‖Y‖² − ‖𝔼Y‖²)`. -/
theorem integral_norm_sq_sampleMean {Y : Ω → X} (hY : MemLp Y 2 p) (V : ℝ) {N : ℕ}
    (hN : 0 < N) :
    ∫ ω, ‖(V / N : ℝ) • ∑ j, Y (ω j) - V • ∫ ω', Y ω' ∂p‖ ^ 2 ∂(Measure.pi fun _ : Fin N => p) =
      V ^ 2 / N * ((∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖∫ ω', Y ω' ∂p‖ ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set m : X := ∫ ω', Y ω' ∂p with hm
  set Z : Ω → X := fun ω' => Y ω' - m with hZ_def
  have hYint : Integrable Y p := hY.integrable one_le_two
  have hZ : MemLp Z 2 p := hY.sub (memLp_const m)
  have hZint : Integrable Z p := hZ.integrable one_le_two
  have hZ0 : ∫ ω, Z ω ∂p = 0 := by
    rw [hZ_def]
    simp only
    rw [integral_sub hYint (integrable_const m), integral_const, probReal_univ, one_smul, ← hm,
      sub_self]
  have hNne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  -- the centred sum
  have hpt : ∀ ω : Fin (n + 1) → Ω,
      (V / (n + 1 : ℕ) : ℝ) • ∑ j, Y (ω j) - V • m = (V / (n + 1 : ℕ) : ℝ) • ∑ j, Z (ω j) := by
    intro ω
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_mul_cancel₀ V hNne]
  -- the second moment of the centred variable
  have hYsq : Integrable (fun ω' => ‖Y ω'‖ ^ 2) p :=
    (memLp_two_iff_integrable_sq_norm hY.1).mp hY
  have hvar : ∫ ω', ‖Z ω'‖ ^ 2 ∂p = (∫ ω', ‖Y ω'‖ ^ 2 ∂p) - ‖m‖ ^ 2 := by
    have h1 : ∀ ω', ‖Z ω'‖ ^ 2 = ‖Y ω'‖ ^ 2 - 2 * ⟪Y ω', m⟫ + ‖m‖ ^ 2 := fun ω' =>
      norm_sub_sq_real _ _
    simp_rw [h1]
    have hA : Integrable (fun ω' => ‖Y ω'‖ ^ 2 - 2 * ⟪Y ω', m⟫) p :=
      hYsq.sub ((hYint.inner_const m).const_mul (2 : ℝ))
    rw [integral_add hA (integrable_const _),
      integral_sub hYsq ((hYint.inner_const m).const_mul (2 : ℝ)), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    have h2 : ∫ ω', ⟪Y ω', m⟫ ∂p = ‖m‖ ^ 2 := by
      simp_rw [real_inner_comm m (Y _)]
      rw [integral_inner hYint, ← hm, real_inner_self_eq_norm_sq]
    rw [h2]
    ring
  -- rewrite the integrand through the centred sum
  have hint_eq : (fun ω : Fin (n + 1) → Ω =>
      ‖(V / (n + 1 : ℕ) : ℝ) • ∑ j, Y (ω j) - V • m‖ ^ 2) =
      fun ω => (V / (n + 1 : ℕ)) ^ 2 * ‖∑ j, Z (ω j)‖ ^ 2 := by
    funext ω
    rw [hpt ω, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- the key identity: `∫ ‖∑ Z(ω_j)‖² = (n+1) ∫ ‖Z‖²`
  have hkey : ∫ ω, ‖∑ j, Z (ω j)‖ ^ 2 ∂(Measure.pi fun _ : Fin (n + 1) => p) =
      (n + 1 : ℕ) * ∫ ω', ‖Z ω'‖ ^ 2 ∂p := by
    have hexp : ∀ ω : Fin (n + 1) → Ω,
        ‖∑ j, Z (ω j)‖ ^ 2 = ∑ j, ∑ k, ⟪Z (ω j), Z (ω k)⟫ := by
      intro ω
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp_rw [inner_sum]
    simp_rw [hexp]
    have hZj : ∀ j : Fin (n + 1),
        MemLp (fun ω : Fin (n + 1) → Ω => Z (ω j)) 2 (Measure.pi fun _ : Fin (n + 1) => p) :=
      fun j => memLp_eval_pi p hZ j
    have hterm : ∀ j k : Fin (n + 1), Integrable (fun ω : Fin (n + 1) → Ω => ⟪Z (ω j), Z (ω k)⟫)
        (Measure.pi fun _ : Fin (n + 1) => p) := by
      intro j k
      have h1 := (memLp_two_iff_integrable_sq_norm (hZj j).1).mp (hZj j)
      have h2 := (memLp_two_iff_integrable_sq_norm (hZj k).1).mp (hZj k)
      refine ((h1.add h2).const_mul (1 / 2 : ℝ)).mono' ((hZj j).1.inner (hZj k).1)
        (Eventually.of_forall fun ω => ?_)
      calc ‖⟪Z (ω j), Z (ω k)⟫‖ ≤ ‖Z (ω j)‖ * ‖Z (ω k)‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 * (‖Z (ω j)‖ ^ 2 + ‖Z (ω k)‖ ^ 2) := by
            nlinarith [sq_nonneg (‖Z (ω j)‖ - ‖Z (ω k)‖)]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hterm j k]
    simp_rw [integral_finsetSum _ fun k _ => hterm _ k]
    have hdiag : ∀ j : Fin (n + 1),
        ∫ ω, ⟪Z (ω j), Z (ω j)⟫ ∂(Measure.pi fun _ : Fin (n + 1) => p) =
          ∫ ω', ‖Z ω'‖ ^ 2 ∂p := by
      intro j
      simp_rw [real_inner_self_eq_norm_sq]
      exact integral_eval_pi p (hZ.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable j
    have hoff : ∀ j k : Fin (n + 1), j ≠ k →
        ∫ ω, ⟪Z (ω j), Z (ω k)⟫ ∂(Measure.pi fun _ : Fin (n + 1) => p) = 0 :=
      fun j k hjk => integral_inner_eval_eval_eq_zero p hZ hZ0 hjk
    calc ∑ j, ∑ k, ∫ ω, ⟪Z (ω j), Z (ω k)⟫ ∂(Measure.pi fun _ : Fin (n + 1) => p)
        = ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            if j = k then ∫ ω', ‖Z ω'‖ ^ 2 ∂p else 0 := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          split_ifs with h
          · subst h
            exact hdiag j
          · exact hoff j k h
      _ = ∑ j : Fin (n + 1), ∫ ω', ‖Z ω'‖ ^ 2 ∂p := by simp
      _ = (n + 1 : ℕ) * ∫ ω', ‖Z ω'‖ ^ 2 ∂p := by simp
  rw [hint_eq, integral_const_mul, hkey, hvar]
  field_simp

end Hilbert
