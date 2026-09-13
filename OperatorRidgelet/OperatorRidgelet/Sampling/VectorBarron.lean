import OperatorRidgelet.Sampling.VectorCompact
import OperatorRidgelet.ToFoML.TwoCoordinate
import OperatorRidgelet.ToMathlib.RealInnerDual
import OperatorRidgelet.ToMathlib.SqrtSumSq

/-!
# The Hilbert-valued Rademacher average of the ridge atoms

For a fixed sample `θ_1, …, θ_N` and outer weights `h_1, …, h_N` in the unit ball of a complex
Hilbert space `Y`, the average over the signs of `‖∑_j ε_j h_j β(⟪a_j, ·⟫ + c_j)‖_{C(K;Y)}` is at
most `2|β(0)| √N + 4 Lip(β) R_K √(∑_j (‖a_j‖² + c_j²))`.

The scalar bound of `OperatorRidgelet.Sampling.Basic` splits the complex phase into its real and
imaginary parts and contracts each; for a general Hilbert space this is unavailable, and the
manuscript replaces it by the two-coordinate comparison `lem:two-coordinate-comparison`
(`OperatorRidgelet.avg_iSup_boolSignVector_le`).  The output norm is written as a supremum over
the unit ball of `Y` viewed as a real Hilbert space, so the sign process is indexed by the
product of the compact set with that ball, and the increments of

`ψ_j(x, y) = β(⟪a_j, x⟫ + c_j) ⟪y, h_j⟫`

are dominated by those of `u_j(x, y) = Lip(β) (⟪a_j, x⟫ + c_j)` and
`v_j(x, y) = (|β(0)| + Lip(β) R_K ‖(a_j, c_j)‖) ⟪y, h_j⟫` together.
-/

noncomputable section
namespace OperatorRidgelet
open MeasureTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  {K : Set H}

/-- Evaluation of a real linear combination of vector ridge atoms. -/
theorem sum_smul_vectorRidgeAtom_apply (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) {N : ℕ} (θ : Fin N → H × ℝ) (h : Fin N → Y) (s : Fin N → ℝ)
    (x : K) :
    (∑ j, s j • vectorRidgeAtom hK (continuous_ofReal_comp hβ) (θ j) (h j)) x =
      ∑ j, (s j * β (⟪(θ j).1, (x : H)⟫ + (θ j).2)) • h j := by
  rw [BoundedContinuousFunction.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  change s j • ((β (⟪(θ j).1, (x : H)⟫ + (θ j).2) : ℂ) • h j) = _
  rw [Complex.coe_smul, smul_smul]

/-- **The Hilbert-valued Rademacher average of the ridge atoms.**  For a fixed sample and outer
weights in the unit ball of `Y`,
`2⁻ᴺ ∑_σ ‖∑_j σ_j h_j β(⟪a_j, ·⟫ + c_j)‖_{C(K;Y)} ≤
2|β(0)| √N + 4 Lip(β) R_K √(∑_j (‖a_j‖² + c_j²))`.
This is the Hilbert-valued form of
`OperatorRidgelet.inv_pow_two_mul_sum_norm_sum_signVector_smul_ridgeAtom_le`; the constant of the
first term is twice as large because the contraction principle is replaced by the two-coordinate
comparison `OperatorRidgelet.avg_iSup_boolSignVector_le`. -/
theorem inv_pow_two_mul_sum_norm_sum_signVector_smul_vectorRidgeAtom_le (hK : IsCompact K)
    (hKne : K.Nonempty) {β : ℝ → ℝ} {L : ℝ≥0} (hβ : LipschitzWith L β) {N : ℕ}
    (θ : Fin N → H × ℝ) (h : Fin N → Y) (hh : ∀ j, ‖h j‖ ≤ 1) :
    (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        ‖∑ j, signVector σ j • vectorRidgeAtom hK (continuous_ofReal_comp hβ) (θ j) (h j)‖ ≤
      2 * |β 0| * Real.sqrt N +
        4 * L * compactRadius K * Real.sqrt (∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2)) := by
  letI := InnerProductSpace.rclikeToReal ℂ Y
  obtain ⟨x₀, hx₀⟩ := hKne
  haveI : Nonempty (↥K × {y : Y // ‖y‖ ≤ 1}) := ⟨(⟨x₀, hx₀⟩, ⟨0, by simp⟩)⟩
  set R := compactRadius K with hRdef
  have hR0 : 0 ≤ R := compactRadius_nonneg K
  set t : Fin N → ℝ := fun j => Real.sqrt (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2) with htdef
  have ht0 : ∀ j, 0 ≤ t j := fun j => Real.sqrt_nonneg _
  set B : Fin N → ℝ := fun j => |β 0| + (L : ℝ) * R * t j with hBdef
  have hB0 : ∀ j, 0 ≤ B j := fun j => by
    have : (0 : ℝ) ≤ (L : ℝ) * R * t j := by positivity
    exact add_nonneg (abs_nonneg _) this
  -- the preactivation and the dual coordinate of the two-variable process
  set pre : Fin N → ↥K × {y : Y // ‖y‖ ≤ 1} → ℝ :=
    fun j z => ⟪(θ j).1, (z.1 : H)⟫ + (θ j).2 with hpredef
  set q : Fin N → ↥K × {y : Y // ‖y‖ ≤ 1} → ℝ := fun j z => ⟪(z.2 : Y), h j⟫ with hqdef
  have hpre : ∀ j z, |pre j z| ≤ t j * R := by
    intro j z
    refine (abs_inner_add_le_sqrt (θ j).1 (z.1 : H) (θ j).2).trans ?_
    have hsq : Real.sqrt (‖(θ j).1‖ ^ 2 + (θ j).2 ^ 2) = t j := by
      simp only [htdef, sq_abs]
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (le_compactRadius hK z.1.2) (ht0 j)
  have hq : ∀ j z, |q j z| ≤ 1 := by
    intro j z
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_one₀ z.2.2 (norm_nonneg _) (hh j)
  have hβabs : ∀ r : ℝ, |β r| ≤ |β 0| + (L : ℝ) * |r| := by
    intro r
    have := hβ.dist_le_mul r 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    calc |β r| = |β 0 + (β r - β 0)| := by ring_nf
      _ ≤ |β 0| + |β r - β 0| := abs_add_le _ _
      _ ≤ |β 0| + (L : ℝ) * |r| := by gcongr
  have hβB : ∀ j z, |β (pre j z)| ≤ B j := by
    intro j z
    refine (hβabs (pre j z)).trans ?_
    have : (L : ℝ) * |pre j z| ≤ (L : ℝ) * (t j * R) :=
      mul_le_mul_of_nonneg_left (hpre j z) L.coe_nonneg
    rw [hBdef]
    simp only
    nlinarith [this]
  -- the three processes of the comparison
  set ψ : Fin N → ↥K × {y : Y // ‖y‖ ≤ 1} → ℝ := fun j z => β (pre j z) * q j z with hψdef
  set u : Fin N → ↥K × {y : Y // ‖y‖ ≤ 1} → ℝ := fun j z => (L : ℝ) * pre j z with hudef
  set v : Fin N → ↥K × {y : Y // ‖y‖ ≤ 1} → ℝ := fun j z => B j * q j z with hvdef
  have hψbdd : ∀ j, IsBddFun (ψ j) := fun j => ⟨B j, fun z => by
    rw [hψdef]
    simp only [abs_mul]
    calc |β (pre j z)| * |q j z| ≤ B j * 1 :=
          mul_le_mul (hβB j z) (hq j z) (abs_nonneg _) (hB0 j)
      _ = B j := mul_one _⟩
  have hubdd : ∀ j, IsBddFun (u j) := fun j => ⟨(L : ℝ) * (t j * R), fun z => by
    rw [hudef]
    simp only [abs_mul, abs_of_nonneg L.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (hpre j z) L.coe_nonneg⟩
  have hvbdd : ∀ j, IsBddFun (v j) := fun j => ⟨B j, fun z => by
    rw [hvdef]
    simp only [abs_mul, abs_of_nonneg (hB0 j)]
    calc B j * |q j z| ≤ B j * 1 := mul_le_mul_of_nonneg_left (hq j z) (hB0 j)
      _ = B j := mul_one _⟩
  have hincr : ∀ j z z', |ψ j z - ψ j z'| ≤ |u j z - u j z'| + |v j z - v j z'| := by
    intro j z z'
    have hu' : |u j z - u j z'| = (L : ℝ) * |pre j z - pre j z'| := by
      rw [hudef]
      simp only [← mul_sub, abs_mul, abs_of_nonneg L.coe_nonneg]
    have hv' : |v j z - v j z'| = B j * |q j z - q j z'| := by
      rw [hvdef]
      simp only [← mul_sub, abs_mul, abs_of_nonneg (hB0 j)]
    have hlip : |β (pre j z) - β (pre j z')| ≤ (L : ℝ) * |pre j z - pre j z'| := by
      have := hβ.dist_le_mul (pre j z) (pre j z')
      rwa [Real.dist_eq, Real.dist_eq] at this
    have h1 : |(β (pre j z) - β (pre j z')) * q j z| ≤ |u j z - u j z'| := by
      rw [abs_mul, hu']
      calc |β (pre j z) - β (pre j z')| * |q j z| ≤ ((L : ℝ) * |pre j z - pre j z'|) * 1 :=
            mul_le_mul hlip (hq j z) (abs_nonneg _) (by positivity)
        _ = (L : ℝ) * |pre j z - pre j z'| := mul_one _
    have h2 : |β (pre j z') * (q j z - q j z')| ≤ |v j z - v j z'| := by
      rw [abs_mul, hv']
      exact mul_le_mul_of_nonneg_right (hβB j z') (abs_nonneg _)
    have hsplit : ψ j z - ψ j z' =
        (β (pre j z) - β (pre j z')) * q j z + β (pre j z') * (q j z - q j z') := by
      rw [hψdef]; ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have key := avg_iSup_boolSignVector_le hψbdd hubdd hvbdd hincr
  -- the supremum of the signed process dominates the `C(K;Y)` norm
  have hsumbdd : ∀ s : Fin N → ℝ, IsBddFun (fun z => ∑ j, s j * ψ j z) :=
    fun s => IsBddFun.sum Finset.univ fun j _ => (hψbdd j).const_mul (s j)
  have hnorm : ∀ s : Fin N → ℝ,
      ‖∑ j, s j • vectorRidgeAtom hK (continuous_ofReal_comp hβ) (θ j) (h j)‖ ≤
        ⨆ z, ∑ j, s j * ψ j z := by
    intro s
    have hbdd := (hsumbdd s).bddAbove
    have hz0 : (0 : ℝ) ≤ ⨆ z, ∑ j, s j * ψ j z := by
      refine le_trans (le_of_eq ?_) (le_ciSup hbdd ((⟨x₀, hx₀⟩, ⟨0, by simp⟩) :
        ↥K × {y : Y // ‖y‖ ≤ 1}))
      simp [hψdef, hqdef]
    refine (BoundedContinuousFunction.norm_le hz0).mpr fun x => ?_
    rw [sum_smul_vectorRidgeAtom_apply hK hβ θ h s x]
    obtain ⟨y, hy1, hy2⟩ := exists_norm_le_real_inner
      (∑ j, (s j * β (⟪(θ j).1, (x : H)⟫ + (θ j).2)) • h j)
    refine hy2.trans (le_trans (le_of_eq ?_) (le_ciSup hbdd ((x, ⟨y, hy1⟩) :
      ↥K × {y : Y // ‖y‖ ≤ 1})))
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    simp only [hψdef, hpredef, hqdef]
    ring
  -- the two-coordinate process splits into a linear process and a Hilbert process
  have hlin : ∀ (e₁ e₂ : Fin N → ℝ) (z : ↥K × {y : Y // ‖y‖ ≤ 1}),
      ∑ j, (e₁ j * u j z + e₂ j * v j z) ≤
        (L : ℝ) * R * Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 + (∑ j, e₁ j * (θ j).2) ^ 2) +
          ‖∑ j, (e₂ j * B j) • h j‖ := by
    intro e₁ e₂ z
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · have hlin1 : ∑ j, e₁ j * pre j z =
          ⟪∑ j, e₁ j • (θ j).1, (z.1 : H)⟫ + ∑ j, e₁ j * (θ j).2 := by
        rw [sum_inner, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_left]
        simp only [hpredef]
        ring
      have h1 : ∑ j, e₁ j * u j z = (L : ℝ) * ∑ j, e₁ j * pre j z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hudef]
        ring
      have h2 : ∑ j, e₁ j * pre j z ≤
          Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 + (∑ j, e₁ j * (θ j).2) ^ 2) * R := by
        calc ∑ j, e₁ j * pre j z ≤ |∑ j, e₁ j * pre j z| := le_abs_self _
          _ = |⟪∑ j, e₁ j • (θ j).1, (z.1 : H)⟫ + ∑ j, e₁ j * (θ j).2| := by rw [hlin1]
          _ ≤ Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 + (∑ j, e₁ j * (θ j).2) ^ 2) *
                Real.sqrt (‖(z.1 : H)‖ ^ 2 + 1) := abs_inner_add_le_sqrt _ _ _
          _ ≤ Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 + (∑ j, e₁ j * (θ j).2) ^ 2) * R :=
              mul_le_mul_of_nonneg_left (le_compactRadius hK z.1.2) (Real.sqrt_nonneg _)
      rw [h1]
      calc (L : ℝ) * ∑ j, e₁ j * pre j z ≤
            (L : ℝ) * (Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 +
              (∑ j, e₁ j * (θ j).2) ^ 2) * R) := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
        _ = (L : ℝ) * R * Real.sqrt (‖∑ j, e₁ j • (θ j).1‖ ^ 2 +
              (∑ j, e₁ j * (θ j).2) ^ 2) := by ring
    · have h3 : ∑ j, e₂ j * v j z = ⟪(z.2 : Y), ∑ j, (e₂ j * B j) • h j⟫ := by
        rw [inner_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_right]
        simp only [hvdef, hqdef]
        ring
      rw [h3]
      calc ⟪(z.2 : Y), ∑ j, (e₂ j * B j) • h j⟫ ≤ ‖(z.2 : Y)‖ * ‖∑ j, (e₂ j * B j) • h j‖ :=
            real_inner_le_norm _ _
        _ ≤ 1 * ‖∑ j, (e₂ j * B j) • h j‖ :=
            mul_le_mul_of_nonneg_right z.2.2 (norm_nonneg _)
        _ = ‖∑ j, (e₂ j * B j) • h j‖ := one_mul _
  set A : (Fin N → Bool) → ℝ := fun ε =>
    (L : ℝ) * R * Real.sqrt (‖∑ j, boolSignVector ε j • (θ j).1‖ ^ 2 +
      (∑ j, boolSignVector ε j * (θ j).2) ^ 2) with hAdef
  set C : (Fin N → Bool) → ℝ := fun ε => ‖∑ j, (boolSignVector ε j * B j) • h j‖ with hCdef
  have hdouble : ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
        (⨆ z, ∑ j, (boolSignVector ε₁ j * u j z + boolSignVector ε₂ j * v j z)) ≤
      (2 ^ N : ℝ) * (∑ ε, A ε) + (2 ^ N : ℝ) * ∑ ε, C ε := by
    have hcard : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
      simp [Finset.card_univ]
    refine le_trans (Finset.sum_le_sum fun ε₁ _ => Finset.sum_le_sum fun ε₂ _ =>
      ciSup_le (hlin (boolSignVector ε₁) (boolSignVector ε₂))) (le_of_eq ?_)
    calc ∑ ε₁ : Fin N → Bool, ∑ _ε₂ : Fin N → Bool, (A ε₁ + C _ε₂)
        = ∑ ε₁ : Fin N → Bool, ((2 ^ N : ℝ) * A ε₁ + ∑ ε₂, C ε₂) := by
          refine Finset.sum_congr rfl fun ε₁ _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
      _ = (2 ^ N : ℝ) * (∑ ε, A ε) + (2 ^ N : ℝ) * ∑ ε, C ε := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
  -- the two Rademacher averages
  set T := Real.sqrt (∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hAavg : (2 ^ N : ℝ)⁻¹ * ∑ ε, A ε ≤ (L : ℝ) * R * T := by
    have hconv := sum_signs_eq_sum_bool (N := N) fun s =>
      Real.sqrt (‖∑ j, s j • (θ j).1‖ ^ 2 + (∑ j, s j * (θ j).2) ^ 2)
    have hsum : ∑ ε, A ε = (L : ℝ) * R *
        ∑ σ : Signs N, Real.sqrt (‖∑ j, signVector σ j • (θ j).1‖ ^ 2 +
          (∑ j, signVector σ j * (θ j).2) ^ 2) := by
      rw [hconv, Finset.mul_sum]
    rw [hsum, ← mul_assoc, mul_comm ((2 ^ N : ℝ)⁻¹) ((L : ℝ) * R), mul_assoc]
    exact mul_le_mul_of_nonneg_left (inv_pow_two_mul_sum_sqrt_le θ) (by positivity)
  have hCavg : (2 ^ N : ℝ)⁻¹ * ∑ ε, C ε ≤ Real.sqrt (∑ j, B j ^ 2) := by
    have hconv := sum_signs_eq_sum_bool (N := N) fun s => ‖∑ j, (s j * B j) • h j‖
    have hsmul : ∀ σ : Signs N, ∑ j, signVector σ j • (B j • h j) =
        ∑ j, (signVector σ j * B j) • h j :=
      fun σ => Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hstep := inv_pow_two_mul_sum_norm_sum_signVector_smul_le (fun j => B j • h j)
    simp_rw [hsmul] at hstep
    have hle : Real.sqrt (∑ j, ‖B j • h j‖ ^ 2) ≤ Real.sqrt (∑ j, B j ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
      have : ‖B j • h j‖ ≤ B j := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hB0 j)]
        calc B j * ‖h j‖ ≤ B j * 1 := mul_le_mul_of_nonneg_left (hh j) (hB0 j)
          _ = B j := mul_one _
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    rw [show ∑ ε, C ε = ∑ σ : Signs N, ‖∑ j, (signVector σ j * B j) • h j‖ from hconv.symm]
    exact hstep.trans hle
  have hBsum : Real.sqrt (∑ j, B j ^ 2) ≤ |β 0| * Real.sqrt N + (L : ℝ) * R * T := by
    have h1 : Real.sqrt (∑ _j : Fin N, |β 0| ^ 2) = |β 0| * Real.sqrt N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq (abs_nonneg _)]
      ring
    have h2 : Real.sqrt (∑ j, ((L : ℝ) * R * t j) ^ 2) = (L : ℝ) * R * T := by
      have hmul : ∑ j, ((L : ℝ) * R * t j) ^ 2 =
          ((L : ℝ) * R) ^ 2 * ∑ j, (‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : t j ^ 2 = ‖(θ j).1‖ ^ 2 + |(θ j).2| ^ 2 := by
          simp only [htdef]
          exact Real.sq_sqrt (by positivity)
        rw [mul_pow, this]
      rw [hmul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hsplit := Real.sqrt_sum_sq_add_le (fun _ => |β 0|) (fun j => (L : ℝ) * R * t j)
    rw [h1, h2] at hsplit
    refine le_trans (le_of_eq ?_) hsplit
    simp only [hBdef]
  -- assemble
  have hpow : (0 : ℝ) < (2 ^ N : ℝ) := by positivity
  calc (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
        ‖∑ j, signVector σ j • vectorRidgeAtom hK (continuous_ofReal_comp hβ) (θ j) (h j)‖
      ≤ (2 ^ N : ℝ)⁻¹ * ∑ ε : Fin N → Bool, ⨆ z, ∑ j, boolSignVector ε j * ψ j z := by
        rw [sum_signs_eq_sum_bool fun s =>
          ‖∑ j, s j • vectorRidgeAtom hK (continuous_ofReal_comp hβ) (θ j) (h j)‖]
        gcongr with ε _
        exact hnorm (boolSignVector ε)
    _ ≤ 2 * ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹ * ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
          ⨆ z, ∑ j, (boolSignVector ε₁ j * u j z + boolSignVector ε₂ j * v j z)) := key
    _ ≤ 2 * ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹ *
          ((2 ^ N : ℝ) * (∑ ε, A ε) + (2 ^ N : ℝ) * ∑ ε, C ε)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdouble (by positivity)) (by norm_num)
    _ = 2 * ((2 ^ N : ℝ)⁻¹ * ∑ ε, A ε + (2 ^ N : ℝ)⁻¹ * ∑ ε, C ε) := by
        field_simp
    _ ≤ 2 * ((L : ℝ) * R * T + (|β 0| * Real.sqrt N + (L : ℝ) * R * T)) :=
        mul_le_mul_of_nonneg_left (add_le_add hAavg (hCavg.trans hBsum)) (by norm_num)
    _ = 2 * |β 0| * Real.sqrt N + 4 * L * R * T := by ring

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [SecondCountableTopology Y]

/-- **The Hilbert-valued Rademacher complexity of a Lipschitz activation.**
`𝔑_N(K; p, β) ≤ (2|β(0)| + 4 Lip(β) R_K M₂)/√N` for a unit phase `h` and a parameter law with
second moment `M₂²`. -/
theorem rademacherComplexity_vectorRidge_le (hK : IsCompact K) {β : ℝ → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (p : Measure (H × ℝ)) [IsProbabilityMeasure p] (h : H × ℝ → Y)
    (hmeas : AEStronglyMeasurable h p) (hu : ∀ᵐ θ ∂p, ‖h θ‖ = 1)
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) p) {N : ℕ} (hN : 0 < N) :
    rademacherComplexity N K p (fun t => (β t : ℂ)) h ≤
      (2 * |β 0| + 4 * L * compactRadius K * Real.sqrt (secondMoment p)) / Real.sqrt N := by
  have hR : 0 ≤ compactRadius K := compactRadius_nonneg K
  have hnum : 0 ≤ 2 * |β 0| + 4 * (L : ℝ) * compactRadius K * Real.sqrt (secondMoment p) := by
    have : 0 ≤ 4 * (L : ℝ) * compactRadius K * Real.sqrt (secondMoment p) := by positivity
    linarith [abs_nonneg (β 0)]
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · have hzero : rademacherComplexity N (∅ : Set H) p (fun t => (β t : ℂ)) h = 0 := by
      unfold rademacherComplexity compactSupNorm
      simp
    rw [hzero]
    exact div_nonneg hnum (Real.sqrt_nonneg _)
  set Φ : H × ℝ → (K →ᵇ Y) := fun θ => vectorRidgeAtom hK (continuous_ofReal_comp hβ) θ (h θ)
    with hΦdef
  have hΦ : ∀ θ (x : K), Φ θ x = (β (⟪θ.1, (x : H)⟫ + θ.2) : ℂ) • h θ := fun _ _ => rfl
  have hΦint : Integrable Φ p :=
    integrable_vectorRidgeAtom hK (lipschitzWith_ofReal_comp hβ) p h hmeas hu hM
  have hΦj : ∀ j : Fin N, Integrable (fun ω : Fin N → H × ℝ => Φ (ω j)) (sampleLaw N p) :=
    fun j => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hΦint
  have hint : ∀ σ : Signs N, Integrable
      (fun ω : Fin N → H × ℝ => ‖∑ j, signVector σ j • Φ (ω j)‖) (sampleLaw N p) :=
    fun σ => (integrable_finsetSum Finset.univ
      (f := fun j (ω : Fin N → H × ℝ) => signVector σ j • Φ (ω j))
      fun j _ => (hΦj j).smul (signVector σ j)).norm
  have hqj : Integrable (fun ω : Fin N → H × ℝ => ∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2))
      (sampleLaw N p) :=
    integrable_finsetSum Finset.univ
      (f := fun j (ω : Fin N → H × ℝ) => ‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2)
      fun j _ => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hM
  have hsqrt : Integrable (fun ω : Fin N → H × ℝ =>
      Real.sqrt (∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2))) (sampleLaw N p) := hqj.sqrt
  have hae : ∀ᵐ ω ∂sampleLaw N p,
      (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, ‖∑ j, signVector σ j • Φ (ω j)‖ ≤
        2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
          Real.sqrt (∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2)) := by
    filter_upwards [ae_sampleLaw_forall (N := N) (hu.mono fun θ hθ => hθ.le)] with ω hω
    exact inv_pow_two_mul_sum_norm_sum_signVector_smul_vectorRidgeAtom_le hK hKne hβ
      (fun j => ω j) (fun j => h (ω j)) hω
  have hmain : (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N,
      ∫ ω, ‖∑ j, signVector σ j • Φ (ω j)‖ ∂sampleLaw N p ≤
        2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
          Real.sqrt (N * secondMoment p) := by
    calc (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, ∫ ω, ‖∑ j, signVector σ j • Φ (ω j)‖ ∂sampleLaw N p
        = ∫ ω, (2 ^ N : ℝ)⁻¹ * ∑ σ : Signs N, ‖∑ j, signVector σ j • Φ (ω j)‖
            ∂sampleLaw N p := by
          rw [integral_const_mul, integral_finsetSum Finset.univ fun σ _ => hint σ]
      _ ≤ ∫ ω, (2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
            Real.sqrt (∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2))) ∂sampleLaw N p :=
          integral_mono_ae ((integrable_finsetSum Finset.univ fun σ _ => hint σ).const_mul _)
            ((integrable_const _).add (hsqrt.const_mul _)) hae
      _ = 2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
            ∫ ω, Real.sqrt (∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2)) ∂sampleLaw N p := by
          rw [integral_add (integrable_const _) (hsqrt.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul]
      _ ≤ 2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
            Real.sqrt (∫ ω, ∑ j, (‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2) ∂sampleLaw N p) := by
          gcongr
          exact integral_sqrt_le_sqrt_integral hqj
            (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun j _ => by positivity)
      _ = 2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
            Real.sqrt (N * secondMoment p) := by
          unfold sampleLaw secondMoment
          rw [integral_finsetSum Finset.univ
            (f := fun j (ω : Fin N → H × ℝ) => ‖(ω j).1‖ ^ 2 + |(ω j).2| ^ 2)
            fun j _ => (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hM]
          simp_rw [integral_eval_pi p hM.aestronglyMeasurable]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [rademacherComplexity_eq_sum_signs_vec N p (fun t => (β t : ℂ)) h hΦ hΦint]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt N / N = 1 / Real.sqrt N := Real.sqrt_div_self'
  calc (N : ℝ)⁻¹ * ((2 ^ N : ℝ)⁻¹ *
        ∑ σ : Signs N, ∫ ω, ‖∑ j, signVector σ j • Φ (ω j)‖ ∂sampleLaw N p)
      ≤ (N : ℝ)⁻¹ * (2 * |β 0| * Real.sqrt N + 4 * (L : ℝ) * compactRadius K *
          Real.sqrt (N * secondMoment p)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (2 * |β 0| + 4 * (L : ℝ) * compactRadius K * Real.sqrt (secondMoment p)) *
          (Real.sqrt N / N) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N)]
        field_simp
    _ = (2 * |β 0| + 4 * (L : ℝ) * compactRadius K * Real.sqrt (secondMoment p)) /
          Real.sqrt N := by
        rw [hsq]
        ring

/-- The centred sum of Bochner-integrable atoms in a normed space is integrable. -/
theorem integrable_norm_sum_sub_vec {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : Measure Ω) [IsProbabilityMeasure p] {Φ : Ω → E}
    (hint : Integrable Φ p) (N : ℕ) :
    Integrable (fun ω : Fin N → Ω => ‖∑ j, Φ (ω j) - (N : ℝ) • ∫ ω', Φ ω' ∂p‖)
      (sampleLaw N p) :=
  ((integrable_finsetSum Finset.univ (f := fun j (ω : Fin N → Ω) => Φ (ω j)) fun j _ =>
    (measurePreserving_eval (fun _ => p) j).integrable_comp_of_integrable hint).sub
    (integrable_const _)).norm

/-- The `C(K;Y)` sampling error of the polar sampled network is integrable in the sample. -/
theorem integrable_compactSupNorm_polarSampledNetwork_sub_vec (hK : IsCompact K) {β : ℝ → ℝ}
    {L : ℝ≥0} (hβ : LipschitzWith L β) (Γ : VectorMeasure (H × ℝ) Y)
    [IsFiniteMeasure Γ.variation]
    (hM : Integrable (fun θ : H × ℝ => ‖θ.1‖ ^ 2 + |θ.2| ^ 2) (polarLaw Γ)) {N : ℕ}
    (hN : 0 < N) :
    Integrable (fun θ : Fin N → H × ℝ => compactSupNorm K (fun x =>
        polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x)) (sampleLaw N (polarLaw Γ)) := by
  by_cases h0 : totalVariation Γ = 0
  · rw [polarLaw_eq_zero_of_totalVariation_eq_zero h0, sampleLaw_zero hN]
    exact integrable_zero_measure
  haveI := isProbabilityMeasure_polarLaw Γ h0
  have hβc := lipschitzWith_ofReal_comp hβ
  have hh : AEStronglyMeasurable (polarDensity Γ) (polarLaw Γ) :=
    aestronglyMeasurable_polarDensity Γ (ne_zero_of_totalVariation_ne_zero h0)
  have hh1 : ∀ᵐ θ ∂polarLaw Γ, ‖polarDensity Γ θ‖ = 1 := ae_polarLaw_norm_polarDensity_eq_one Γ
  set Φ : H × ℝ → (K →ᵇ Y) := fun θ =>
    vectorRidgeAtom hK (continuous_ofReal_comp hβ) θ (polarDensity Γ θ) with hΦdef
  have hΦ' : ∀ θ (x : K), Φ θ x =
      (β (⟪(id θ).1, (x : H)⟫ + (id θ).2) : ℂ) • polarDensity Γ θ := fun _ _ => rfl
  have hint : Integrable Φ (polarLaw Γ) :=
    integrable_vectorRidgeAtom hK hβc (polarLaw Γ) (polarDensity Γ) hh hh1 hM
  have hpt : ∀ θ : Fin N → H × ℝ,
      compactSupNorm K (fun x => polarSampledNetwork (fun t => (β t : ℂ)) Γ θ x -
          integralNetwork (fun t => (β t : ℂ)) Γ x) =
        polarWeight Γ / N * ‖∑ j, Φ (θ j) - (N : ℝ) • ∫ θ', Φ θ' ∂polarLaw Γ‖ := by
    intro θ
    rw [← compactSupNorm_sampled_sub_eq_vec (polarLaw Γ) (fun t => (β t : ℂ)) id
      (polarDensity Γ) hΦ' hint (polarWeight_nonneg Γ) hN θ]
    refine compactSupNorm_congr fun x hx => ?_
    rw [integralNetwork_eq_integral_polarLaw (fun t => (β t : ℂ)) Γ h0
      ((memLp_ridge_complex hβc (polarLaw Γ) hM x).integrable (by norm_num))]
    rfl
  exact ((integrable_norm_sum_sub_vec (polarLaw Γ) hint N).const_mul (polarWeight Γ / N)).congr
    (Filter.Eventually.of_forall fun θ => (hpt θ).symm)

end OperatorRidgelet
