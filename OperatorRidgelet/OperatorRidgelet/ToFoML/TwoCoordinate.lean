import OperatorRidgelet.ToFoML.RademacherSigns

/-!
# A two-coordinate Rademacher comparison

The contraction principle of Ledoux and Talagrand replaces `∑ ε_j φ_j(u_j(x))` by
`∑ ε_j u_j(x)` when the `φ_j` are Lipschitz, and it is the tool behind the scalar Barron bound
(`sum_sSup_abs_contraction` of `OperatorRidgelet.ToFoML.RademacherSigns`).  For Hilbert-valued
outer weights the same route is not available, and the manuscript replaces it by the comparison
of this file (`lem:two-coordinate-comparison`): if the increments of `ψ_i` are dominated by the
increments of `u_i` and `v_i` together, then the Rademacher average of `sup_s ∑ ε_i ψ_i(s)` is at
most twice the Rademacher average of `sup_s ∑ (ε_{i1} u_i(s) + ε_{i2} v_i(s))`, with independent
signs for the two coordinates.

* `IsBddFun f` says that `f` is bounded, which is what makes the suprema below real numbers;
* `iSup_add_sign_le` is the one-sign comparison with an arbitrary offset `F`, the step of the
  proof that does the work;
* `pow_two_mul_sum_iSup_boolSignVector_le` is the comparison itself, proved from the one-sign
  step by replacing one coordinate at a time.

The averages are the finite averages `2⁻ᴺ ∑_{σ : Signs N}` over the sign vectors, as in
`OperatorRidgelet.ToFoML.RademacherSigns`.
-/

noncomputable section

namespace OperatorRidgelet

open Finset

variable {S : Type*}

/-- A bounded real function: the hypothesis under which the suprema of this file are real
numbers rather than the junk value of an unbounded supremum. -/
def IsBddFun (f : S → ℝ) : Prop := ∃ C, ∀ s, |f s| ≤ C

/-- A bounded function has a supremum: its range is bounded above. -/
theorem IsBddFun.bddAbove {f : S → ℝ} (hf : IsBddFun f) : BddAbove (Set.range f) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, by rintro _ ⟨s, rfl⟩; exact (le_abs_self _).trans (hC s)⟩

/-- A sum of two bounded functions is bounded. -/
theorem IsBddFun.add {f g : S → ℝ} (hf : IsBddFun f) (hg : IsBddFun g) :
    IsBddFun (fun s => f s + g s) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun s => (abs_add_le _ _).trans (add_le_add (hC s) (hD s))⟩

/-- The negative of a bounded function is bounded. -/
theorem IsBddFun.neg {f : S → ℝ} (hf : IsBddFun f) : IsBddFun (fun s => -f s) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun s => by simpa using hC s⟩

/-- A difference of two bounded functions is bounded. -/
theorem IsBddFun.sub {f g : S → ℝ} (hf : IsBddFun f) (hg : IsBddFun g) :
    IsBddFun (fun s => f s - g s) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- A constant multiple of a bounded function is bounded. -/
theorem IsBddFun.const_mul {f : S → ℝ} (hf : IsBddFun f) (c : ℝ) :
    IsBddFun (fun s => c * f s) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨|c| * C, fun s => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC s) (abs_nonneg c)⟩

/-- The zero function is bounded. -/
theorem IsBddFun.zero : IsBddFun (fun _ : S => (0 : ℝ)) := ⟨0, by simp⟩

/-- A finite sum of bounded functions is bounded. -/
theorem IsBddFun.sum {ι : Type*} (t : Finset ι) {f : ι → S → ℝ}
    (hf : ∀ i ∈ t, IsBddFun (f i)) : IsBddFun (fun s => ∑ i ∈ t, f i s) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using (IsBddFun.zero (S := S))
  | insert i t hi ih =>
      have h1 : IsBddFun (f i) := hf i (mem_insert_self i t)
      have h2 : IsBddFun (fun s => ∑ j ∈ t, f j s) :=
        ih fun j hj => hf j (mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using h1.add h2

/-! ### The one-sign comparison -/

/-- **One-sign comparison.**  If the increments of `ψ` are dominated by those of `u` and `v`,
then for every bounded offset `F`,
`sup_s (F + ψ) + sup_s (F − ψ) ≤ ½ ∑_{η ∈ {±1}²} sup_s (F + 2η₁u + 2η₂v)`.
The left side is twice the average over one sign, the right side twice the average over two. -/
theorem iSup_add_sign_le [Nonempty S] {F ψ u v : S → ℝ} (hF : IsBddFun F) (_hψ : IsBddFun ψ)
    (hu : IsBddFun u) (hv : IsBddFun v)
    (hincr : ∀ s t, |ψ s - ψ t| ≤ |u s - u t| + |v s - v t|) :
    (⨆ s, (F s + ψ s)) + (⨆ s, (F s - ψ s)) ≤
      ((⨆ s, (F s + (2 * u s + 2 * v s))) + (⨆ s, (F s + (2 * u s - 2 * v s))) +
          (⨆ s, (F s + (-(2 * u s) + 2 * v s))) +
          (⨆ s, (F s + (-(2 * u s) - 2 * v s)))) / 2 := by
  have hu2 : IsBddFun (fun s => 2 * u s) := hu.const_mul 2
  have hv2 : IsBddFun (fun s => 2 * v s) := hv.const_mul 2
  have b1 : BddAbove (Set.range fun s => F s + (2 * u s + 2 * v s)) :=
    (hF.add (hu2.add hv2)).bddAbove
  have b2 : BddAbove (Set.range fun s => F s + (2 * u s - 2 * v s)) :=
    (hF.add (hu2.sub hv2)).bddAbove
  have b3 : BddAbove (Set.range fun s => F s + (-(2 * u s) + 2 * v s)) :=
    (hF.add (hu2.neg.add hv2)).bddAbove
  have b4 : BddAbove (Set.range fun s => F s + (-(2 * u s) - 2 * v s)) :=
    (hF.add (hu2.neg.sub hv2)).bddAbove
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- near maximizers of `F + ψ` and of `F − ψ`
  obtain ⟨sp, hsp⟩ : ∃ s, (⨆ t, (F t + ψ t)) - ε / 2 < F s + ψ s :=
    exists_lt_of_lt_ciSup (by linarith)
  obtain ⟨sm, hsm⟩ : ∃ s, (⨆ t, (F t - ψ t)) - ε / 2 < F s - ψ s :=
    exists_lt_of_lt_ciSup (by linarith)
  set A := F sp - F sm with hA
  set r := u sp - u sm with hr
  set q := v sp - v sm with hq
  -- each of the four suprema dominates the two values at `sp` and `sm`
  have key : ∀ (e₁ e₂ : ℝ), (e₁ = 1 ∨ e₁ = -1) → (e₂ = 1 ∨ e₂ = -1) →
      ∀ T : ℝ, (F sp + (e₁ * (2 * u sp) + e₂ * (2 * v sp)) ≤ T) →
        (F sm + (e₁ * (2 * u sm) + e₂ * (2 * v sm)) ≤ T) →
        (F sp + F sm) + (e₁ * (2 * (u sp + u sm)) + e₂ * (2 * (v sp + v sm)))
            + |A + (e₁ * (2 * r) + e₂ * (2 * q))| ≤ 2 * T := by
    intro e₁ e₂ _ _ T h1 h2
    have habs := abs_cases (A + (e₁ * (2 * r) + e₂ * (2 * q)))
    rcases habs with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> simp only [hA, hr, hq] <;> nlinarith
  have h1 := key 1 1 (Or.inl rfl) (Or.inl rfl) _
    (le_ciSup_of_le b1 sp (by ring_nf; rfl)) (le_ciSup_of_le b1 sm (by ring_nf; rfl))
  have h2 := key 1 (-1) (Or.inl rfl) (Or.inr rfl) _
    (le_ciSup_of_le b2 sp (by ring_nf; rfl)) (le_ciSup_of_le b2 sm (by ring_nf; rfl))
  have h3 := key (-1) 1 (Or.inr rfl) (Or.inl rfl) _
    (le_ciSup_of_le b3 sp (by ring_nf; rfl)) (le_ciSup_of_le b3 sm (by ring_nf; rfl))
  have h4 := key (-1) (-1) (Or.inr rfl) (Or.inr rfl) _
    (le_ciSup_of_le b4 sp (by ring_nf; rfl)) (le_ciSup_of_le b4 sm (by ring_nf; rfl))
  -- `|A + X| + |A − X| ≥ 2|X|`, applied to the two symmetric pairs of signs
  have hsym : ∀ X : ℝ, 2 * |X| ≤ |A + X| + |A - X| := by
    intro X
    have h := abs_sub (A + X) (A - X)
    have hX : (A + X) - (A - X) = 2 * X := by ring
    rwa [hX, abs_mul, abs_two] at h
  have hrq : |r| + |q| ≤ |r + q| + |r - q| := by
    have e1 : 2 * |r| ≤ |r + q| + |r - q| := by
      have h := abs_add_le (r + q) (r - q)
      have hr2 : (r + q) + (r - q) = 2 * r := by ring
      rwa [hr2, abs_mul, abs_two] at h
    have e2 : 2 * |q| ≤ |r + q| + |r - q| := by
      have h := abs_sub (r + q) (r - q)
      have hq2 : (r + q) - (r - q) = 2 * q := by ring
      rwa [hq2, abs_mul, abs_two] at h
    linarith
  have hpsi : ψ sp - ψ sm ≤ |r| + |q| :=
    le_trans (le_trans (le_abs_self _) (hincr sp sm)) (by rw [hr, hq])
  -- combine the four bounds; the sign-linear terms cancel
  have hA1 := hsym (2 * (r + q))
  have hA2 := hsym (2 * (r - q))
  have e1 : |A + (1 * (2 * r) + 1 * (2 * q))| = |A + 2 * (r + q)| := by ring_nf
  have e2 : |A + (-1 * (2 * r) + -1 * (2 * q))| = |A - 2 * (r + q)| := by ring_nf
  have e3 : |A + (1 * (2 * r) + -1 * (2 * q))| = |A + 2 * (r - q)| := by ring_nf
  have e4 : |A + (-1 * (2 * r) + 1 * (2 * q))| = |A - 2 * (r - q)| := by ring_nf
  rw [e1] at h1
  rw [e3] at h2
  rw [e4] at h3
  rw [e2] at h4
  have habs2 : |2 * (r + q)| = 2 * |r + q| := by rw [abs_mul, abs_two]
  have habs3 : |2 * (r - q)| = 2 * |r - q| := by rw [abs_mul, abs_two]
  rw [habs2] at hA1
  rw [habs3] at hA2
  linarith

/-! ### Boolean sign vectors -/

/-- The real sign vector of a Boolean vector: `+1` where the Boolean is `true` and `-1` where it
is `false`. -/
def boolSignVector {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : ℝ := if ε i then 1 else -1

/-- The first sign of a Boolean vector extended by `Fin.cons`. -/
theorem boolSignVector_cons_zero {N : ℕ} (b : Bool) (ε : Fin N → Bool) :
    boolSignVector (Fin.cons b ε) 0 = if b then (1 : ℝ) else -1 := by
  simp [boolSignVector]

/-- The remaining signs of a Boolean vector extended by `Fin.cons`. -/
theorem boolSignVector_cons_succ {N : ℕ} (b : Bool) (ε : Fin N → Bool) (i : Fin N) :
    boolSignVector (Fin.cons b ε) i.succ = boolSignVector ε i := by
  simp [boolSignVector]

/-- Sums over the Boolean vectors of length `N + 1` split into the first sign and the rest. -/
theorem sum_boolVector_succ {N : ℕ} (g : (Fin (N + 1) → Bool) → ℝ) :
    ∑ ε : Fin (N + 1) → Bool, g ε = ∑ ε : Fin N → Bool, ∑ b : Bool, g (Fin.cons b ε) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (N + 1) => Bool)
      (fun p => g (Fin.cons p.1 p.2)) g fun _ => rfl,
    Fintype.sum_prod_type, Finset.sum_comm]

/-- Two independent sums over the Boolean vectors of length `N + 1` split into their first
signs and the rest, with the two new signs outermost. -/
theorem sum_boolVector_succ₂ {N : ℕ} (G : (Fin (N + 1) → Bool) → (Fin (N + 1) → Bool) → ℝ) :
    ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
        G (Fin.cons b₁ ε₁) (Fin.cons b₂ ε₂) =
      ∑ ε₁ : Fin (N + 1) → Bool, ∑ ε₂ : Fin (N + 1) → Bool, G ε₁ ε₂ := by
  calc ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
        G (Fin.cons b₁ ε₁) (Fin.cons b₂ ε₂)
      = ∑ b₁ : Bool, ∑ ε₁ : Fin N → Bool, ∑ b₂ : Bool, ∑ ε₂ : Fin N → Bool,
          G (Fin.cons b₁ ε₁) (Fin.cons b₂ ε₂) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ε₁ : Fin N → Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ ε₂ : Fin N → Bool,
          G (Fin.cons b₁ ε₁) (Fin.cons b₂ ε₂) := Finset.sum_comm
    _ = ∑ ε₁ : Fin N → Bool, ∑ b₁ : Bool, ∑ ε₂ : Fin N → Bool, ∑ b₂ : Bool,
          G (Fin.cons b₁ ε₁) (Fin.cons b₂ ε₂) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ε₁ : Fin (N + 1) → Bool, ∑ ε₂ : Fin (N + 1) → Bool, G ε₁ ε₂ := by
        rw [sum_boolVector_succ fun ε₁ => ∑ ε₂ : Fin (N + 1) → Bool, G ε₁ ε₂]
        exact Finset.sum_congr rfl fun ε₁ _ => Finset.sum_congr rfl fun b₁ _ =>
          (sum_boolVector_succ fun ε₂ => G (Fin.cons b₁ ε₁) ε₂).symm

/-- The Boolean signs and the signs of `FoML.Signs`, as an equivalence. -/
def boolEquivSign : Bool ≃ {z : ℤ // z ∈ ({-1, 1} : Finset ℤ)} where
  toFun b := if b then ⟨1, by simp⟩ else ⟨-1, by simp⟩
  invFun z := decide ((z : ℤ) = 1)
  left_inv b := by cases b <;> simp
  right_inv z := by
    obtain ⟨z, hz⟩ := z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp

/-- Sums over `FoML`'s sign vectors are sums over the Boolean vectors. -/
theorem sum_signs_eq_sum_bool {N : ℕ} (f : (Fin N → ℝ) → ℝ) :
    ∑ σ : Signs N, f (signVector σ) = ∑ ε : Fin N → Bool, f (boolSignVector ε) := by
  refine (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin N)) boolEquivSign)
    (fun ε => f (boolSignVector ε)) (fun σ => f (signVector σ)) fun ε => ?_).symm
  refine congrArg f (funext fun j => ?_)
  simp only [signVector_apply, boolSignVector, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, id_eq, boolEquivSign, Equiv.coe_fn_mk]
  split_ifs <;> norm_num

/-! ### The two-coordinate comparison -/

/-- **Two-coordinate comparison.**  If the increments of `ψ i` are dominated by those of `u i`
and `v i` together, then the Rademacher average of `sup_s (F + ∑_i ε_i ψ_i)` is at most the
average of `sup_s (F + ∑_i (2 ε_{i1} u_i + 2 ε_{i2} v_i))` over two independent sign vectors.
The averages are written without their normalizations: the factor `2^N` on the left is what
turns `2^{-N} ∑_ε` into `4^{-N} ∑_{ε₁} ∑_{ε₂}`. -/
theorem pow_two_mul_sum_iSup_boolSignVector_le [Nonempty S] (N : ℕ) :
    ∀ (F : S → ℝ) (ψ u v : Fin N → S → ℝ), IsBddFun F → (∀ i, IsBddFun (ψ i)) →
      (∀ i, IsBddFun (u i)) → (∀ i, IsBddFun (v i)) →
      (∀ i s t, |ψ i s - ψ i t| ≤ |u i s - u i t| + |v i s - v i t|) →
      (2 : ℝ) ^ N * ∑ ε : Fin N → Bool, ⨆ s, (F s + ∑ i, boolSignVector ε i * ψ i s) ≤
        ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool, ⨆ s,
          (F s + ∑ i, (2 * (boolSignVector ε₁ i * u i s) +
            2 * (boolSignVector ε₂ i * v i s))) := by
  induction N with
  | zero =>
      intro F ψ u v _ _ _ _ _
      simp
  | succ N ih =>
      intro F ψ u v hF hψ hu hv hincr
      -- the offset carried by the remaining signs, and the offset carried by the two new signs
      set R : (Fin N → Bool) → S → ℝ :=
        fun ε s => ∑ i : Fin N, boolSignVector ε i * ψ i.succ s with hR
      set P : Bool → Bool → S → ℝ := fun b₁ b₂ s =>
        F s + (2 * ((if b₁ then (1 : ℝ) else -1) * u 0 s) +
          2 * ((if b₂ then (1 : ℝ) else -1) * v 0 s)) with hP
      have hRbdd : ∀ ε, IsBddFun (R ε) := fun ε =>
        IsBddFun.sum Finset.univ fun i _ => (hψ i.succ).const_mul _
      have hPbdd : ∀ b₁ b₂, IsBddFun (P b₁ b₂) := fun b₁ b₂ =>
        hF.add ((((hu 0).const_mul _).const_mul 2).add (((hv 0).const_mul _).const_mul 2))
      -- replacing the first sign, for a fixed choice of the remaining ones
      have hstep : ∀ ε : Fin N → Bool,
          ∑ b : Bool, ⨆ s, (F s + ∑ i, boolSignVector (Fin.cons b ε) i * ψ i s) ≤
            2⁻¹ * ∑ b₁ : Bool, ∑ b₂ : Bool, ⨆ s, (P b₁ b₂ s + R ε s) := by
        intro ε
        have hsplit : ∀ (b : Bool) (s : S),
            F s + ∑ i, boolSignVector (Fin.cons b ε) i * ψ i s =
              (F s + R ε s) + (if b then (1 : ℝ) else -1) * ψ 0 s := by
          intro b s
          rw [Fin.sum_univ_succ, boolSignVector_cons_zero]
          simp only [hR, boolSignVector_cons_succ]
          ring
        have hpos : (⨆ s, (F s + ∑ i, boolSignVector (Fin.cons true ε) i * ψ i s)) =
            ⨆ s, ((F s + R ε s) + ψ 0 s) :=
          iSup_congr fun s => by rw [hsplit true s]; norm_num
        have hneg : (⨆ s, (F s + ∑ i, boolSignVector (Fin.cons false ε) i * ψ i s)) =
            ⨆ s, ((F s + R ε s) - ψ 0 s) :=
          iSup_congr fun s => by rw [hsplit false s]; norm_num; ring
        have hcomp := iSup_add_sign_le (F := fun s => F s + R ε s) (ψ := ψ 0) (u := u 0)
          (v := v 0) (hF.add (hRbdd ε)) (hψ 0) (hu 0) (hv 0) fun s t => hincr 0 s t
        have hfour : ∑ b₁ : Bool, ∑ b₂ : Bool, ⨆ s, (P b₁ b₂ s + R ε s) =
            ((⨆ s, ((F s + R ε s) + (2 * u 0 s + 2 * v 0 s))) +
                (⨆ s, ((F s + R ε s) + (2 * u 0 s - 2 * v 0 s)))) +
              ((⨆ s, ((F s + R ε s) + (-(2 * u 0 s) + 2 * v 0 s))) +
                (⨆ s, ((F s + R ε s) + (-(2 * u 0 s) - 2 * v 0 s)))) := by
          simp only [Fintype.sum_bool]
          refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg₂ (· + ·) ?_ ?_) <;>
            exact iSup_congr fun s => by simp only [hP]; norm_num; ring
        rw [Fintype.sum_bool, hpos, hneg, hfour]
        linarith [hcomp]
      calc (2 : ℝ) ^ (N + 1) *
            ∑ ε : Fin (N + 1) → Bool, ⨆ s, (F s + ∑ i, boolSignVector ε i * ψ i s)
          = (2 : ℝ) ^ (N + 1) * ∑ ε : Fin N → Bool, ∑ b : Bool,
              ⨆ s, (F s + ∑ i, boolSignVector (Fin.cons b ε) i * ψ i s) := by
            rw [sum_boolVector_succ]
        _ ≤ (2 : ℝ) ^ (N + 1) * ∑ ε : Fin N → Bool,
              2⁻¹ * ∑ b₁ : Bool, ∑ b₂ : Bool, ⨆ s, (P b₁ b₂ s + R ε s) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => hstep ε) (by positivity)
        _ = ∑ b₁ : Bool, ∑ b₂ : Bool,
              (2 : ℝ) ^ N * ∑ ε : Fin N → Bool, ⨆ s, (P b₁ b₂ s + R ε s) := by
            simp only [← Finset.mul_sum, Finset.sum_comm (γ := Bool), Fintype.sum_bool]
            ring
        _ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool, ⨆ s,
              (P b₁ b₂ s + ∑ i : Fin N, (2 * (boolSignVector ε₁ i * u i.succ s) +
                2 * (boolSignVector ε₂ i * v i.succ s))) :=
            Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
              ih (P b₁ b₂) (fun i => ψ i.succ) (fun i => u i.succ) (fun i => v i.succ)
                (hPbdd b₁ b₂) (fun i => hψ i.succ) (fun i => hu i.succ) (fun i => hv i.succ)
                fun i s t => hincr i.succ s t
        _ = ∑ ε₁ : Fin (N + 1) → Bool, ∑ ε₂ : Fin (N + 1) → Bool, ⨆ s,
              (F s + ∑ i, (2 * (boolSignVector ε₁ i * u i s) +
                2 * (boolSignVector ε₂ i * v i s))) := by
            refine Eq.trans ?_ (sum_boolVector_succ₂ fun ε₁ ε₂ => ⨆ s,
              (F s + ∑ i, (2 * (boolSignVector ε₁ i * u i s) +
                2 * (boolSignVector ε₂ i * v i s))))
            refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ =>
              Finset.sum_congr rfl fun ε₁ _ => Finset.sum_congr rfl fun ε₂ _ =>
                iSup_congr fun s => ?_
            rw [Fin.sum_univ_succ, boolSignVector_cons_zero, boolSignVector_cons_zero]
            simp only [hP, boolSignVector_cons_succ]
            ring

/-- **Lemma [lem:two-coordinate-comparison]**, in the normalized form of the manuscript: the
Rademacher average of `sup_s ∑_i ε_i ψ_i(s)` is at most twice the average of
`sup_s ∑_i (ε_{i1} u_i(s) + ε_{i2} v_i(s))` over two independent sign vectors. -/
theorem avg_iSup_boolSignVector_le [Nonempty S] {N : ℕ} {ψ u v : Fin N → S → ℝ}
    (hψ : ∀ i, IsBddFun (ψ i)) (hu : ∀ i, IsBddFun (u i)) (hv : ∀ i, IsBddFun (v i))
    (hincr : ∀ i s t, |ψ i s - ψ i t| ≤ |u i s - u i t| + |v i s - v i t|) :
    (2 ^ N : ℝ)⁻¹ * ∑ ε : Fin N → Bool, ⨆ s, ∑ i, boolSignVector ε i * ψ i s ≤
      2 * ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹ * ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
        ⨆ s, ∑ i, (boolSignVector ε₁ i * u i s + boolSignVector ε₂ i * v i s)) := by
  have hcore := pow_two_mul_sum_iSup_boolSignVector_le (S := S) N (fun _ => 0) ψ u v
    IsBddFun.zero hψ hu hv hincr
  have hL : ∀ ε : Fin N → Bool,
      (⨆ s, ((0 : ℝ) + ∑ i, boolSignVector ε i * ψ i s)) =
        ⨆ s, ∑ i, boolSignVector ε i * ψ i s :=
    fun ε => iSup_congr fun s => zero_add _
  have hR : ∀ ε₁ ε₂ : Fin N → Bool,
      (⨆ s, ((0 : ℝ) + ∑ i, (2 * (boolSignVector ε₁ i * u i s) +
          2 * (boolSignVector ε₂ i * v i s)))) =
        2 * ⨆ s, ∑ i, (boolSignVector ε₁ i * u i s + boolSignVector ε₂ i * v i s) := by
    intro ε₁ ε₂
    rw [Real.mul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    refine iSup_congr fun s => ?_
    rw [zero_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hL, hR, ← Finset.mul_sum] at hcore
  calc (2 ^ N : ℝ)⁻¹ * ∑ ε : Fin N → Bool, ⨆ s, ∑ i, boolSignVector ε i * ψ i s
      = ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹) *
          ((2 : ℝ) ^ N * ∑ ε : Fin N → Bool, ⨆ s, ∑ i, boolSignVector ε i * ψ i s) := by
        field_simp
    _ ≤ ((2 ^ N : ℝ)⁻¹ * (2 ^ N : ℝ)⁻¹) *
          (2 * ∑ ε₁ : Fin N → Bool, ∑ ε₂ : Fin N → Bool,
            ⨆ s, ∑ i, (boolSignVector ε₁ i * u i s + boolSignVector ε₂ i * v i s)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by ring

end OperatorRidgelet
