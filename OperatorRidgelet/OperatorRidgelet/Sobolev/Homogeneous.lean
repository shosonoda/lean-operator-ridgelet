import OperatorRidgelet.Transform.Basic
import OperatorRidgelet.Transform.Gaussian

/-!
# Polynomial moments of a homogeneous direction measure

Appendix I of the manuscript uses one quantitative consequence of homogeneity: a measure `ν`
that is homogeneous of degree `α > 0` and finite on the unit ball has finite moments
`∫ (1 + ‖a‖²)^e dν` for every exponent `2e + α < 0`
(`eq:homogeneous-polynomial-integrability`).

Both statements here are the two steps of that proof: homogeneity scales centred balls,
`ν(B_R) = R^α ν(B_1)`, and the dyadic annuli `2^n < ‖a‖ ≤ 2^{n+1}` then contribute a geometric
series.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Metric
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- Homogeneity of degree `α` scales the centred balls: `ν(B_R) = R^α ν(B_1)` for `R > 0`. -/
theorem IsHomogeneous.measure_closedBall {α : ℝ} {ν : Measure H} (hν : IsHomogeneous α ν)
    {R : ℝ} (hR : 0 < R) :
    ν (closedBall 0 R) = ENNReal.ofReal (R ^ α) * ν (closedBall 0 1) := by
  have hR' : (0 : ℝ) < R⁻¹ := inv_pos.mpr hR
  have hpre : (fun a : H => R⁻¹ • a) ⁻¹' closedBall 0 1 = closedBall 0 R := by
    rw [preimage_smul_closedBall hR', one_div, inv_inv]
  have hconst : |R⁻¹| ^ (-α) = R ^ α := by
    rw [abs_of_pos hR', Real.rpow_neg hR'.le, Real.inv_rpow hR.le, inv_inv]
  have := hν.measure_preimage_smul (inv_ne_zero hR.ne')
    (measurableSet_closedBall (x := (0 : H)) (ε := 1))
  rwa [hpre, hconst] at this

/-- The polynomial moments of a homogeneous measure that is finite on the unit ball:
`∫ (1 + ‖a‖²)^e dν < ∞` whenever `2e + α < 0` (`eq:homogeneous-polynomial-integrability`,
with `e = -d/2`). -/
theorem IsHomogeneous.lintegral_one_add_norm_sq_rpow_lt_top {α e : ℝ} (hα : 0 < α)
    {ν : Measure H} (hν : IsHomogeneous α ν) (hB : ν (closedBall 0 1) ≠ ⊤)
    (he : 2 * e + α < 0) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖ ^ 2) ^ e) ∂ν < ⊤ := by
  have he0 : e ≤ 0 := by nlinarith
  set f : H → ℝ≥0∞ := fun a => ENNReal.ofReal ((1 + ‖a‖ ^ 2) ^ e) with hf
  set B : ℕ → Set H := fun n => closedBall 0 ((2 : ℝ) ^ n) with hBdef
  have hBmono : Monotone B := by
    intro m n hmn
    exact closedBall_subset_closedBall (pow_le_pow_right₀ one_le_two hmn)
  have hBmeas : ∀ n, MeasurableSet (B n) := fun _ => measurableSet_closedBall
  have hcover : ⋃ n, B n = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖a‖ (one_lt_two (α := ℝ))
    exact Set.mem_iUnion.mpr ⟨n, by simpa [hBdef, mem_closedBall_zero_iff] using hn.le⟩
  set ρ : ℝ := (2 : ℝ) ^ (α + 2 * e) with hρdef
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos two_pos _
  have hρlt : ρ < 1 := by
    rw [hρdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(2 * e))) * ν (closedBall 0 1) with hCdef
  have key : ∀ n : ℕ, ∫⁻ a in disjointed B n, f a ∂ν ≤ C * ENNReal.ofReal ρ ^ n := by
    intro n
    match n with
    | 0 =>
      have h0 : disjointed B 0 = closedBall (0 : H) 1 := by
        simp [disjointed_zero, hBdef]
      have hle : ∀ a ∈ closedBall (0 : H) 1, f a ≤ 1 := by
        intro a _
        refine (ENNReal.ofReal_le_one).mpr ?_
        exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖a‖]) he0
      calc ∫⁻ a in disjointed B 0, f a ∂ν
          ≤ ∫⁻ _ in closedBall (0 : H) 1, 1 ∂ν := by
            rw [h0]; exact setLIntegral_mono' measurableSet_closedBall hle
        _ = ν (closedBall 0 1) := by simp
        _ ≤ C * ENNReal.ofReal ρ ^ 0 := by
            rw [pow_zero, mul_one, hCdef]
            refine le_mul_of_one_le_left' ?_
            exact ENNReal.one_le_ofReal.mpr (Real.one_le_rpow one_le_two (by linarith))
    | (n + 1) =>
      have hsub : disjointed B (n + 1) ⊆ B (n + 1) \ B n := by
        have hd := hBmono.disjointed_succ (i := n) (not_isMax n)
        rw [Order.succ_eq_add_one] at hd
        exact hd.subset
      have hmeas : MeasurableSet (disjointed B (n + 1)) :=
        MeasurableSet.disjointed hBmeas _
      have hle : ∀ a ∈ disjointed B (n + 1),
          f a ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * (n : ℝ) * e)) := by
        intro a ha
        have hnot : a ∉ B n := (hsub ha).2
        have hgt : ((2 : ℝ) ^ n) < ‖a‖ := by
          by_contra hcon
          exact hnot (by simpa [hBdef, mem_closedBall_zero_iff] using not_lt.mp hcon)
        have hsq : (2 : ℝ) ^ (2 * (n : ℝ)) ≤ 1 + ‖a‖ ^ 2 := by
          have hpow : (2 : ℝ) ^ (2 * (n : ℝ)) = ((2 : ℝ) ^ n) ^ 2 := by
            rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast, Real.rpow_two]
          have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
          rw [hpow]
          nlinarith
        refine ENNReal.ofReal_le_ofReal ?_
        have := Real.rpow_le_rpow_of_nonpos (by positivity) hsq he0
        rwa [← Real.rpow_mul (by norm_num)] at this
      have hmeasure : ν (disjointed B (n + 1)) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (((n : ℝ) + 1) * α)) * ν (closedBall 0 1) := by
        refine le_trans (measure_mono (hsub.trans Set.sdiff_subset)) ?_
        refine le_of_eq ?_
        rw [hν.measure_closedBall (R := (2 : ℝ) ^ (n + 1)) (by positivity)]
        congr 2
        rw [← Real.rpow_natCast (2 : ℝ) (n + 1), ← Real.rpow_mul (by norm_num)]
        push_cast
        ring_nf
      calc ∫⁻ a in disjointed B (n + 1), f a ∂ν
          ≤ ∫⁻ _ in disjointed B (n + 1), ENNReal.ofReal ((2 : ℝ) ^ (2 * (n : ℝ) * e)) ∂ν :=
            setLIntegral_mono' hmeas hle
        _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * (n : ℝ) * e)) * ν (disjointed B (n + 1)) := by simp
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * (n : ℝ) * e)) *
              (ENNReal.ofReal ((2 : ℝ) ^ (((n : ℝ) + 1) * α)) * ν (closedBall 0 1)) :=
            by gcongr
        _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * (n : ℝ) * e) * (2 : ℝ) ^ (((n : ℝ) + 1) * α)) *
              ν (closedBall 0 1) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            ring
        _ = C * ENNReal.ofReal ρ ^ (n + 1) := by
            have hreal : (2 : ℝ) ^ (2 * (n : ℝ) * e) * (2 : ℝ) ^ (((n : ℝ) + 1) * α)
                = (2 : ℝ) ^ (-(2 * e)) * ((2 : ℝ) ^ (α + 2 * e)) ^ (n + 1) := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ (α + 2 * e)) (n + 1),
                ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
                ← Real.rpow_add (by norm_num)]
              congr 1
              push_cast
              ring
            rw [hreal, ENNReal.ofReal_mul (by positivity), hCdef, hρdef,
              ENNReal.ofReal_pow (by positivity)]
            ring
  have hsum : ∫⁻ a : H, f a ∂ν ≤ ∑' n : ℕ, C * ENNReal.ofReal ρ ^ n := by
    calc ∫⁻ a : H, f a ∂ν = ∫⁻ a in ⋃ n, disjointed B n, f a ∂ν := by
          rw [iUnion_disjointed, hcover, Measure.restrict_univ]
      _ ≤ ∑' n : ℕ, ∫⁻ a in disjointed B n, f a ∂ν := lintegral_iUnion_le _ _
      _ ≤ ∑' n : ℕ, C * ENNReal.ofReal ρ ^ n := ENNReal.tsum_le_tsum key
  refine lt_of_le_of_lt hsum ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top
  · refine ENNReal.inv_lt_top.mpr ?_
    refine tsub_pos_of_lt ?_
    exact ENNReal.ofReal_lt_one.mpr hρlt

end OperatorRidgelet
