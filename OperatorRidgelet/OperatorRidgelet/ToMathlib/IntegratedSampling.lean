import OperatorRidgelet.ToMathlib.MeasurePi

/-! # Integrated second-moment bounds for Hilbert-valued sample means -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Jensen's second-moment inequality, obtained from the one-sample variance identity. -/
theorem norm_integral_sq_le_integral_norm_sq (p : Measure Ω) [IsProbabilityMeasure p]
    {f : Ω → Y} (hf : MemLp f 2 p) : ‖∫ ω, f ω ∂p‖ ^ 2 ≤ ∫ ω, ‖f ω‖ ^ 2 ∂p := by
  have h := integral_norm_sq_sampleMean p hf 1 (N := 1) (by decide)
  have hn : 0 ≤ ∫ ω : Fin 1 → Ω,
      ‖(1 / (1 : ℝ)) • ∑ j, f (ω j) - (1 : ℝ) • ∫ ω', f ω' ∂p‖ ^ 2
      ∂Measure.pi (fun _ : Fin 1 => p) := integral_nonneg fun _ => sq_nonneg _
  norm_num only [Nat.cast_one, one_div, inv_one, one_smul, one_pow, div_one] at h hn
  rw [h] at hn
  linarith

/-- A square-integrable family of atoms has a square-integrable pointwise mean. -/
theorem memLp_integral_family (p : Measure Ω) [IsProbabilityMeasure p]
    (ζ : Measure X) [IsProbabilityMeasure ζ] {Φ : X → Ω → Y}
    (hΦ : MemLp (Function.uncurry Φ) 2 (ζ.prod p))
    (hs : ∀ x, MemLp (Φ x) 2 p) : MemLp (fun x => ∫ ω, Φ x ω ∂p) 2 ζ := by
  have hm := hΦ.1.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hΦ.1).mp hΦ
  have hb : Integrable (fun x => ∫ ω, ‖Φ x ω‖ ^ 2 ∂p) ζ := hi.integral_prod_left
  apply hb.mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_integral_sq_le_integral_norm_sq p (hs x)

/-- The expected integrated squared error of an empirical mean is bounded by its
integrated second moment divided by the number of samples. -/
theorem integral_integral_norm_sq_sampleMean_le (p : Measure Ω) [IsProbabilityMeasure p]
    (ζ : Measure X) [IsProbabilityMeasure ζ] {Φ : X → Ω → Y}
    (hΦ : MemLp (Function.uncurry Φ) 2 (ζ.prod p))
    (hs : ∀ x, MemLp (Φ x) 2 p) (V : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, (∫ x, ‖(V / N : ℝ) • ∑ j, Φ x (ω j) - V • ∫ θ, Φ x θ ∂p‖ ^ 2 ∂ζ)
        ∂Measure.pi (fun _ : Fin N => p) ≤
      V ^ 2 / N * ∫ θ, (∫ x, ‖Φ x θ‖ ^ 2 ∂ζ) ∂p := by
  let q := Measure.pi (fun _ : Fin N => p)
  have hj (j : Fin N) : MemLp (fun z : (Fin N → Ω) × X => Φ z.2 (z.1 j)) 2 (q.prod ζ) := by
    exact hΦ.comp_measurePreserving
      (((MeasurePreserving.id ζ).prod (measurePreserving_eval (fun _ : Fin N => p) j)).comp
        Measure.measurePreserving_swap)
  have hm := memLp_integral_family p ζ hΦ hs
  have hmp : MemLp (fun z : (Fin N → Ω) × X => ∫ θ, Φ z.2 θ ∂p) 2 (q.prod ζ) :=
    hm.comp_measurePreserving ⟨measurable_snd, Measure.snd_prod⟩
  have herr : MemLp (fun z : (Fin N → Ω) × X =>
      (V / N : ℝ) • ∑ j, Φ z.2 (z.1 j) - V • ∫ θ, Φ z.2 θ ∂p) 2 (q.prod ζ) :=
    ((memLp_finsetSum Finset.univ fun j _ => hj j).const_smul (V / N)).sub (hmp.const_smul V)
  have hi := (memLp_two_iff_integrable_sq_norm herr.1).mp herr
  rw [integral_integral_swap hi]
  have hbound : Integrable (fun x => V ^ 2 / N * ∫ θ, ‖Φ x θ‖ ^ 2 ∂p) ζ :=
    ((memLp_two_iff_integrable_sq_norm hΦ.1).mp hΦ).integral_prod_left.const_mul _
  calc
    _ ≤ ∫ x, V ^ 2 / N * ∫ θ, ‖Φ x θ‖ ^ 2 ∂p ∂ζ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        hbound
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [integral_norm_sq_sampleMean p (hs x) V hN]
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
    _ = _ := by
      rw [integral_const_mul, integral_integral_swap ((memLp_two_iff_integrable_sq_norm hΦ.1).mp hΦ)]
