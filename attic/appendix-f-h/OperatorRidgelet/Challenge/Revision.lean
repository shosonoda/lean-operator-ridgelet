/-! Historical fragments; see the archive README. -/

/-- **Theorem [thm:H.1]** Bounded-set finite direction weights retain universality. -/
theorem thm_H_1_dense (ν : Measure H) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (hfin : ∀ R : ℝ, ν (Metric.closedBall (0 : H) R) < ⊤)
    (β : TemperedDistribution ℝ ℂ) (b : ℝ → ℝ)
    (hβ : IsTemperedFunction β b) (hpoly : ¬ IsPolynomialFun b) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsBandPass ρ) (hC : temperedAdmissibilityConst α β ρ = 1) (I : Set ℝ)
    (hI : IsFrequencyWindow ρ I) {f : H → ℂ} (hf : Continuous f) {K : Set H}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → ℂ) (a : Fin N → H) (c : Fin N → ℝ),
      compactSupNorm K (fun x => f x - finiteNetwork (fun t => (b t : ℂ)) v a c x) < ε := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:H.1]** Abstract input weights retain completed backprojection. -/
theorem thm_H_1_backprojection (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hα : 0 < α) (hν : IsHomogeneous α ν)
    (ρ : SchwartzMap ℝ ℝ) (hρ : IsAdmissible α ρ) (f : spectralRange μ ν) :
    backprojection α ν ρ (ridgeletExtension μ ν ρ f) =ᵐ[ν]
      fun ξ => admissibilityConst α ρ * (f : Lp ℂ 2 ν) ξ := by
  sorry

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- **Theorem [thm:H.1]** Stability holds for an arbitrary probability input weight. -/
theorem thm_H_1_stability (μ ν : Measure H) [IsProbabilityMeasure μ]
    [SigmaFinite ν] {α : ℝ} (hν : IsHomogeneous α ν) (ρ : SchwartzMap ℝ ℝ)
    (hρ : IsAdmissible α ρ) (f : spectralRange μ ν) (γ : Lp ℂ 2 (parameterMeasure ν))
    {δ : ℝ} (hδ : ‖γ - ridgeletExtension μ ν ρ f‖ ≤ δ) :
    ‖coefficientDecoder α μ ν ρ γ - f‖ ≤ δ / Real.sqrt (admissibilityConst α ρ) := by
  sorry
