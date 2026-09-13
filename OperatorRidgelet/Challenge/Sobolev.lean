import OperatorRidgelet.Sobolev.Defs
import OperatorRidgelet.Reconstruction.Defs

/-!
# comparator challenge: Appendix C, the weak Sobolev tools

Statements with proof `sorry`, identical to `OperatorRidgelet.Paper.Sobolev`.  This module
imports only definition modules, never `OperatorRidgelet.Paper`.

The Sobolev space `H^s_ω(ℝ;Y)` of the manuscript is carried by the pair of a profile `h` and its
inverse Fourier transform `γ`, as documented in `OperatorRidgelet.Sobolev.Defs`: `MemRaySobolev`
is the membership, `raySobolevNorm` the norm `eq:sobolev-norm`, and `rayProfile γ = γ̂` the
profile of a coefficient.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Lemma [lem:sobolev-tools]**(i) The weighted inverse Fourier estimate
`∫ ⟨t⟩^r ‖γ(t)‖ dt ≤ A_{s,r} ‖h‖_{H^s_ω}` (`eq:sobolev-weighted-l1`) for `0 ≤ r < s - 1/2`,
where `γ = ȟ` and `A_{s,r} = (2π)^{-1/2}(∫ (1+t²)^{-(s-r)} dt)^{1/2}`. -/
theorem lem_sobolev_tools_i {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) :
    ∫ t : ℝ, (bracket t ^ r : ℝ) * ‖γ t‖ ≤ sobolevMomentConst s r * raySobolevNorm s γ := by
  sorry

/-- **Lemma [lem:sobolev-tools]**(ii) Reflection `R h(ω) = h(-ω)` is an isometry of
`H^s_ω(ℝ;Y)`: the reflected coefficient is again in the class with the same norm, and its
profile is the reflected profile. -/
theorem lem_sobolev_tools_ii {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    MemRaySobolev s (fun t => γ (-t)) ∧
      raySobolevNorm s (fun t => γ (-t)) = raySobolevNorm s γ ∧
      ∀ ω : ℝ, rayProfile (fun t => γ (-t)) ω = rayProfile γ (-ω) := by
  sorry

/-- **Lemma [lem:sobolev-tools]**(iii) Modulation `M_u h(ω) = e^{iuω} h(ω)` maps `H^s_ω(ℝ;Y)`
to itself with `‖M_u h‖_{H^s_ω} ≤ (1 + |u|)^s ‖h‖_{H^s_ω}` (`eq:sobolev-modulation`); its
coefficient is the translate `γ(· + u)`. -/
theorem lem_sobolev_tools_iii {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (u : ℝ) :
    MemRaySobolev s (fun t => γ (t + u)) ∧
      raySobolevNorm s (fun t => γ (t + u)) ≤ ((1 + |u|) ^ s : ℝ) * raySobolevNorm s γ ∧
      ∀ ω : ℝ, rayProfile (fun t => γ (t + u)) ω =
        Complex.exp (((u * ω : ℝ) : ℂ) * Complex.I) • rayProfile γ ω := by
  sorry

/-- **Lemma [lem:sobolev-tools]**(iv) The map `(u, h) ↦ M_u h` is jointly continuous: if the
biases converge and the profiles converge in `H^s_ω(ℝ;Y)`, then so do the modulated profiles. -/
theorem lem_sobolev_tools_iv {S : Type*} {l : Filter S} {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y}
    {γ' : S → ℝ → Y} {u : S → ℝ} {u₀ : ℝ} (hγ : MemRaySobolev s γ)
    (hγ' : ∀ i, MemRaySobolev s (γ' i)) (hu : Tendsto u l (nhds u₀))
    (hconv : Tendsto (fun i => raySobolevNorm s (fun t => γ' i t - γ t)) l (nhds 0)) :
    Tendsto (fun i => raySobolevNorm s (fun t => γ' i (t + u i) - γ (t + u₀))) l (nhds 0) := by
  sorry

/-- **Lemma [lem:sobolev-pairing]**(i) For a continuous activation of polynomial growth `p` and
`s > p + 1/2`, the weighted activation `⟨·⟩^{-s} σ` is square integrable, that is
`b_{σ,s} = ‖⟨·⟩^{-s}σ‖_2 < ∞`. -/
theorem lem_sobolev_pairing_i {σ : ℝ → ℂ} {p s C : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    (hσ : Continuous σ) (hbound : ∀ t : ℝ, ‖σ t‖ ≤ C * (1 + |t|) ^ p) :
    MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume := by
  sorry

/-- **Lemma [lem:sobolev-pairing]**(ii) The pairing `L_σ^Y(h) = ∫ σ(t) γ(-t) dt` converges
absolutely and is bounded: `‖L_σ^Y(h)‖ ≤ (2π)^{-1/2} b_{σ,s} ‖h‖_{H^s_ω}`, so it is an element
of the bilinear dual of `H^s_ω(ℝ;Y)` with that norm (`eq:sobolev-pairing`). -/
theorem lem_sobolev_pairing_ii {σ : ℝ → ℂ} {s : ℝ} {γ : ℝ → Y}
    (hσ : MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume)
    (hγ : MemRaySobolev s γ) :
    Integrable (fun t : ℝ => σ t • γ (-t)) volume ∧
      ‖sobolevPairing σ γ‖ ≤
        sobolevPairingConst σ s / Real.sqrt (2 * Real.pi) * raySobolevNorm s γ := by
  sorry

/-- **Lemma [lem:sobolev-pairing]**(iii) The bias translation of the activation is the
modulation of the profile: `∫ σ(u - b) γ(b) db = L_σ^Y(M_u h)` (`eq:sobolev-bias-pairing`). -/
theorem lem_sobolev_pairing_iii (σ : ℝ → ℂ) (γ : ℝ → Y) (u : ℝ) :
    ∫ b : ℝ, σ (u - b) • γ b = sobolevPairing σ (fun t => γ (t + u)) := by
  sorry

/-! ### Theorem `thm:weak-sobolev-synthesis` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- **Theorem [thm:weak-sobolev-synthesis]**(i) The coefficient moments `eq:sobolev-moments`:
for `0 ≤ r < s - 1/2`,
`∫ (1 + ‖a‖ + |b|)^r ‖γ_g(a,b)‖ dν db ≤ 2^{r/2} A_{s,r} 𝔅_s(ρ,g)`. -/
theorem thm_weak_sobolev_synthesis_i [CompleteSpace Y] {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s)
    (ν : Measure H) [SFinite ν] {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b)) :
    ∫⁻ q : H × ℝ, ENNReal.ofReal ((1 + ‖q.1‖ + |q.2|) ^ r * ‖γ q‖) ∂(ν.prod volume) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r / 2) * sobolevMomentConst s r) *
        ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν := by
  sorry

/-- **Theorem [thm:weak-sobolev-synthesis]**(ii) The coefficient measure
`Γ_g = γ_g (ν ⊗ db)` is finite. -/
theorem thm_weak_sobolev_synthesis_ii [CompleteSpace Y] {s : ℝ} (hs : 1 / 2 < s)
    (ν : Measure H) [SFinite ν]
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Integrable γ (ν.prod volume) := by
  sorry

/-- **Theorem [thm:weak-sobolev-synthesis]**(iii) The synthesis identity
`eq:weak-sobolev-synthesis`: the ordinary, absolutely convergent synthesis of the coefficient
is `C^{(α)}_{σ,ρ} f_g`, the cross constant being the Sobolev pairing of `σ` with the coefficient
of `q_{α,ρ}`. -/
theorem thm_weak_sobolev_synthesis_iii [CompleteSpace Y] {s p α Cσ : ℝ} (hp : 0 ≤ p)
    (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν) {ρ : SchwartzMap ℝ ℝ}
    {g : H → Y} (hgm : StronglyMeasurable g) {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hprofile : ∀ᵐ a ∂ν, ∀ ω : ℝ,
      rayProfile (fun b => γ (a, b)) ω = filterFourier ρ (-ω) • g (ω • a))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤)
    {γq : ℝ → ℂ} (hγq : MemRaySobolev s γq)
    (hqprofile : ∀ ω : ℝ, rayProfile γq ω = filterFourier ρ (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ))
    (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) =
      sobolevPairing σ γq • spectralTarget ν g x := by
  sorry

/-- **Theorem [thm:weak-sobolev-synthesis]**(iv) The absolute convergence is uniform on bounded
input sets: on `‖x‖ ≤ R` the synthesis integrand has one integrable majorant. -/
theorem thm_weak_sobolev_synthesis_iv [CompleteSpace Y] {s p Cσ R : ℝ} (hp : 0 ≤ p)
    (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ}
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    ∃ M : H × ℝ → ℝ, Integrable M (ν.prod volume) ∧
      ∀ x : H, ‖x‖ ≤ R → ∀ q : H × ℝ, ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ ≤ M q := by
  sorry

/-- **Theorem [thm:weak-sobolev-synthesis]**(v) The synthesis is continuous. -/
theorem thm_weak_sobolev_synthesis_v [CompleteSpace Y] {s p Cσ : ℝ} (hp : 0 ≤ p)
    (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Continuous fun x : H => ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) := by
  sorry

end OperatorRidgelet.Paper
