import OperatorRidgelet.Sobolev.Defs
import OperatorRidgelet.Sobolev.GaussianDefs
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

/-! ### Proposition `prop:nonbandpass-sobolev` -/

/-- **Proposition [prop:nonbandpass-sobolev]**(i) The Gaussian-derivative filter of order `k`
is a real Schwartz function with Fourier transform `ρ̂_k(ω) = ω^{2k} e^{-ω²}`. -/
theorem prop_nonbandpass_sobolev_i (k : ℕ) (ω : ℝ) :
    filterFourier (gaussDerivFilter k) ω = ((ω ^ (2 * k) * Real.exp (-ω ^ 2) : ℝ) : ℂ) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(ii) The filter is not band pass: its Fourier
transform vanishes only at the origin. -/
theorem prop_nonbandpass_sobolev_ii (k : ℕ) : ¬ IsBandPass (gaussDerivFilter k) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(iii) The filter is nevertheless `α`-admissible,
`0 < C^{(α)}_{ρ_k} < ∞`, in the range `α < 4k + 1`. -/
theorem prop_nonbandpass_sobolev_iii {k : ℕ} {α : ℝ} (hα : 0 < α) (hk : α < 4 * k + 1) :
    IsAdmissible α (gaussDerivFilter k) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(iv) The polynomial moments
`eq:homogeneous-polynomial-integrability` of a homogeneous measure that is finite on the unit
ball: `∫ (1 + ‖a‖²)^e dν < ∞` whenever `2e + α < 0`. -/
theorem prop_nonbandpass_sobolev_iv {α e : ℝ} (hα : 0 < α) {ν : Measure H}
    (hν : IsHomogeneous α ν) (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (he : 2 * e + α < 0) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖ ^ 2) ^ e) ∂ν < ⊤ := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(v) The coefficient of the rays of the filter for
the Gaussian target `g(ξ) = e^{-‖ξ‖²} v` is jointly strongly measurable. -/
theorem prop_nonbandpass_sobolev_v (k : ℕ) (v : Y) :
    StronglyMeasurable (gaussRayCoefficient (H := H) k v) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(vi) Every ray lies in `H^s_ω(ℝ;Y)` and has the
profile `h_a(ω) = ρ̂_k(-ω) g(ωa)` required by `thm:weak-sobolev-synthesis`. -/
theorem prop_nonbandpass_sobolev_vi [CompleteSpace Y] (k : ℕ) (v : Y) {s : ℝ} (hs : 0 ≤ s)
    (a : H) :
    MemRaySobolev s (fun b => gaussRayCoefficient k v (a, b)) ∧
      ∀ ω : ℝ, rayProfile (fun b => gaussRayCoefficient k v (a, b)) ω =
        filterFourier (gaussDerivFilter k) (-ω) • gaussTarget v (ω • a) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(vii) The Sobolev mass `𝔅_s(ρ_k, g)` is finite in
the range `2k > α + 2s - 1/2` of `eq:nonbandpass-order`. -/
theorem prop_nonbandpass_sobolev_vii {k : ℕ} {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (hk : α + 2 * s - 1 / 2 < 2 * k) {ν : Measure H} (hν : IsHomogeneous α ν)
    (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (v : Y) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s *
      raySobolevNorm s fun b => gaussRayCoefficient k v (a, b)) ∂ν ≠ ⊤ := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(viii) The Sobolev test
`q_{α,ρ_k}(ω) = ρ̂_k(-ω) |ω|^{-α}` lies in `H^s_ω(ℝ)` in the same range. -/
theorem prop_nonbandpass_sobolev_viii {k : ℕ} {α s : ℝ} (hα : 0 < α) (hs : 1 / 2 < s)
    (hk : α + 2 * s - 1 / 2 < 2 * k) :
    MemRaySobolev s (gaussSobolevRay k α) ∧
      ∀ ω : ℝ, rayProfile (gaussSobolevRay k α) ω =
        filterFourier (gaussDerivFilter k) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
  sorry

/-- **Proposition [prop:nonbandpass-sobolev]**(ix) Consequently the filter satisfies every
hypothesis of `thm:weak-sobolev-synthesis`: for each continuous activation of growth order
`p < s - 1/2` the synthesis of the rays is absolutely convergent and reproduces the target. -/
theorem prop_nonbandpass_sobolev_ix [CompleteSpace Y] {k : ℕ} {α s p Cσ : ℝ} (hα : 0 < α)
    (hp : 0 ≤ p) (hps : p + 1 / 2 < s) (hk : α + 2 * s - 1 / 2 < 2 * k)
    {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν)
    (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (v : Y) {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • gaussRayCoefficient k v q ∂(ν.prod volume) =
      sobolevPairing σ (gaussSobolevRay k α) • spectralTarget ν (gaussTarget v) x := by
  sorry

end OperatorRidgelet.Paper
