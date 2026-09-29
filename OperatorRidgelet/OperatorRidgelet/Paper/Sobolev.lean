import OperatorRidgelet.Sobolev.Defs
import OperatorRidgelet.Sobolev.Synthesis
import OperatorRidgelet.Sobolev.Basic
import OperatorRidgelet.Sobolev.Pairing
import OperatorRidgelet.Sobolev.GaussianSobolev

/-!
# Statements of Appendix C: Appendix C, the Sobolev tools

Each item is `theorem OperatorRidgelet.Paper.<kind>_<number>[_<part>]`, identical to its twin in
`Challenge.Sobolev`, and proved from the library.

For Hilbert-valued `Y`, the Bessel potential space `H^s_ω(ℝ;Y)` is represented by a profile
`h` and its inverse Fourier transform `γ`. As documented in `OperatorRidgelet.Sobolev.Defs`,
`MemRaySobolev s γ` and `raySobolevNorm s γ` express the weighted inverse-transform condition
and norm `eq:sobolev-norm`, and `rayProfile γ = γ̂`. For general Banach `Y`, every use of this
notation refers directly to the specified weighted inverse transform; no Plancherel identity
is assumed.
-/

noncomputable section

namespace OperatorRidgelet.Paper

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Lemma [lem:C.3]**(i) The weighted inverse Fourier estimate
`∫ ⟨t⟩^r ‖γ(t)‖ dt ≤ A_{s,r} ‖h‖_{H^s_ω}` (`eq:sobolev-weighted-l1`) for `0 ≤ r < s - 1/2`,
where `γ = ȟ` and `A_{s,r} = (2π)^{-1/2}(∫ (1+t²)^{-(s-r)} dt)^{1/2}`. -/
theorem lem_C_3_i {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s) {γ : ℝ → Y}
    (hγ : MemRaySobolev s γ) :
    ∫ t : ℝ, (bracket t ^ r : ℝ) * ‖γ t‖ ≤ sobolevMomentConst s r * raySobolevNorm s γ := by
  exact integral_bracket_rpow_norm_le hr0 hrs hγ

/-- **Lemma [lem:C.3]**(ii) Reflection `R h(ω) = h(-ω)` is an isometry of
`H^s_ω(ℝ;Y)`: the reflected coefficient is again in the class with the same norm, and its
profile is the reflected profile. -/
theorem lem_C_3_ii {s : ℝ} {γ : ℝ → Y} (hγ : MemRaySobolev s γ) :
    MemRaySobolev s (fun t => γ (-t)) ∧
      raySobolevNorm s (fun t => γ (-t)) = raySobolevNorm s γ ∧
      ∀ ω : ℝ, rayProfile (fun t => γ (-t)) ω = rayProfile γ (-ω) := by
  exact ⟨memRaySobolev_neg hγ, raySobolevNorm_neg s γ, rayProfile_neg γ⟩

/-- **Lemma [lem:C.3]**(iii) Modulation `M_u h(ω) = e^{iuω} h(ω)` maps `H^s_ω(ℝ;Y)`
to itself with `‖M_u h‖_{H^s_ω} ≤ (1 + |u|)^s ‖h‖_{H^s_ω}` (`eq:sobolev-modulation`); its
coefficient is the translate `γ(· + u)`. -/
theorem lem_C_3_iii {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y} (hγ : MemRaySobolev s γ)
    (u : ℝ) :
    MemRaySobolev s (fun t => γ (t + u)) ∧
      raySobolevNorm s (fun t => γ (t + u)) ≤ ((1 + |u|) ^ s : ℝ) * raySobolevNorm s γ ∧
      ∀ ω : ℝ, rayProfile (fun t => γ (t + u)) ω =
        Complex.exp (((u * ω : ℝ) : ℂ) * Complex.I) • rayProfile γ ω := by
  exact ⟨memRaySobolev_translate hs hγ u, raySobolevNorm_translate_le hs hγ u,
    rayProfile_translate γ u⟩

/-- **Lemma [lem:C.3]**(iv) The map `(u, h) ↦ M_u h` is jointly continuous: if the
biases converge and the profiles converge in `H^s_ω(ℝ;Y)`, then so do the modulated profiles. -/
theorem lem_C_3_iv {S : Type*} {l : Filter S} {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → Y}
    {γ' : S → ℝ → Y} {u : S → ℝ} {u₀ : ℝ} (hγ : MemRaySobolev s γ)
    (hγ' : ∀ i, MemRaySobolev s (γ' i)) (hu : Tendsto u l (nhds u₀))
    (hconv : Tendsto (fun i => raySobolevNorm s (fun t => γ' i t - γ t)) l (nhds 0)) :
    Tendsto (fun i => raySobolevNorm s (fun t => γ' i (t + u i) - γ (t + u₀))) l (nhds 0) := by
  exact tendsto_raySobolevNorm_modulation hs hγ hγ' hu hconv

/-- **Lemma [lem:C.4]**(i) For a continuous activation of polynomial growth `p` and
`s > p + 1/2`, the weighted activation `⟨·⟩^{-s} σ` is square integrable, that is
`b_{σ,s} = ‖⟨·⟩^{-s}σ‖_2 < ∞`. -/
theorem lem_C_4_i {σ : ℝ → ℂ} {p s C : ℝ} (hp : 0 ≤ p) (hps : p + 1 / 2 < s)
    (hσ : Continuous σ) (hbound : ∀ t : ℝ, ‖σ t‖ ≤ C * (1 + |t|) ^ p) :
    MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume := by
  exact memLp_bracket_rpow_neg_smul hp hps hσ hbound

/-- **Lemma [lem:C.4]**(ii) The pairing `L_σ^Y(h) = ∫ σ(t) γ(-t) dt` converges
absolutely and is bounded: `‖L_σ^Y(h)‖ ≤ (2π)^{-1/2} b_{σ,s} ‖h‖_{H^s_ω}`, so it is an element
of the bilinear dual of `H^s_ω(ℝ;Y)` with that norm (`eq:sobolev-pairing`). -/
theorem lem_C_4_ii {σ : ℝ → ℂ} {s : ℝ} {γ : ℝ → Y}
    (hσ : MemLp (fun t : ℝ => (bracket t ^ (-s) : ℝ) • σ t) 2 volume)
    (hγ : MemRaySobolev s γ) :
    Integrable (fun t : ℝ => σ t • γ (-t)) volume ∧
      ‖sobolevPairing σ γ‖ ≤
        sobolevPairingConst σ s / Real.sqrt (2 * Real.pi) * raySobolevNorm s γ := by
  exact ⟨integrable_smul_neg hσ hγ, norm_sobolevPairing_le hσ hγ⟩

/-- **Lemma [lem:C.4]**(iii) The bias translation of the activation is the
modulation of the profile: `∫ σ(u - b) γ(b) db = L_σ^Y(M_u h)` (`eq:sobolev-bias-pairing`). -/
theorem lem_C_4_iii (σ : ℝ → ℂ) (γ : ℝ → Y) (u : ℝ) :
    ∫ b : ℝ, σ (u - b) • γ b = sobolevPairing σ (fun t => γ (t + u)) := by
  exact integral_smul_sub_eq_sobolevPairing_translate σ γ u

/-! ### Theorem `thm:5.6` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H]

/-- **Theorem [thm:5.6]**(i) The coefficient moments `eq:sobolev-moments`:
for `0 ≤ r < s - 1/2`,
`∫ (1 + ‖a‖ + |b|)^r ‖γ_g(a,b)‖ dν db ≤ 2^{r/2} A_{s,r} 𝔅_s(ρ,g)`. -/
theorem thm_5_6_i [CompleteSpace Y] {s r : ℝ} (hr0 : 0 ≤ r) (hrs : r + 1 / 2 < s)
    (ν : Measure H) [SFinite ν] {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b)) :
    ∫⁻ q : H × ℝ, ENNReal.ofReal ((1 + ‖q.1‖ + |q.2|) ^ r * ‖γ q‖) ∂(ν.prod volume) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r / 2) * sobolevMomentConst s r) *
        ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν := by
  have h2 : Real.sqrt 2 ^ r = (2 : ℝ) ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [← h2]
  exact lintegral_prod_moment_le hr0 hrs hγm hray

/-- **Theorem [thm:5.6]**(ii) The coefficient measure
`Γ_g = γ_g (ν ⊗ db)` is finite. -/
theorem thm_5_6_ii [CompleteSpace Y] {s : ℝ} (hs : 1 / 2 < s)
    (ν : Measure H) [SFinite ν]
    {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Integrable γ (ν.prod volume) := by
  exact integrable_coefficient hs hγm hray hB

/-- **Theorem [thm:5.6]**(iii) The synthesis identity
`eq:weak-sobolev-synthesis`: the ordinary, absolutely convergent synthesis of the coefficient
is `C^{(α)}_{σ,ρ} f_g`, the cross constant being the Sobolev pairing of `σ` with the coefficient
of `q_{α,ρ}`. -/
theorem thm_5_6_iii [CompleteSpace Y] {s p α Cσ : ℝ} (hp : 0 ≤ p)
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
  exact integral_synthesis_eq_pairing_smul hp hps hν hgm hσc hσg hγm hray hprofile hB hγq
    hqprofile x

/-- **Theorem [thm:5.6]**(iv) The absolute convergence is uniform on bounded
input sets: on `‖x‖ ≤ R` the synthesis integrand has one integrable majorant. -/
theorem thm_5_6_iv [CompleteSpace Y] {s p Cσ R : ℝ} (hp : 0 ≤ p)
    (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ}
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    ∃ M : H × ℝ → ℝ, Integrable M (ν.prod volume) ∧
      ∀ x : H, ‖x‖ ≤ R → ∀ q : H × ℝ, ‖σ (⟪q.1, x⟫ - q.2) • γ q‖ ≤ M q := by
  refine ⟨fun q => Cσ * max 1 R ^ p * ((1 + ‖q.1‖ + |q.2|) ^ p * ‖γ q‖),
    (integrable_moment hp hps hγm hray hB).const_mul _, fun x hx q => ?_⟩
  exact norm_synthesis_le_majorant hp hσg hx γ q

/-- **Theorem [thm:5.6]**(v) The synthesis is continuous. -/
theorem thm_5_6_v [CompleteSpace Y] {s p Cσ : ℝ} (hp : 0 ≤ p)
    (hps : p + 1 / 2 < s)
    {ν : Measure H} [SFinite ν] {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) {γ : H × ℝ → Y} (hγm : StronglyMeasurable γ)
    (hray : ∀ᵐ a ∂ν, MemRaySobolev s fun b => γ (a, b))
    (hB : ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s * raySobolevNorm s fun b => γ (a, b)) ∂ν ≠ ⊤) :
    Continuous fun x : H => ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • γ q ∂(ν.prod volume) := by
  exact continuous_synthesis hp hps hσc hσg hγm hray hB

/-! ### Proposition `prop:5.8` -/

/-- **Proposition [prop:5.8]**(i) The Gaussian-derivative filter of order `k`
is a real Schwartz function with Fourier transform `ρ̂_k(ω) = ω^{2k} e^{-ω²}`. -/
theorem prop_5_8_i (k : ℕ) (ω : ℝ) :
    filterFourier (gaussDerivFilter k) ω = ((ω ^ (2 * k) * Real.exp (-ω ^ 2) : ℝ) : ℂ) := by
  exact filterFourier_gaussDerivFilter k ω

/-- **Proposition [prop:5.8]**(ii) The filter is not band pass: its Fourier
transform vanishes only at the origin. -/
theorem prop_5_8_ii (k : ℕ) : ¬ IsBandPass (gaussDerivFilter k) := by
  exact not_isBandPass_gaussDerivFilter k

/-- **Proposition [prop:5.8]**(iii) The filter is nevertheless `α`-admissible,
`0 < C^{(α)}_{ρ_k} < ∞`, in the range `α < 4k + 1`. -/
theorem prop_5_8_iii {k : ℕ} {α : ℝ} (hα : 0 < α) (hk : α < 4 * k + 1) :
    IsAdmissible α (gaussDerivFilter k) := by
  exact isAdmissible_gaussDerivFilter hk

/-- **Proposition [prop:5.8]**(iv) The polynomial moments
`eq:homogeneous-polynomial-integrability` of a homogeneous measure that is finite on the unit
ball: `∫ (1 + ‖a‖²)^e dν < ∞` whenever `2e + α < 0`. -/
theorem prop_5_8_iv {α e : ℝ} (hα : 0 < α) {ν : Measure H}
    (hν : IsHomogeneous α ν) (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (he : 2 * e + α < 0) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖ ^ 2) ^ e) ∂ν < ⊤ := by
  exact hν.lintegral_one_add_norm_sq_rpow_lt_top hα hB he

/-- **Proposition [prop:5.8]**(v) The coefficient associated with the filter for
the Gaussian target `g(ξ) = e^{-‖ξ‖²} v` is jointly strongly measurable. -/
theorem prop_5_8_v (k : ℕ) (v : Y) :
    StronglyMeasurable (gaussRayCoefficient (H := H) k v) := by
  exact stronglyMeasurable_gaussRayCoefficient k v

/-- **Proposition [prop:5.8]**(vi) Every profile belongs to `H^s_ω(ℝ;Y)` and
equals the
profile `h_a(ω) = ρ̂_k(-ω) g(ωa)` required by `thm:5.6`. -/
theorem prop_5_8_vi [CompleteSpace Y] (k : ℕ) (v : Y) {s : ℝ} (hs : 0 ≤ s)
    (a : H) :
    MemRaySobolev s (fun b => gaussRayCoefficient k v (a, b)) ∧
      ∀ ω : ℝ, rayProfile (fun b => gaussRayCoefficient k v (a, b)) ω =
        filterFourier (gaussDerivFilter k) (-ω) • gaussTarget v (ω • a) := by
  exact ⟨memRaySobolev_gaussRayCoefficient k v hs a,
    rayProfile_gaussRayCoefficient k v a⟩

/-- **Proposition [prop:5.8]**(vii) The Sobolev mass `𝔅_s(ρ_k, g)` is finite in
the range `2k > α + 2s - 1/2` of `eq:nonbandpass-order`. -/
theorem prop_5_8_vii {k : ℕ} {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (hk : α + 2 * s - 1 / 2 < 2 * k) {ν : Measure H} (hν : IsHomogeneous α ν)
    (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (v : Y) :
    ∫⁻ a : H, ENNReal.ofReal ((1 + ‖a‖) ^ s *
      raySobolevNorm s fun b => gaussRayCoefficient k v (a, b)) ∂ν ≠ ⊤ := by
  exact lintegral_raySobolevNorm_gaussRayCoefficient_ne_top hα hs hk hν hB v

/-- **Proposition [prop:5.8]**(viii) The Sobolev test
`q_{α,ρ_k}(ω) = ρ̂_k(-ω) |ω|^{-α}` lies in `H^s_ω(ℝ)` in the same range. -/
theorem prop_5_8_viii {k : ℕ} {α s : ℝ} (hα : 0 < α) (hs : 1 / 2 < s)
    (hk : α + 2 * s - 1 / 2 < 2 * k) :
    MemRaySobolev s (gaussSobolevRay k α) ∧
      ∀ ω : ℝ, rayProfile (gaussSobolevRay k α) ω =
        filterFourier (gaussDerivFilter k) (-ω) * ((|ω| ^ (-α) : ℝ) : ℂ) := by
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    push_cast at hk
    linarith
  have hk2 : α < 2 * k := by linarith
  exact ⟨memRaySobolev_gaussSobolevRay hα (by linarith) hk,
    rayProfile_gaussSobolevRay hk1 hα hk2⟩

/-- **Proposition [prop:5.8]**(ix) Consequently the filter satisfies every
hypothesis of `thm:5.6`: for each continuous activation of growth order
`p < s - 1/2` the synthesis of the coefficient is absolutely convergent and reproduces the target.
-/
theorem prop_5_8_ix [CompleteSpace Y] {k : ℕ} {α s p Cσ : ℝ} (hα : 0 < α)
    (hp : 0 ≤ p) (hps : p + 1 / 2 < s) (hk : α + 2 * s - 1 / 2 < 2 * k)
    {ν : Measure H} [SFinite ν] (hν : IsHomogeneous α ν)
    (hB : ν (Metric.closedBall 0 1) ≠ ⊤) (v : Y) {σ : ℝ → ℂ} (hσc : Continuous σ)
    (hσg : ∀ t : ℝ, ‖σ t‖ ≤ Cσ * (1 + |t|) ^ p) (x : H) :
    ∫ q : H × ℝ, σ (⟪q.1, x⟫ - q.2) • gaussRayCoefficient k v q ∂(ν.prod volume) =
      sobolevPairing σ (gaussSobolevRay k α) • spectralTarget ν (gaussTarget v) x := by
  have hs : 1 / 2 < s := by linarith
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    push_cast at hk
    linarith
  have hk2 : α < 2 * k := by linarith
  refine integral_synthesis_eq_pairing_smul hp hps hν ?_ hσc hσg
    (stronglyMeasurable_gaussRayCoefficient k v)
    (Filter.Eventually.of_forall fun a =>
      memRaySobolev_gaussRayCoefficient k v (by linarith) a)
    (Filter.Eventually.of_forall fun a => rayProfile_gaussRayCoefficient k v a)
    (lintegral_raySobolevNorm_gaussRayCoefficient_ne_top hα (by linarith) hk hν hB v)
    (memRaySobolev_gaussSobolevRay hα (by linarith) hk)
    (rayProfile_gaussSobolevRay hk1 hα hk2) x
  exact stronglyMeasurable_gaussTarget v

end OperatorRidgelet.Paper
