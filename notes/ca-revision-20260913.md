# Synchronizing with the 2026-09-13 Constructive Approximation revision

Manuscript: `-draft-operator-ridgelet`, branch `main`, commit `3e312d5`
("Revise manuscript for Constructive Approximation readers"; the former working branch
`lean/operator-ridgelet` was merged into `main` on 2026-09-13, and the manuscript develops on
`main` from now on).  The previous synchronization point
was `fb56ba6` (recorded in `paper.json` as the "2026-09-12 revision").  The revision plan is
`00note/plan20260913-ca-ja.md` of the manuscript repository; its Section 6 is the symbol table.

This note records what the revision changes for the formalization.  `comparator/paper.json` and
`STATUS.md` carry the same information per item; this is the overview and the work list.

## What was done in this commit

`scripts/sync-paper-numbers.py` was run against the new `main.tex` and `main.aux`.  All 63 labels
of the previous revision survive, so every `lean` list was preserved by label; the numbering and the
placement changed considerably (several main-text lemmas moved to the appendices, for instance
`lem:coefficient-isometry` 3.7 to B.1, `lem:partial-fourier-l2` 3.5 to A.1, `lem:ray-regular-examples`
6.6 to D.3).  Five new items were added.  `paper.json` items now carry an optional `revision` field
(`new` or `restated`), which `scripts/status.py` and the blueprint chapter generator render in the
status column, and `paper.json` `manuscript.conventions` records the renaming and the bias sign.

No Lean file was touched.  Nothing that was verified became unverified: comparator checks the
`Challenge` statement against the `Paper` proof, and both are unchanged.  What changed is the
correspondence between the Lean statements and the manuscript, which is what the new fields record.

## Global: the bias sign

The manuscript now writes a neuron as `sigma(<a,x> - b)`; the previous revision and the Lean
definitions (`ridgelet`, `integralNetwork`, `integralNetworkDensity`, `spectralCoefficient`, ...)
write `<a,x> + c`.  The two coordinates are related by the involution `tau(a,c) = (a,-c)`, which
preserves `lambda_alpha = nu_alpha (x) dc` because the bias carries Lebesgue measure.  Consequently

- no Lean statement becomes false, and no proof needs repair;
- but the manuscript-to-Lean reading of every bias-dependent statement goes through `tau`, and the
  reader of the blueprint should not have to perform that substitution silently.

Two ways to close this, to be decided before the next comparator run:

1. keep the Lean convention and add, next to `def:integral-network`, a pair of definitions in the
   manuscript convention together with the transport lemmas `S_sigma[tau_# Gamma] = ...` and
   `R_rho^{new} f (a,b) = R_rho f (a,-b)`, and cite them from the affected blueprint nodes;
2. flip the Lean convention in the definition modules and repair the proofs.

Option 1 is what the manuscript plan suggests (Section 10: wrappers rather than a global rename),
and it is much the smaller change; option 2 touches every proof that unfolds a bias integral.

The other renamings of the plan's Section 6 (`H` to `\mathcal H`, `\mathcal G_Q` to `F_Q`, scalar
activation `beta` to `sigma`, operator activation `sigma` to `Sigma`, spectral density `G` to `g`,
target `g_G` to `f_g`, coefficient `gamma_G` to `gamma_g`, `\mathcal N(0,Q)` to `mu_Q`, Gaussian
activation `Phi` to `sigma_Gauss`, operator layer `\mathcal F` to `F`, Dirichlet Green operator
`\mathsf G` to `L_D^{-1}`, the Gaussian-parameter ReLU target `F_Q` to `f_{ReLU,Q}`) have no effect
on the Lean statements.  Lean names follow Mathlib conventions and are not renamed to track them.

## New items (5): formalization outstanding

They come from the manuscript's `supp.tex`, whose results were proved by hand but never formalized.

| Item | Label | Source in `supp.tex` | Depends on | Status |
|---|---|---|---|---|
| 5.6 | `thm:weak-sobolev-synthesis` | `supp:thm:weak-sobolev-synthesis` | C.3, C.4 | **done** |
| C.3 | `lem:sobolev-tools` | `supp:lem:sobolev-tools` | — | **done** |
| C.4 | `lem:sobolev-pairing` | `supp:lem:sobolev-pairing` | C.3 | **done** |
| D.2 | `lem:two-coordinate-comparison` | `supp:lem:supp-two-coordinate-comparison` | — | **done** |
| I.3 | `prop:nonbandpass-sobolev` | `supp:prop:nonbandpass-sobolev` | 5.6 | outstanding |

`prop:nonbandpass-sobolev` (I.3) is what remains.  It needs the Schwartz filter with
`ρ̂(ω) = ω^{2k}e^{-ω²}` (the vendored Hermite–Gaussian tools should supply it), the membership
`q_{α,ρ} ∈ H^s_ω` for `2k > α + 2s - 1/2` — that is, a weighted `L²` bound on the inverse
transform of `|ω|^{δ}e^{-ω²}`, which the manuscript obtains from `H^m ⊆ H^s` and integration by
parts on the two half-lines — the Gaussian ray hypotheses, and the two Gamma-function
reconstruction constants.

`thm:weak-sobolev-synthesis` gives absolute synthesis for filters that need not be band pass: with
Sobolev regularity of order `s` along rays it needs `s > p + 1/2` for an activation of growth `p`
and yields moments of every order `r < s - 1/2`, so `s > 5/2` for the second moment that
`thm:lipschitz-barron` consumes.  `lem:two-coordinate-comparison` is the combinatorial step of the
Hilbert-valued uniform bound below and is independent of the Sobolev line; it can be formalized
first.

## Restated items (3): verified, but against the earlier statement

| Item | Label | What changed |
|---|---|---|
| 6.3 | `thm:lipschitz-barron` | Now stated for `Y`-valued coefficient measures in `C(K;Y)` with the sharper constant `V(4|sigma(0)| + 8 Lip(sigma) R_K M_2)/sqrt N`; the earlier scalar `8V(...)/sqrt N` is kept as a consequence.  Conventions for `V = 0` and empty `K` are now stated.  This is `supp:vector-uniform` of `supp.tex`. |
| 6.5 | `thm:D` | The vector-valued clause now claims the same explicit width-`N` bound through 6.3, where it previously referred to the weaker vector-valued rate.  `thm_D` and `thm_D_dense` are unaffected; `thm_D_vec` predates the change. |
| 7.4 | `ex:operator-layer` | Clause (i) now gives the uniform bound `E||F_N - F||_{C(K;Y)} <= B_1(4|sigma(0)| + 8 Lip(sigma) R_K ||A||_infty)/sqrt N` for the whole output function, in place of the earlier per-observable scalar bound and the `L^2(zeta;Y)` rate.  The output kernel is renamed `b_y` to `v_y`. |

`ex:convolution` (7.5) went the other way: the revision added the hypothesis `sigma = sigma_Gauss`
to the non-cylindricity clause, which is the hypothesis `ex_convolution_x` already carries
(`gaussianFun`).  The manuscript was corrected to the formalized statement, so the item is in sync.

`ex:dirichlet` (7.6) has prose corrections only (the layer is the nonlinear correction in a Picard
update; with `Q = P = L_D^{-1}` the input measure is the Gaussian field with covariance `L_D^{-1}`,
not `L_D^{-2}`; the claim that no rate is available for the nonlinear layer is replaced by a pointer
to the uniform estimate of 7.4).  Its formalized content is unchanged, so it carries a note but no
`revision` flag.

## Progress (2026-09-13)

Steps 1 and 2 of the work list below are done and verified by comparator.

* `lem:two-coordinate-comparison` (D.2) is `OperatorRidgelet/ToFoML/TwoCoordinate.lean`: the
  one-sign comparison `iSup_add_sign_le` with an arbitrary bounded offset, and the comparison
  itself by replacing one coordinate at a time along the Boolean sign vectors
  (`pow_two_mul_sum_iSup_boolSignVector_le`, normalized as `avg_iSup_boolSignVector_le`).  The
  Lean statement holds for an arbitrary nonempty index type; the manuscript's countability is
  kept in the `Paper` statement only for fidelity.
* `thm:lipschitz-barron` (6.3) is now the Hilbert-valued statement in three parts: the
  expectation bound with the sharp constant `V(4|β(0)| + 8 Lip(β) R_K M₂)/√N` (`_i`), the
  deterministic realization (`_ii`), and the weaker second inequality `8V(…)/√N` (`_iii`).  The
  conditional Rademacher average of the `Y`-valued ridge atoms is
  `OperatorRidgelet/Sampling/VectorBarron.lean`, which writes the output norm as a supremum over
  the unit ball of `Y` and applies D.2.  The scalar bound that `cor:sampling-concentration`,
  `cor:two-stage-error` and `ex:operator-layer`(i-e) consume moved to the library as
  `integral_compactSupNorm_polarSampledNetwork_sub_le`, so no other manuscript statement changed.
* `thm:D` (6.5): the vector clause `thm_D_vec` now carries the same explicit width-`N` bound and
  a deterministic realization, through the `Y`-valued Barron bound for a coefficient measure with
  a density (`integral_compactSupNorm_densitySampledNetwork_sub_leVec`).
* `ex:operator-layer` (7.4): the new clause `ex_operator_layer_i_f` is the uniform bound
  `E‖F_N − F‖_{C(K;Y)} ≤ B₁(4|β(0)| + 8 Lip(β) R_K ‖A‖_∞)/√N` of `eq:operator-layer-uniform` for
  the whole output function; `i_e` stays the scalar observable.
* Two general-purpose lemmas were added to `OperatorRidgelet/ToMathlib/`: `RealInnerDual.lean`
  (the norm as a real inner product against the unit ball) and `SqrtSumSq.lean` (the `ℓ²`
  triangle inequality).

The Sobolev line is then done except for `prop:nonbandpass-sobolev` (I.3).

### The Sobolev line

`OperatorRidgelet/Sobolev/` holds the coefficient-side foundation of Appendix C, with no
manuscript item claimed yet.

* `Defs.lean`: the bracket `⟨t⟩`, the class `MemRaySobolev s γ` (`γ` square integrable against
  `⟨t⟩^{2s}`), the norm `raySobolevNorm s γ = (2π ∫ ⟨t⟩^{2s} ‖γ‖²)^{1/2}` of the profile whose
  inverse Fourier transform is `γ`, the profile `rayProfile γ = γ̂` in the angular convention,
  and the constants `A_{s,r}` and `b_{σ,s}`.  For `s > 1/2` the coefficient is integrable, so
  the profile is an ordinary Fourier integral and no `L²` extension of the transform is needed.
* `Basic.lean`: all four clauses of `lem:sobolev-tools` (C.3) — the weighted inverse Fourier
  estimate, the reflection isometry, the modulation bound, and the joint continuity of
  `(u, h) ↦ M_u h`, which is reduced to the strong continuity of translation in `L²`
  (`ToMathlib/L2Translation.lean`, from Mathlib's continuous `ℝᵈᵃᵃ` action on `Lp`) and a
  dominated convergence step for the multiplier `(⟨t⟩/⟨t+u⟩)^s`.
* `Pairing.lean`: `lem:sobolev-pairing` (C.4) — finiteness of `b_{σ,s}`, absolute convergence
  with the bound `(2π)^{-1/2} b_{σ,s} ‖h‖`, and the bias translation formula.
* `Uniqueness.lean`: `L¹` uniqueness of the profile (the multiplication formula, the fact that
  every real test function is a profile, and Mathlib's
  `ae_eq_of_integral_contDiff_smul_eq`).  This replaces the manuscript's `H^s`-valued Bochner
  integral: the direction average `Ψ(t) = ∫ γ(a, ⟪a,x⟫ - t) dν` is identified with
  `q̌_{α,ρ}(-t) f_g(x)` by comparing profiles, not by constructing `Φ_x` in `H^s`.
* `Synthesis.lean`: `thm:weak-sobolev-synthesis` (5.6) — the moment bound, the finite variation,
  the synthesis identity, the uniform majorant on balls, and the continuity of the synthesis.
  The identity is proved by the bias translation formula, two Fubini steps, the profile of `Ψ`
  through homogeneity, and `L¹` uniqueness.  The `L²(ν ⊗ db)` clause of the manuscript's
  conclusion (with value `C^{(α)}_ρ ‖g‖²`) is not part of the Lean statement; `paper.json`
  records this.

**The bias convention.**  The existing items keep the Lean convention `⟨a,x⟩ + c`, as the plan's
Section 10 suggests; `paper.json` `manuscript.conventions` records the transport `τ(a,c) =
(a,-c)`.  Theorem 5.6 is the exception: its coefficient is defined by its own Fourier relation,
so it is stated in the manuscript's convention `σ(⟪a,x⟫ - b)`, and
`integral_synthesis_eq_integralNetworkDensity` is the wrapper that rewrites it as the library's
`integralNetworkDensity` of the transported coefficient `γ ∘ τ`.

## Suggested order of work

1. `lem:two-coordinate-comparison` (D.2), then the Hilbert-valued `thm:lipschitz-barron` (6.3), with
   the old scalar bound rederived from it.  This unblocks 6.5 and 7.4, which are corollaries of 6.3
   in the manuscript.
2. `thm:D` (6.5) vector clause and `ex:operator-layer` (7.4) uniform clause.
3. The Sobolev line: `lem:sobolev-tools` (C.3), `lem:sobolev-pairing` (C.4),
   `thm:weak-sobolev-synthesis` (5.6), `prop:nonbandpass-sobolev` (I.3).
4. The bias convention, by whichever of the two options above is chosen.

Each step adds its statements to `Challenge`, `Paper`, `paper.json`, and `ArchitectBridge.lean` in
the same change, and clears the `revision` field of the item once the Lean statement is the
manuscript statement again.  Run `scripts/check-challenge.py`, then `scripts/comparator-check.sh`
once per package of work rather than per statement, and regenerate `STATUS.md` and the blueprint
chapter.
