# Synchronizing with the 2026-09-13 Constructive Approximation revision

Manuscript: `-draft-operator-ridgelet`, branch `lean/operator-ridgelet`, commit `3e312d5`
("Revise manuscript for Constructive Approximation readers").  The previous synchronization point
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

| Item | Label | Source in `supp.tex` | Depends on |
|---|---|---|---|
| 5.6 | `thm:weak-sobolev-synthesis` | `supp:thm:weak-sobolev-synthesis` | C.3, C.4 |
| C.3 | `lem:sobolev-tools` | `supp:lem:sobolev-tools` | — |
| C.4 | `lem:sobolev-pairing` | `supp:lem:sobolev-pairing` | C.3 |
| D.2 | `lem:two-coordinate-comparison` | `supp:lem:supp-two-coordinate-comparison` | — |
| I.3 | `prop:nonbandpass-sobolev` | `supp:prop:nonbandpass-sobolev` | 5.6 |

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
