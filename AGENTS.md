# Agent guide for lean-operator-ridgelet

This repository is the development repository of the Lean formalization of the operator ridgelet
manuscript.  The manuscript itself is not part of this repository; `comparator/paper.json` carries
the index of its statements.

## Read first

1. `README.md` for the layout and the build, comparator, and blueprint commands.
2. `STATUS.md` for what is stated and what is verified.  It is generated; never edit it by hand.
3. `OperatorRidgelet/comparator/paper.json` for the manuscript index (labels, numbers, Lean names).
4. `git status --short`; preserve unrelated edits.

## Two Lake projects, one toolchain

- `OperatorRidgelet/` is the mathematics.  `OperatorRidgeletBlueprint/` is the human-facing Verso
  Blueprint and depends on `../OperatorRidgelet` by path.  Both use Lean 4.32.0 and Mathlib
  v4.32.0.  Keep `lean-toolchain` and the Mathlib revision identical in both.
- `lake-manifest.json` files are tracked; run `lake update <pkg>` only to change a pin on purpose.
- `OperatorRidgelet/LeanRidgelet/` is a verbatim copy of eight files of `shosonoda/lean-ridgelet`
  (revision in `LeanRidgelet.lean`).  Do not edit them; update by diffing against upstream.
- Never run two `lake build`s in the same project concurrently.
- `OperatorRidgelet/NeuralNetworkProofs/` vendors the Leshno theorem from
  `davorrunje/neural-network-proofs`; its pinned revision, license, and compatibility adaptation
  are recorded in `NeuralNetworkProofs.lean`. Preserve the upstream copyright headers and
  document any further adaptations. Keep the operator-specific bridge in `Architecture/`.

## The comparator scheme is the record of formalization

- Every theorem, proposition, lemma, corollary, and example of the manuscript is a theorem
  `OperatorRidgelet.Paper.<kind>_<label>[_<part>]` (`<label>` is the LaTeX label without its
  prefix, `-` replaced by `_`; multi-part results are split per part, e.g. `thm_B_i`).
- The statement is written twice with identical text: in `Challenge/<Section>.lean` with proof
  `sorry`, and in `OperatorRidgelet/Paper/<Section>.lean` with the real proof (or `sorry` while
  outstanding).  `Challenge` imports only definition modules, never `OperatorRidgelet.Paper`.
- `comparator/config.json` `theorem_names` lists exactly the Paper theorems whose proofs are
  complete.  Adding a name and running `scripts/comparator-check.sh` is the definition of
  "verified".  A `sorry`-ed theorem is never in `theorem_names`.
- Definitions used in statements live in `*/Defs.lean` modules and are `sorry`-free.  Close heavy
  proof obligations inside definitions with junk values in the Mathlib style; state the
  properties as theorems.
- Run `scripts/check-challenge.py` after editing either side, and regenerate `STATUS.md` with
  `scripts/status.py > ../STATUS.md`.

## LeanArchitect and Verso Blueprint

- LeanArchitect and Verso Blueprint both define an attribute named `blueprint`. All LeanArchitect
  annotations are `attribute [blueprint ...]` commands in `OperatorRidgelet/ArchitectBridge.lean`
  and its `ArchitectBridge/` modules;
  no other module imports `Architect`, and no blueprint chapter imports `ArchitectBridge`.
- Tag a statement whose proof is `sorry` with `(notReady := true)`; remove the flag when the proof
  is done.  `scripts/status.py` checks that the flag agrees with `theorem_names`.
- Blueprint node labels are the manuscript labels (`thm:B-i`, `lem:fourier-slice`, ...).
- Build LeanArchitect metadata with `lake build OperatorRidgelet:blueprintJson` (library name
  required), and the blueprint with `lake exe vbp build && lake exe vbp check` in
  `OperatorRidgeletBlueprint/`.

## Where general mathematics goes

- Before writing a general-purpose result (Fourier analysis, functional analysis, measure
  theory, anything that makes sense without neural networks or ridgelet transforms), search
  Mathlib first, then the vendored files under `OperatorRidgelet/LeanRidgelet/`, then the
  `LeanRidgelet/ToMathlib/` directory of <https://github.com/shosonoda/lean-ridgelet>, which
  holds the general tools that earlier ridgelet formalizations needed (weighted Sobolev spaces,
  Fourier conventions and Plancherel, Gaussian Schwartz functions, Bochner integrals in `L²`,
  Hilbert–Schmidt kernels, Lipschitz discretization, ...).
- If the result exists in `lean-ridgelet`'s `ToMathlib`, vendor that file verbatim into
  `OperatorRidgelet/LeanRidgelet/ToMathlib/` with the same provenance header as the other vendored
  files (upstream path and revision), add it to `LeanRidgelet.lean`, and do not edit it.
- If it exists in neither, implement it in `OperatorRidgelet/OperatorRidgelet/ToMathlib/`
  (module `OperatorRidgelet.ToMathlib.*`): Mathlib-only imports, Mathlib generality and naming, no
  reference to ridgelet-specific definitions, a docstring on every declaration.  These files are
  staged to be merged into `lean-ridgelet`'s `ToMathlib` later, so keep them self-contained.
- Ridgelet-specific auxiliary lemmas stay in the `*/Basic.lean` modules next to their definitions.

## Conventions

- Namespace `OperatorRidgelet`; Mathlib naming (`lowerCamelCase` definitions, `snake_case`
  theorems); Fourier convention `f̂(ξ) = ∫ f(x) e^{-i⟨x,ξ⟩} dx` as in the manuscript.
- `H` is a real Hilbert space (`[NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]`); `μ` the input probability
  measure, `ν` the σ-finite homogeneous direction measure.  State the core theory for abstract
  `(μ, ν)` and specialize to the Gaussian case.
- Every new statement is added to `paper.json` (`lean` list), `Challenge`, `Paper`, and
  `ArchitectBridge.lean` in the same change.
- Commit messages describe the manuscript items touched (e.g. `Prove lem:fourier-slice`).

## Resuming on another machine

1. Clone this repository, install [elan](https://github.com/leanprover/elan), then in
   `OperatorRidgelet/` run `lake exe cache get` followed by `lake build`. The library has no
   admitted proofs. The separate `Challenge` target intentionally uses `sorry` for its statements.
2. `STATUS.md` says which manuscript items are verified. Regenerate it with
   `python3 scripts/status.py > ../STATUS.md` from `OperatorRidgelet/`.
3. To re-verify the proofs, build [comparator](https://github.com/leanprover/comparator) and
   [lean4export](https://github.com/leanprover/lean4export) at tag `v4.32.0` and run
   `scripts/comparator-check.sh` (see the README for how the executables are located). On Linux it
   sandboxes with `landrun`; elsewhere use comparator's `fake-landrun.sh` shim.
4. The 63 items of the previous manuscript revision, comprising 345 statements, are verified on
   `main`. The branch `lean/ca-revision-20260913` tracks the 2026-09-13 Constructive
   Approximation revision: 5 new items are not formalized, 3 verified items were restated, and
   the manuscript flipped the bias sign (`sigma(<a,x> - b)`, `b = -c`) while the Lean
   definitions keep `<a,x> + c`. `STATUS.md` and `comparator/paper.json` carry the details.
   Earlier work
   branches are historical checkpoints; resume from `main`, not their WIP tips.
5. The deferred line-length and docstring pass is complete. After `lake build`, run
   `python3 scripts/check-style.py` to check the 100-character limit and declaration documentation
   in project-owned modules. Vendored files keep their upstream formatting.
6. The 2026-09-12 revision includes the unitary partial Fourier transform, coefficient
   adjoint and stability, finite-order ray estimates with output-independent constants,
   exact sampling variance, and qualitative vector sampling under a first moment.
   Full build, Comparator, LeanArchitect, Blueprint build/check, and style checks pass.
