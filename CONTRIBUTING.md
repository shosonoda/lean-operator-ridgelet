# Contributor guide

Start with [README.md](README.md) for the public overview and minimal build instructions,
[the formalization guide](docs/FORMALIZATION.md) for the source map, and
[STATUS.md](STATUS.md) for the generated verification record. The manuscript index is
[OperatorRidgelet/comparator/paper.json](OperatorRidgelet/comparator/paper.json).

Use `main` when resuming work on another machine; surviving work branches are historical
checkpoints. Run `git status --short` before editing and preserve unrelated changes.

Paths in the dependency and vendoring sections are relative to the repository root. In the
statement-update and annotation sections, paths such as `Challenge/`, `comparator/`, and
`OperatorRidgelet/Paper/` are relative to the mathematics project, `OperatorRidgelet/`.
Command blocks that start with `cd` assume the repository root as the starting directory.
Python scripts require Python 3.

## Dependencies and vendored code

- `OperatorRidgelet/` is the mathematics.  `OperatorRidgeletBlueprint/` is the human-facing Verso
  Blueprint and depends on `../OperatorRidgelet` by path.  Both use Lean 4.32.0 and Mathlib
  v4.32.0.  Keep `lean-toolchain` and the Mathlib revision identical in both.
- `lake-manifest.json` files are tracked; run `lake update <pkg>` only to change a pin on purpose.
- `OperatorRidgelet/LeanRidgelet/` is a verbatim subset of `shosonoda/lean-ridgelet`
  (revision in `LeanRidgelet.lean`).  Do not edit them; update by diffing against upstream.
- Never run two `lake build`s in the same project concurrently.
- `OperatorRidgeletBlueprint/vendor/VersoBlueprint/` vendors Verso Blueprint at revision
  `84fafd488acf60e47d3a7e2b029ee4502e740ba8`, with a local extension for a distinct Example
  node kind. Preserve the upstream license and copyright notices; the source and local
  changes are recorded in [PROVENANCE.md](OperatorRidgeletBlueprint/vendor/VersoBlueprint/PROVENANCE.md).
  Keep its `.lake/build` separate from any upstream checkout when compiling the extension.

## Updating manuscript statements

- Every theorem, proposition, lemma, corollary, and example of the manuscript is a theorem
  `OperatorRidgelet.Paper.<kind>_<number>[_<part>]`, with dots in the manuscript number
  replaced by underscores (for example, `thm_3_14_i_a` or `cor_D_2_i`). Multipart results
  retain their part suffixes; vector-valued theorem parts use descriptive `plancherel`,
  `representation`, and `frame` suffixes. Pure definitions retain their semantic names.
  In `paper.json`, `label` remains the source LaTeX label, while `blueprint_label` is the
  numbered Blueprint identifier (for example, `thm:3.14` for source label `thm:B`).
- The statement is written twice with identical text: in `Challenge/<Section>.lean` with proof
  `sorry`, and in `OperatorRidgelet/Paper/<Section>.lean` with the real proof (or `sorry` while
  outstanding).  `Challenge` imports only definition modules, never `OperatorRidgelet.Paper`.
- `comparator/config.json` `theorem_names` lists exactly the Paper theorems whose proofs are
  complete.  Adding a name and running `scripts/comparator-check.sh` is the definition of
  "verified".  A `sorry`-ed theorem is never in `theorem_names`.
- Definitions used in statements live in `*/Defs.lean` modules and are `sorry`-free.  Close heavy
  proof obligations inside definitions with junk values in the Mathlib style; state the
  properties as theorems.  `OperatorRidgelet/BasisIndependence.lean` is where the obligations of
  the chosen-basis definitions (`traceOf`, `fredholmDet`) are discharged; add new
  ones there, with the general mathematics in `ToMathlib`.
- Run `scripts/check-challenge.py` after editing either side, and regenerate `STATUS.md` with
  `scripts/status.py > ../STATUS.md`.

## Blueprint annotations

- LeanArchitect and Verso Blueprint both define an attribute named `blueprint`. All LeanArchitect
  annotations are `attribute [blueprint ...]` commands in `OperatorRidgelet/ArchitectBridge.lean`
  and its `ArchitectBridge/` modules;
  no other module imports `Architect`, and no blueprint chapter imports `ArchitectBridge`.
- Tag a statement whose proof is `sorry` with `(notReady := true)`; remove the flag when the proof
  is done.  `scripts/status.py` checks that the flag agrees with `theorem_names`.
- Blueprint node labels use manuscript numbers (`thm:3.14`, `lem:3.5`, ...), recorded
  separately from source LaTeX labels in each item's `blueprint_label` field.
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

## Comparator tools

Build [comparator](https://github.com/leanprover/comparator) and
[lean4export](https://github.com/leanprover/lean4export) at tag `v4.32.0`, following each
project's build instructions. The wrapper
[comparator-check.sh](OperatorRidgelet/scripts/comparator-check.sh) locates the tools as follows:

| Executable on `PATH` | Override with an executable path |
| --- | --- |
| `comparator` | `COMPARATOR_BIN` |
| `lean4export` | `COMPARATOR_LEAN4EXPORT` |
| `landrun` | `COMPARATOR_LANDRUN` |

For example, from the repository root, substitute the actual absolute paths:

```sh
cd OperatorRidgelet
export COMPARATOR_BIN=/absolute/path/to/comparator
export COMPARATOR_LEAN4EXPORT=/absolute/path/to/lean4export
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
lake build Challenge Solution
./scripts/comparator-check.sh
```

`landrun` provides sandboxing on Linux. On macOS or other systems, set `COMPARATOR_LANDRUN`
to the executable `scripts/fake-landrun.sh` in the comparator checkout; this runs without a
sandbox. The textual `check-challenge.py` check and the generated status table do not execute
comparator and do not replace proof verification.

## Validation and generated files

Run the following from the repository root, with comparator tools configured as above.
The two Lake projects share the mathematics project by path; run these builds sequentially.

```sh
cd OperatorRidgelet
lake build
lake build Challenge Solution
python3 scripts/check-challenge.py
python3 scripts/check-style.py
./scripts/comparator-check.sh
lake build OperatorRidgelet:blueprintJson
python3 scripts/status.py > ../STATUS.md
```

Then, starting again at the repository root:

```sh
python3 scripts/update-readme-badges.py
cd OperatorRidgeletBlueprint
lake exe cache get
lake exe vbp build
lake exe vbp check
```

A change is finished when the full build, challenge and style checks, comparator, and Blueprint
build and check all pass, and `STATUS.md` has been regenerated. The style check enforces the
100-character limit and declaration documentation in project-owned Lean modules; vendored
files retain their upstream formatting.

Do not edit generated files by hand:

| Generated output | Generator (from the repository root) |
| --- | --- |
| `STATUS.md` | `python3 OperatorRidgelet/scripts/status.py > STATUS.md` |
| README badge block | `python3 scripts/update-readme-badges.py` |

Commit regenerated outputs with their source changes. In particular, regenerate the badges
after changing the toolchain and the status table after changing `paper.json`, `config.json`,
or `Challenge/`.

## Blueprint

```sh
cd OperatorRidgeletBlueprint
lake exe cache get                                        # first time only: Mathlib cache
lake exe vbp build --serve --port 8001                    # then open http://127.0.0.1:8001/
lake exe vbp check
lake exe vbp query work-queue                             # statements whose proof is still `sorry`
```

The Blueprint follows manuscript Sections 1–9 and Appendices A–E, with supporting
infrastructure presented separately. Each mathematical node links its informal statement to
the corresponding Lean declarations. The formalization notes in `paper.json` record the
scope of those statements. Comparator independently checks the 341 propositions in
`Challenge` against their proved counterparts; [STATUS.md](STATUS.md) records the item mapping.

### Continuous integration and GitHub Pages

`.github/workflows/pages.yml` builds the blueprint on every push to `main` (and on demand) and
deploys it to GitHub Pages, with the blueprint's own `index.html` as the top page.  The job sets
up Lean with `leanprover/lean-action` in `OperatorRidgeletBlueprint/`, which fetches the Mathlib
cache, restores the previous run's build of the library, the blueprint, and the Verso packages
with `actions/cache` (keyed on the two `lean-toolchain` files, the two `lake-manifest.json`
files, and the commit, falling back to the latest run with the same toolchain and manifests), and
then runs

```sh
cd OperatorRidgeletBlueprint
./scripts/ci-pages.sh       # builds, checks, and assembles _site/
```

which can also be run locally.  The first run compiles everything that the Mathlib cache does not
cover; later runs rebuild only the modules whose inputs changed.

Before the first deployment, enable GitHub Pages in the repository settings (Settings, Pages)
with source "GitHub Actions"; no branch is needed.  The `deploy` job then publishes each build
to <https://shosonoda.github.io/lean-operator-ridgelet/>.

`.github/workflows/badges.yml` (`Generated files`) runs `python3 scripts/update-readme-badges.py
--check` on every push and pull request; it needs no Lean.
