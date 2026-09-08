# lean-operator-ridgelet

Lean 4 formalization of the operator ridgelet transform on infinite-dimensional Hilbert spaces
(the Gaussian-weighted ridgelet transform, its Plancherel and reconstruction theory, tempered
synthesis activations such as ReLU, and dimension-free finite-width approximation), following the
manuscript by Sho Sonoda and coauthors.

The formalization status is recorded in [STATUS.md](STATUS.md), which is generated from the
[comparator](https://github.com/leanprover/comparator) configuration: every theorem, proposition,
lemma, corollary, and example of the manuscript is stated in `OperatorRidgelet/Challenge/` with
`sorry`, proved in `OperatorRidgelet/OperatorRidgelet/Paper/`, and listed in
`OperatorRidgelet/comparator/config.json` once comparator verifies the proof against the statement
with only the axioms `propext`, `Quot.sound`, and `Classical.choice`.

## Layout

```
OperatorRidgelet/            Lake project (Lean 4.32.0, Mathlib v4.32.0)
  OperatorRidgelet/          the library: definitions, lemmas, and the paper statements (Paper/)
  LeanRidgelet/              vendored subset of shosonoda/lean-ridgelet (activation spaces)
  Challenge.lean, Challenge/ comparator challenge: paper statements with `sorry`
  Solution.lean              comparator solution: imports OperatorRidgelet.Paper
  comparator/                config.json (verified theorems), paper.json (manuscript index)
  scripts/                   comparator-check.sh, status.py, check-challenge.py, sync-paper-numbers.py
OperatorRidgeletBlueprint/   Verso Blueprint (human-readable, depends on ../OperatorRidgelet)
attic/lean/                  retired Lean files, not built
```

Dependencies: [Mathlib](https://github.com/leanprover-community/mathlib4) v4.32.0,
[FoML](https://github.com/auto-res/lean-rademacher) (branch `v4.32.0`, Rademacher complexity),
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) v4.32.0 (dependency metadata), and
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) v4.32.0 (blueprint project only).

## Build

```sh
cd OperatorRidgelet
lake exe cache get          # first time only: Mathlib cache
lake build                  # library; the only warnings are the intentional `sorry`s
lake build Challenge Solution
lake build OperatorRidgelet:blueprintJson   # LeanArchitect metadata (library name required)
```

## Verify the paper statements with comparator

Build [comparator](https://github.com/leanprover/comparator) and
[lean4export](https://github.com/leanprover/lean4export) at tag `v4.32.0` and put the
`comparator`, `lean4export`, and `landrun` executables on `PATH` (or point the environment
variables `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_LANDRUN` at them), then

```sh
scripts/comparator-check.sh
scripts/check-challenge.py           # fast textual check that Challenge and Paper agree
scripts/status.py > ../STATUS.md     # regenerate the status table
```

comparator sandboxes the builds with `landrun`, which needs Linux; comparator ships a
`scripts/fake-landrun.sh` shim for development on other systems (no sandbox).

## Blueprint

```sh
cd OperatorRidgeletBlueprint
lake exe cache get                                        # first time only: Mathlib cache
lake exe vbp build --serve --port 8001                    # then open http://127.0.0.1:8001/
lake exe vbp check
lake exe vbp query work-queue                             # statements whose proof is still `sorry`
```

## License

Apache License 2.0, see [LICENSE](LICENSE).  The files under `OperatorRidgelet/LeanRidgelet/`
are copied from [shosonoda/lean-ridgelet](https://github.com/shosonoda/lean-ridgelet), also
Apache 2.0.
