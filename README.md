# lean-operator-ridgelet

Lean 4 formalization of the operator ridgelet transform on infinite-dimensional Hilbert spaces,
following the manuscript by Sho Sonoda and coauthors. It covers the Gaussian-weighted ridgelet
transform, Plancherel and reconstruction theorems, tempered synthesis activations such as ReLU,
and dimension-free finite-width approximation.

This source snapshot (`snapshot20260929`) contains the Lean sources, pinned dependency
configuration, and comparator inputs. Build caches and development tooling are omitted.

The snapshot tracks the **68 manuscript items of the 2026-09-29 numbered manuscript**:
all are recorded as
verified, comprising **369 Lean statements checked by comparator** and the pure definitions.
The manuscript itself is not included. See the [Verso Blueprint](https://shosonoda.github.io/lean-operator-ridgelet/)
for a presentation organized by manuscript Sections 1–8 and Appendices A–J, followed by
supporting infrastructure, and [STATUS.md](STATUS.md) for the generated per-item record.

## What is formalized, and where?

The mathematics is in [OperatorRidgelet/OperatorRidgelet/](OperatorRidgelet/OperatorRidgelet/).

| Topic | Main modules |
| --- | --- |
| Scalar and operator networks, rank-one lifts, universality | [Network/](OperatorRidgelet/OperatorRidgelet/Network/), [Architecture/](OperatorRidgelet/OperatorRidgelet/Architecture/) |
| Gaussian-weighted transform, Fourier-slice identity, Plancherel | [Transform/](OperatorRidgelet/OperatorRidgelet/Transform/) |
| Integral representation, reconstruction, frame operator, vector-valued extensions | [Reconstruction/](OperatorRidgelet/OperatorRidgelet/Reconstruction/) |
| Tempered activations and ReLU; absolute synthesis under a Sobolev condition | [Tempered/](OperatorRidgelet/OperatorRidgelet/Tempered/), [Sobolev/](OperatorRidgelet/OperatorRidgelet/Sobolev/) |
| Finite-width approximation and sampling bounds | [Sampling/](OperatorRidgelet/OperatorRidgelet/Sampling/) |
| Gaussian examples, operator layers, convolution and Dirichlet operators | [Examples/](OperatorRidgelet/OperatorRidgelet/Examples/) |
| Finite-dimensional formulas and explicit analysis filters | [FiniteDim/](OperatorRidgelet/OperatorRidgelet/FiniteDim/), [Filters/](OperatorRidgelet/OperatorRidgelet/Filters/) |

[STATUS.md](STATUS.md) lists individual items, Lean declaration names, and notation conventions.
[comparator/paper.json](OperatorRidgelet/comparator/paper.json) records the manuscript-to-Lean
correspondence and formalization notes. The precise statements are in
[Challenge/](OperatorRidgelet/Challenge/) and their proofs in
[Paper/](OperatorRidgelet/OperatorRidgelet/Paper/).

Manuscript-facing declarations use `OperatorRidgelet.Paper.<kind>_<number>[_<part>]`,
with dots replaced by underscores, for example `thm_3_11_i`. Semantic definition names
remain unchanged. In `paper.json`, `label` retains the source label and `blueprint_label`
records the numbered Blueprint identifier. Comparator checks the 369 independent
statements; there is no separate human-facing Comparator review chapter.

`STATUS.md` preserves the verification record generated before packaging. References there to
`scripts/status.py` and `scripts/comparator-check.sh` describe the development repository;
the scripts are omitted here. Use the direct comparator command below to reproduce the check.

## Build

Install [elan](https://github.com/leanprover/elan), extract the archive, then run from its root
(with network access to fetch the pinned dependencies and Mathlib cache):

```sh
cd OperatorRidgelet
lake exe cache get
lake build
```

The project pins Lean 4.32.0 and Mathlib v4.32.0; elan selects the Lean toolchain automatically.
The library has no admitted proofs. The separate comparator `Challenge` target intentionally
uses `sorry` to state the propositions to be checked.

## Reproduce the comparator check

Build [comparator](https://github.com/leanprover/comparator) and
[lean4export](https://github.com/leanprover/lean4export) at tag `v4.32.0`. Put `comparator`,
`lean4export`, and `landrun` on `PATH`, then run from the repository root:

```sh
cd OperatorRidgelet
lake build Challenge Solution
export COMPARATOR_LEAN4EXPORT="$(command -v lean4export)"
export COMPARATOR_LANDRUN="$(command -v landrun)"
lake env comparator comparator/config.json
```

The check compares the proved statements with the independent `Challenge` statements and
allows only `propext`, `Quot.sound`, and `Classical.choice`. On systems other than Linux, use
comparator's `scripts/fake-landrun.sh` through `COMPARATOR_LANDRUN` (without sandboxing).
Set `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN` to absolute executable paths if the tools
are not on `PATH`. On macOS, replace the `COMPARATOR_LANDRUN` export above with the absolute
path to `scripts/fake-landrun.sh` in the comparator checkout. The snapshot contains all
369 configured statements in [comparator/config.json](OperatorRidgelet/comparator/config.json).

## License

Apache License 2.0, see [LICENSE](LICENSE).  The files under `OperatorRidgelet/LeanRidgelet/`
are copied from [shosonoda/lean-ridgelet](https://github.com/shosonoda/lean-ridgelet), also
Apache 2.0. The files under `OperatorRidgelet/NeuralNetworkProofs/` are copied from
[Davor Runje's neural-network-proofs](https://github.com/davorrunje/neural-network-proofs),
commit `f90942517be8b66dd34574212ada69b2130a48e5`, also Apache 2.0. Their copyright headers
and license are preserved. `OperatorRidgelet/NeuralNetworkProofs.lean` records the subset and
the compatibility adaptation for Mathlib v4.32.0.
