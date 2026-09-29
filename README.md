# lean-operator-ridgelet

<!-- BEGIN GENERATED BADGES -->
[![Lean 4.32.0](https://img.shields.io/badge/Lean-4.32.0-0f4c81.svg?style=flat-square)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/blueprint-Verso-6f42c1.svg?style=flat-square)](https://shosonoda.github.io/lean-operator-ridgelet/)
[![Blueprint pages](https://img.shields.io/github/actions/workflow/status/shosonoda/lean-operator-ridgelet/pages.yml?branch=main&label=blueprint%20pages&style=flat-square)](https://github.com/shosonoda/lean-operator-ridgelet/actions/workflows/pages.yml)
[![License Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square)](LICENSE)
<!-- END GENERATED BADGES -->

Lean 4 formalization of the operator ridgelet transform on infinite-dimensional Hilbert spaces,
following the manuscript by Sho Sonoda and coauthors. It covers the Gaussian-weighted ridgelet
transform, Plancherel and reconstruction theorems, activations represented by tempered
distributions such as ReLU, and dimension-free finite-width approximation.

The repository tracks the **68 manuscript items of the 2026-09-29 terminology revision**:
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
| Reconstruction formulas and activation functions; integral representation under Sobolev conditions | [Tempered/](OperatorRidgelet/OperatorRidgelet/Tempered/), [Sobolev/](OperatorRidgelet/OperatorRidgelet/Sobolev/) |
| Finite-width approximation rates | [Sampling/](OperatorRidgelet/OperatorRidgelet/Sampling/) |
| Gaussian examples, operator layers, convolution and Dirichlet operators | [Examples/](OperatorRidgelet/OperatorRidgelet/Examples/) |
| Finite-dimensional formulas and explicit analysis filters | [FiniteDim/](OperatorRidgelet/OperatorRidgelet/FiniteDim/), [Filters/](OperatorRidgelet/OperatorRidgelet/Filters/) |

[The formalization guide](docs/FORMALIZATION.md) explains the manuscript-to-Lean correspondence,
where to find the precise statements and proofs, the notation conventions, and the scope of
verification. [STATUS.md](STATUS.md) lists individual items and Lean declaration names.

## Build

Install [elan](https://github.com/leanprover/elan), clone this repository, then run from its root:

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
./scripts/comparator-check.sh
```

The check compares the proved statements with the independent `Challenge` statements and
allows only `propext`, `Quot.sound`, and `Classical.choice`. On systems other than Linux, use
comparator's `scripts/fake-landrun.sh` through `COMPARATOR_LANDRUN` (without sandboxing).
See [the contributor guide](CONTRIBUTING.md#comparator-tools) for executable paths and setup details.

Development checks, Blueprint builds, and publishing instructions are in
[CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache License 2.0, see [LICENSE](LICENSE).  The files under `OperatorRidgelet/LeanRidgelet/`
are copied from [shosonoda/lean-ridgelet](https://github.com/shosonoda/lean-ridgelet), also
Apache 2.0. The files under `OperatorRidgelet/NeuralNetworkProofs/` are copied from
[Davor Runje's neural-network-proofs](https://github.com/davorrunje/neural-network-proofs),
commit `f90942517be8b66dd34574212ada69b2130a48e5`, also Apache 2.0. Their copyright headers
and license are preserved. `OperatorRidgelet/NeuralNetworkProofs.lean` records the subset and
the compatibility adaptation for Mathlib v4.32.0.
`OperatorRidgeletBlueprint/vendor/VersoBlueprint/` preserves Verso Blueprint's Apache-2.0
license and copyright notices; its pinned revision and Example-kind extension are documented
in [PROVENANCE.md](OperatorRidgeletBlueprint/vendor/VersoBlueprint/PROVENANCE.md).
