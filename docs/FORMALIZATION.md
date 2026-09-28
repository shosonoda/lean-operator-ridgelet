# Guide to the formalization

This guide maps the operator ridgelet manuscript to the Lean sources. For an item-by-item list
of labels, numbers, declaration names, and verification status, see [STATUS.md](../STATUS.md).
The [Verso Blueprint](https://shosonoda.github.io/lean-operator-ridgelet/) presents the informal
mathematics alongside Lean declarations and their dependencies.

## Reading a manuscript item in Lean

The manuscript itself is not included. Its index,
[paper.json](../OperatorRidgelet/comparator/paper.json), records the 2026-09-13 revision and
includes a `note` for each item describing how it is formalized. These notes explain such
choices as explicit hypotheses, representations of operators, and the scope of each statement.

For example, Theorem 3.11 (`thm:B`, Plancherel identity and injectivity) corresponds to the
`OperatorRidgelet.Paper.thm_B_*` declarations in
[Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean). Its independent
statements are in [Challenge/Transform.lean](../OperatorRidgelet/Challenge/Transform.lean),
its definitions in [Transform/Defs.lean](../OperatorRidgelet/OperatorRidgelet/Transform/Defs.lean),
and its supporting proofs in the other `Transform/` modules.

In general, manuscript results have names
`OperatorRidgelet.Paper.<kind>_<label>[_<part>]`: the label loses its prefix and hyphens become
underscores. Multipart results may be split into several Lean declarations. Pure definitions
usually live directly in the `OperatorRidgelet` namespace.

The blueprint chapter **Comparator review of the Challenge statements** brings together each
item's informal statement link, formalization note, exact `Challenge` declaration text, and
recorded comparator status. It is a useful starting point for reviewing whether the formal
statements express the intended mathematics.

## Mathematical source map

All paths in this table are relative to
[OperatorRidgelet/OperatorRidgelet/](../OperatorRidgelet/OperatorRidgelet/). `Paper/` collects the
manuscript-facing theorems; the other modules supply definitions and supporting proofs.

| Subject and manuscript items | Definitions and supporting mathematics | Manuscript-facing proofs |
| --- | --- | --- |
| Networks (§2), Hilbert–Schmidt reduction, exact lifts and universality (Appendix F) | [Network/](../OperatorRidgelet/OperatorRidgelet/Network/), [Architecture/](../OperatorRidgelet/OperatorRidgelet/Architecture/), [RankOneLift.lean](../OperatorRidgelet/OperatorRidgelet/RankOneLift.lean), [OperatorValuedRidgelet.lean](../OperatorRidgelet/OperatorRidgelet/OperatorValuedRidgelet.lean) | [Paper/Networks.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Networks.lean) |
| Homogeneous Gaussian mixtures, Fourier-slice identity, spectral space and Plancherel (§3, Theorem B) | [Transform/](../OperatorRidgelet/OperatorRidgelet/Transform/) | [Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean), [Paper/Revision.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Revision.lean) |
| Integral representation, reconstruction, frame operator and vector-valued extensions (§4, Theorems A and C; Appendix B) | [Reconstruction/](../OperatorRidgelet/OperatorRidgelet/Reconstruction/) | [Paper/Reconstruction.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Reconstruction.lean), [Paper/Revision.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Revision.lean) |
| Tempered synthesis, ReLU and standard activations (§5, Appendix C) | [Tempered/](../OperatorRidgelet/OperatorRidgelet/Tempered/), [Activation.lean](../OperatorRidgelet/OperatorRidgelet/Activation.lean) | [Paper/Tempered.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Tempered.lean) |
| Weak Sobolev synthesis, Sobolev pairing and non-band-pass Gaussian-derivative filters (§5.6, C.3–C.4, I.3) | [Sobolev/](../OperatorRidgelet/OperatorRidgelet/Sobolev/) | [Paper/Sobolev.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Sobolev.lean) |
| Rademacher bounds, dimension-free finite-width approximation, sampling and input truncation (§6, Theorems D and E; Appendix D) | [Sampling/](../OperatorRidgelet/OperatorRidgelet/Sampling/), [ToFoML/](../OperatorRidgelet/OperatorRidgelet/ToFoML/) | [Paper/Sampling.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Sampling.lean), [Paper/SamplingRevision.lean](../OperatorRidgelet/OperatorRidgelet/Paper/SamplingRevision.lean), [Paper/Revision.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Revision.lean) |
| Gaussian targets, operator layers, convolution, Dirichlet operators and Gaussian integral identities (§7, Appendix E) | [Examples/](../OperatorRidgelet/OperatorRidgelet/Examples/) | [Paper/Examples.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Examples.lean) |
| Finite-dimensional backprojection and dilation obstruction (Appendix G) | [FiniteDim/](../OperatorRidgelet/OperatorRidgelet/FiniteDim/), [Transform/](../OperatorRidgelet/OperatorRidgelet/Transform/) | [Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean) |
| Abstract-weight extension (Appendix H) | [Transform/](../OperatorRidgelet/OperatorRidgelet/Transform/), [Reconstruction/](../OperatorRidgelet/OperatorRidgelet/Reconstruction/) | [Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean), [Paper/Revision.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Revision.lean) |
| Band-pass and Mexican-hat filters (I.1–I.2) | [Filters/](../OperatorRidgelet/OperatorRidgelet/Filters/) | [Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean) |

`Revision.lean` and `SamplingRevision.lean` contain additional statements from manuscript
revisions; consult them together with the main topic files. The `lean` lists in `paper.json`
and the table in `STATUS.md` give the exact declaration names for each item.

General-purpose results on Fourier analysis, Gaussian measures, operators, and integration live
in [ToMathlib/](../OperatorRidgelet/OperatorRidgelet/ToMathlib/), with Mathlib-only imports.
[BasisIndependence.lean](../OperatorRidgelet/OperatorRidgelet/BasisIndependence.lean) discharges
the basis-independence obligations for the trace, Fredholm determinant, and Hilbert–Schmidt norm.

## Conventions and verification scope

The input space `H` is a real, complete, second-countable Hilbert space with its Borel measurable
structure. The theory uses an input probability measure `μ` and a σ-finite homogeneous direction
measure `ν`, with both abstract-weight results and Gaussian specializations. The Fourier
convention is `f̂(ξ) = ∫ f(x) exp(-i⟨x,ξ⟩) dx`.

The manuscript writes neurons as `sigma(⟨a,x⟩ - b)`, whereas the Lean definitions use
`⟨a,x⟩ + c`; the correspondence is `b = -c`. Bias-dependent statements must be read through
this change of coordinates. The manuscript also renames several symbols without changing the
mathematics; the complete list is in the conventions paragraph of [STATUS.md](../STATUS.md)
and the `manuscript.conventions` field of `paper.json`.

The verification record has three components:

- [Challenge/](../OperatorRidgelet/Challenge/) states the propositions with intentional `sorry`
  proofs and imports only definition modules, never `OperatorRidgelet.Paper`.
- [Paper/](../OperatorRidgelet/OperatorRidgelet/Paper/) supplies the same statements with their
  proofs; [Solution.lean](../OperatorRidgelet/Solution.lean) imports these for comparator.
- [config.json](../OperatorRidgelet/comparator/config.json) lists the completed theorems.
  Comparator checks them against `Challenge`, allowing only `propext`, `Quot.sound`, and
  `Classical.choice`, with no admitted proofs.

All 68 indexed items are recorded as verified: 369 comparator statements plus the pure
definitions. This is verification of the indexed Lean formulations. Reviewing their agreement
with the manuscript also requires reading the formalization notes and hypotheses. For example,
the note for I.3 explicitly excludes two closed-form constants: the Lean result uses a Sobolev
pairing for the synthesis constant instead. Definitions are `sorry`-free; properties that do
not follow merely from a definition are stated and proved separately.

`STATUS.md` is generated from the local index, declarations, and comparator configuration;
generating it does not itself run comparator. Reproduction commands are in
[README.md](../README.md#reproduce-the-comparator-check), with development checks in
[CONTRIBUTING.md](../CONTRIBUTING.md#validation-and-generated-files).

## Repository and dependencies

| Location | Purpose |
| --- | --- |
| [OperatorRidgelet/](../OperatorRidgelet/) | Mathematics Lake project, including `Challenge`, `Solution`, comparator data and scripts |
| [OperatorRidgeletBlueprint/](../OperatorRidgeletBlueprint/) | Verso Blueprint, depending on the mathematics project by path |
| [OperatorRidgelet/LeanRidgelet/](../OperatorRidgelet/LeanRidgelet/) | Vendored activation spaces, Fourier conventions and general analysis tools from `shosonoda/lean-ridgelet`; [provenance](../OperatorRidgelet/LeanRidgelet.lean) |
| [OperatorRidgelet/NeuralNetworkProofs/](../OperatorRidgelet/NeuralNetworkProofs/) | Vendored Leshno theorem and dependencies from `davorrunje/neural-network-proofs`; [provenance and adaptation](../OperatorRidgelet/NeuralNetworkProofs.lean) |
| [attic/lean/](../attic/lean/) | Retired files, excluded from the build |

Both Lake projects pin Lean 4.32.0 and Mathlib v4.32.0. Other dependencies are
[FoML](https://github.com/auto-res/lean-rademacher) for Rademacher complexity,
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) for dependency metadata, and
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) for the presentation.
The `lakefile.toml` and tracked `lake-manifest.json` files in each project record the pins.
