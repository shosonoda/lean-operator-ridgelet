# Guide to the formalization

This guide maps the operator ridgelet manuscript to the Lean sources. For an item-by-item list
of labels, numbers, declaration names, and verification status, see [STATUS.md](../STATUS.md).
The [Verso Blueprint](https://shosonoda.github.io/lean-operator-ridgelet/) presents the informal
mathematics alongside Lean declarations and their dependencies, following manuscript
Sections 1–9 and Appendices A–E and then the supporting infrastructure.

## Reading a manuscript item in Lean

The manuscript itself is not included. Its index,
[paper.json](../OperatorRidgelet/comparator/paper.json), records the 2026-10-07 reading-order manuscript revision and
includes a `note` for each item describing how it is formalized. These notes explain such
choices as explicit hypotheses, representations of operators, and the scope of each statement.

For example, Theorem 3.14 (`thm:B`, Plancherel identity and injectivity) corresponds to the
`OperatorRidgelet.Paper.thm_3_14_*` declarations in
[Paper/Transform.lean](../OperatorRidgelet/OperatorRidgelet/Paper/Transform.lean). Its independent
statements are in [Challenge/Transform.lean](../OperatorRidgelet/Challenge/Transform.lean),
its definitions in [Transform/Defs.lean](../OperatorRidgelet/OperatorRidgelet/Transform/Defs.lean),
and its supporting proofs in the other `Transform/` modules.

In general, manuscript results have names
`OperatorRidgelet.Paper.<kind>_<number>[_<part>]`: dots in the manuscript number become
underscores, as in `thm_3_14_i_a` or `cor_D_2_i`. Multipart results may be split into several
Lean declarations; vector-valued parts use descriptive `plancherel`, `representation`, and
`frame` suffixes. Pure definitions retain their semantic names, usually directly in the
`OperatorRidgelet` namespace. The index keeps the source LaTeX `label` separately from the
numbered `blueprint_label`: Theorem 3.14 has source label `thm:B` and Blueprint label
`thm:3.14`. Its informal statement and Lean declarations appear together in the corresponding
mathematical chapter; the index's formalization note explains the verification scope.

A numbered Blueprint node also collects the Lean definitions used in that manuscript item.
For example, the backprojection definitions belong to Lemma 3.9 and the coefficient
projection to Proposition B.1; the Hermite definitions belong to Lemma 4.7. Setup for
a numbered example appears with that example. Shared conventions without a unique numbered
counterpart retain descriptive identifiers and state their manuscript locations. The polar
decomposition is the unnumbered vector-measure fact before Definition 2.2; it supplies the
sampling data of Definition 6.1, and both dependency edges are recorded.

## Mathematical source map

All paths in this table are relative to
[OperatorRidgelet/OperatorRidgelet/](../OperatorRidgelet/OperatorRidgelet/). `Paper/` collects the
manuscript-facing theorems; the other modules supply definitions and supporting proofs.

| Subject and manuscript items | Definitions and supporting mathematics | Manuscript-facing proofs |
| --- | --- | --- |
| Networks (§2) | `Network/` | `Paper/Networks.lean` |
| Gaussian measures, partial Fourier transform, coefficient isometry and Plancherel (§3, Theorem 3.14) | `Transform/`, `Reconstruction/` | `Paper/Transform.lean`, `Paper/Revision.lean` |
| Spectral targets, coefficient decay, integral representation, Hermite inversion and frame reconstruction (§4, Theorems 4.5 and 4.8) | `Reconstruction/` | `Paper/Reconstruction.lean`, `Paper/Revision.lean` |
| Weighted Sobolev duality, tempered activations, ReLU and reconstruction (§5) | `Tempered/`, `Sobolev/`, `Activation.lean` | `Paper/Tempered.lean`, `Paper/Sobolev.lean` |
| Rademacher bounds, finite-width approximation and universality (§6, Theorems 6.6 and 6.8) | `Sampling/`, `ToFoML/` | `Paper/Sampling.lean`, `Paper/SamplingRevision.lean`, `Paper/Revision.lean` |
| Gaussian identities, targets and operator layers (§7) | `Examples/` | `Paper/Examples.lean` |
| Regularized characteristic functional (Appendix A) | `Transform/` | `Paper/Transform.lean` |
| Projection and minimum-norm solutions (Appendix B) | `Reconstruction/` | `Paper/Reconstruction.lean` |
| Concentration and input truncation (Appendix C) | `Sampling/` | `Paper/Sampling.lean`, `Paper/SamplingRevision.lean` |
| Finite-dimensional comparison and dilation obstruction (Appendix D) | `FiniteDim/`, `Transform/` | `Paper/Transform.lean` |
| Numerical methods (Appendix E) | Numerical exposition only | No additional theorem assertions |

`Revision.lean` and `SamplingRevision.lean` contain additional statements from manuscript
revisions; consult them together with the main topic files. The `lean` lists in `paper.json`
and the table in `STATUS.md` give the exact declaration names for each item.

General-purpose results on Fourier analysis, Gaussian measures, operators, and integration live
in [ToMathlib/](../OperatorRidgelet/OperatorRidgelet/ToMathlib/), with Mathlib-only imports.
[BasisIndependence.lean](../OperatorRidgelet/OperatorRidgelet/BasisIndependence.lean) discharges
the basis-independence obligations for the trace and Fredholm determinant.

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

### Terminology and retained Lean names

For a spectral density `G`, write `G_a(ω) := G (ω • a)`. For nonzero `a`, this is
the restriction of `G` to the line through the origin spanned by `a`; `G_0` is constant.
The short phrase *regularity along rays* means smoothness of these functions near the
specified frequency window together with weighted integrability of their derivative bounds.
`IsRegularAlongRays`, `rayDerivBound`, and related declaration names retain this convention.

The current notation uses `T_α` alone for the frame/Riesz operator, and `F_Q`
for both the Gaussian-weighted transform on its concrete core and its unitary
extension to `𝓔_α`. In the spectral-range realization the completed map is the
inclusion into `L²(ν)`; its core restriction is `spectralEmbed`. The transpose
`F_Q′` has domain `L²(ν)` and codomain `𝓔_α′`, rather than ambient `L²(μ)`.
General elements of the completion need not have pointwise input representatives.
Paper notation uses sharp for one-dimensional and bias Fourier transforms and
hat for spatial Fourier–Stieltjes transforms and torus coefficients. The actual
Lean Fourier definitions retain the angular convention and their semantic names;
Mathlib's `𝓕`, where used, retains its own `2π` normalization.

The *frame operator* is used in its dual-space form: `frameOperator` maps the Hilbert space
to its continuous anti-dual and equals the Riesz map. The *backprojection* is the adjoint
of the coefficient operator, with values in the frequency-domain density space.
An analysis filter is *band-pass* here when it is nonzero and its smooth Fourier transform
has compact support away from zero. *ReLU is admissible* refers to its pairing with a suitable
analysis filter, giving a nonzero reconstruction constant; ReLU itself is not a Schwartz filter.

For an activation represented by a tempered distribution, synthesis is defined by regularizing
the activation and taking a norm limit in the continuous anti-dual (Definition 5.3). An
absolutely convergent network integral instead requires integrability of the integrand against
the total variation of its coefficient measure. These describe different aspects of the
construction: under the additional hypotheses of Theorems 4.5(iii) or 5.10, a continuous
activation of polynomial growth gives such an integral.

For Hilbert-valued functions, the Sobolev norm is the Bessel-potential norm in the frequency
variable. For Banach-valued functions, `MemRaySobolev` and `raySobolevNorm` directly express
weighted square integrability of a specified inverse Fourier transform. A Fourier isometry
is asserted only in the Hilbert-valued case. `polarLaw` denotes the sampling distribution
obtained by normalizing the total variation measure (zero when that measure is zero), and
`IsCenteredGaussianLayers` describes the Gaussian components of a scale mixture.
The terminology revision preserves the mathematical statements. Manuscript-facing `Paper`
declarations and Blueprint identifiers follow the current manuscript numbering; semantic
names for definitions and supporting mathematics remain unchanged.

The verification record has three components:

- [Challenge/](../OperatorRidgelet/Challenge/) states the propositions with intentional `sorry`
  proofs and imports only definition modules, never `OperatorRidgelet.Paper`.
- [Paper/](../OperatorRidgelet/OperatorRidgelet/Paper/) supplies the same statements with their
  proofs; [Solution.lean](../OperatorRidgelet/Solution.lean) imports these for comparator.
- [config.json](../OperatorRidgelet/comparator/config.json) lists the completed theorems.
  Comparator checks them against `Challenge`, allowing only `propext`, `Quot.sound`, and
  `Classical.choice`, with no admitted proofs.

All 62 indexed items are recorded as verified: 341 comparator statements plus the pure
definitions. This is verification of the indexed Lean formulations. Reviewing their agreement
with the manuscript also requires reading the formalization notes and hypotheses. For example,
the note for Proposition 5.12 explicitly excludes two closed-form constants: the Lean result uses a Sobolev
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
| [OperatorRidgeletBlueprint/vendor/VersoBlueprint/](../OperatorRidgeletBlueprint/vendor/VersoBlueprint/) | Pinned Verso Blueprint with a distinct Example node kind; [provenance](../OperatorRidgeletBlueprint/vendor/VersoBlueprint/PROVENANCE.md) |
| [OperatorRidgelet/LeanRidgelet/](../OperatorRidgelet/LeanRidgelet/) | Vendored activation spaces, Fourier conventions and general analysis tools from `shosonoda/lean-ridgelet`; [provenance](../OperatorRidgelet/LeanRidgelet.lean) |
| [attic/](../attic/) | Retired files, excluded from the build |

Both Lake projects pin Lean 4.32.0 and Mathlib v4.32.0. Other dependencies are
[FoML](https://github.com/auto-res/lean-rademacher) for Rademacher complexity,
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) for dependency metadata, and
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) for the presentation.
The `lakefile.toml` and tracked `lake-manifest.json` files in each project record the pins.
