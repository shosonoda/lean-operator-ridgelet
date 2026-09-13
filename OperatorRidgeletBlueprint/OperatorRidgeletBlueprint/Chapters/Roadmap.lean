import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Transform.Infra
import OperatorRidgelet.ToMathlib.VectorMeasureRadonNikodym
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Infrastructure and roadmap" =>
%%%
file := "roadmap"
%%%

This chapter collects the infrastructure that Mathlib v4.32.0 lacks and that the manuscript
takes from the literature. Every manuscript item is verified, so every piece of infrastructure
that a manuscript item needs is proved as well, here or in a vendored third-party
development; each node below carries the Lean name that proves it. What remains without a Lean
association is not a missing step of a proof, but an obligation that a definition leaves open on
purpose, as the next paragraph explains.

The definition modules also record obligations that the definitions leave open on purpose
(the Mathlib style of closing a definition with a junk value and stating the property as a
theorem): the value of the trace and of the Fredholm determinant does not depend on the
basis, the Hilbert–Schmidt norm equals $`\sum_n\|Ae_n\|^2` along every Hilbert basis, and the
local stand-ins for the Section 4 and Section 6 objects used inside Section 5 and Section 7
(the anti-dual, the extended transform, and the sampled networks of the examples) are to be
unified with the definitions of the reconstruction and sampling chapters.

:::theorem "roadmap:gaussian-layers" (lean := "OperatorRidgelet.exists_isCenteredGaussianLayers") (uses := "aux:centered-gaussian")
For an injective, positive, self-adjoint, trace-class $`P` on a separable Hilbert space there
is a family of Gaussian layers $`\mathcal N(0,2sP)`, $`s>0`, with characteristic functionals
$`e^{-s\langle P\xi,\xi\rangle}`: the Gaussian series $`X=\sum_j\sqrt{p_j}Z_je_j` of
Appendix A, which converges in $`L^2(\Omega;H)` and almost surely. Mathlib has the class of
Gaussian measures but no constructor of a centred Gaussian measure with a prescribed
trace-class covariance in infinite dimension.
:::

:::theorem "roadmap:trace-and-determinant" (uses := "aux:centered-gaussian")
For a positive operator the trace $`\sum_i\langle Pe_i,e_i\rangle` has the same value along
every Hilbert basis, the Fredholm determinant $`\prod_i(1+m_i)` of a positive trace-class
operator has the same value along every orthonormal eigenbasis, and the intrinsic
Hilbert–Schmidt norm equals $`\sum_n\|Ae_n\|^2` along every Hilbert basis. These are the
basis-independence obligations left open by the definitions of the trace, the determinant,
and the Hilbert–Schmidt class.
:::

:::theorem "roadmap:polar-decomposition" (lean := "MeasureTheory.VectorMeasure.exists_withDensityᵥ_variation_eq")
Every complex or Hilbert-space-valued measure $`\Gamma` of bounded variation has a polar
decomposition $`\Gamma=h|\Gamma|` with $`\|h\|=1` $`|\Gamma|`-almost everywhere (the
Radon–Nikodym theorem for vector measures). Mathlib has the scalar Radon–Nikodym theorem but
not this form; it is proved in the project's `ToMathlib` modules, so the density that the
sampled network of Section 6 chooses always exists.
:::

:::theorem "roadmap:finite-dim-universality" (lean := "UniversalApproximation.Leshno.leshno_dense")
The finite-dimensional universal approximation theorem: for a continuous non-polynomial
$`\beta:\mathbb R\to\mathbb R`, finite linear combinations of $`\beta(\langle a,x\rangle+c)`
are dense in $`C(\mathbb R^m)` for uniform convergence on compact sets. The reduction argument
of {bpref "prop:scalar-universality"}[] composes it with finite-rank projections. Mathlib does
not have it; the project vendors the formalization of Runje (Apache 2.0) under
`NeuralNetworkProofs/`.
:::
