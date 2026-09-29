import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.BasisIndependence
import OperatorRidgelet.Paper.Examples
import OperatorRidgelet.Paper.Networks
import OperatorRidgelet.Paper.Reconstruction
import OperatorRidgelet.Paper.Revision
import OperatorRidgelet.Paper.Sampling
import OperatorRidgelet.Paper.SamplingRevision
import OperatorRidgelet.Paper.Sobolev
import OperatorRidgelet.Paper.Tempered
import OperatorRidgelet.Paper.Transform
import OperatorRidgelet.ToMathlib.VectorMeasureRadonNikodym
import OperatorRidgelet.Transform.Infra

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Formalization infrastructure" =>
%%%
file := "infrastructure"
number := false
%%%

This reference chapter records mathematical infrastructure used by the Lean proofs.
It is separate from the manuscript's numbered exposition. Each statement below is proved;
the links expose its Lean formulation and dependencies. Auxiliary definitions elsewhere in
the Blueprint likewise have descriptive identifiers and are not additional manuscript results.

The formalization uses the bias coordinate $`c=-b`; some statements carry the abstract
input/direction measures used in the supporting proofs. The $`L^2` conclusion of Theorem 5.6 and the closed
forms of the constants in Proposition 5.8 are recorded in weaker forms in the Lean statements.
These distinctions are explained with the corresponding formal statements.

:::theorem "roadmap:gaussian-layers" (lean := "OperatorRidgelet.exists_isCenteredGaussianLayers") (uses := "aux:centered-gaussian")
For an injective, positive, self-adjoint, trace-class $`P` on a separable Hilbert space there
is a family of Gaussian components $`\mathcal N(0,2sP)`, $`s>0`, with characteristic functionals
$`e^{-s\langle P\xi,\xi\rangle}`: the Gaussian series $`X=\sum_j\sqrt{p_j}Z_je_j` of
Appendix A, which converges in $`L^2(\Omega;H)` and almost surely. Mathlib has the class of
Gaussian measures but no constructor of a centred Gaussian measure with a prescribed
trace-class covariance in infinite dimension.
:::

:::theorem "roadmap:trace-and-determinant" (lean := "OperatorRidgelet.traceOf_eq_traceAlong, OperatorRidgelet.fredholmDet_eq_fredholmDetAlong") (uses := "aux:centered-gaussian")
For a positive operator, the trace $`\sum_i\langle Pe_i,e_i\rangle` has the same value
along every Hilbert basis. The Fredholm determinant $`\prod_i(1+m_i)` of a positive
trace-class operator has the same value along every orthonormal eigenbasis. Thus the
chosen bases in `traceOf` and `fredholmDet` do not affect the Gaussian-target formulas.
The trace is compared through the orthonormal eigenbasis supplied by its convergence;
the multiplicity of a nonzero eigenvalue is identified with the trace of the projection
onto its eigenspace.
:::

:::theorem "roadmap:polar-decomposition" (lean := "MeasureTheory.VectorMeasure.exists_withDensityᵥ_variation_eq")
Every complex or Hilbert-space-valued measure $`\Gamma` of bounded variation has a polar
decomposition $`\Gamma=h|\Gamma|` with $`\|h\|=1` $`|\Gamma|`-almost everywhere (the
Radon–Nikodym theorem for vector measures). Mathlib has the scalar Radon–Nikodym theorem but
not this form; it is proved in the project's `ToMathlib` modules, so the density that the
sampled network of Section 6 chooses always exists.
:::
