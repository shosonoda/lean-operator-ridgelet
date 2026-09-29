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

#doc (Manual) "Appendix H. General input and direction weights" =>
%%%
file := "appendix-h"
number := false
%%%

The Gaussian construction is an instance of a more general weighted theory. The input
measure may be a Borel probability measure, and the direction measure may be a sigma-finite
homogeneous measure of full support. The Fourier-slice and coefficient arguments use these
properties directly. Additional hypotheses in the statement supply the core, injectivity
and density conclusions.

:::theorem "thm:H.1" (lean := "OperatorRidgelet.Paper.thm_H_1_plancherel_memLp, OperatorRidgelet.Paper.thm_H_1_plancherel, OperatorRidgelet.Paper.thm_H_1_extension, OperatorRidgelet.Paper.thm_H_1_extension_norm, OperatorRidgelet.Paper.thm_H_1_extension_closed_range, OperatorRidgelet.Paper.thm_H_1_extension_coefficient, OperatorRidgelet.Paper.thm_H_1_injective, OperatorRidgelet.Paper.thm_H_1_one_mem_iff, OperatorRidgelet.Paper.thm_H_1_dense, OperatorRidgelet.Paper.thm_H_1_backprojection, OperatorRidgelet.Paper.thm_H_1_stability") (uses := "aux:conventions, def:3.2, def:3.3, def:3.7")
Let $`\mu` be a Borel probability measure on $`H` and $`\nu` a $`\sigma`-finite Borel measure
with full support and $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for $`\omega\ne0`; define
$`\mathcal G_\mu`, $`\mathcal D_{\mu,\nu}`, and the completion $`\mathcal E_{\mu,\nu}` as in
the Gaussian case. Then the Fourier-slice identity, {bpref "thm:4.2"}[], {bpref "thm:3.11"}[], and
{bpref "thm:4.3"}[] (i)–(iii) remain valid with $`(\mu_Q,\nu_\alpha)` replaced by
$`(\mu,\nu)`: for $`f\in\mathcal D_{\mu,\nu}` the transform lies in $`L^2(\lambda)` and
satisfies the Plancherel identity, $`R_\rho` has a unique bounded extension of norm at most
$`((\!(\rho,\rho)\!)_\alpha)^{1/2}` (with equality when the core is nonzero), with closed range and
$`R_\rho=W_\rho U`, and
$`R_\rho f=0` implies $`f=0`. Moreover $`1\in\mathcal D_{\mu,\nu}` if and only if
$`\int_H|\widehat\mu(\xi)|^2\nu(\mathrm d\xi)<\infty`. The versions for general input and direction measures of
{bpref "thm:4.2"}[] and {bpref "thm:4.3"}[] are the Lean statements of those theorems themselves.
The backprojection and coefficient stability results also hold. If, in addition, $`\nu` is
finite on bounded sets, the spectral-density construction gives compact-open universality.
Full support alone does not imply this local finiteness assumption. Gaussian decay and
Hermite inversion retain their Gaussian hypotheses.
:::

:::proof "thm:H.1" (uses := "lem:3.4, lem:B.1, lem:3.8")
Since $`\mu` is finite, $`f\mu` is a finite complex measure and $`\mathcal G_\mu f` is
continuous; the proofs use only Fubini, the one-dimensional Plancherel and Parseval identities,
and the homogeneity substitution, which holds for $`\nu` by assumption. Completing
$`\mathcal D_{\mu,\nu}` makes $`\mathcal G_\mu` unitary onto the closure of its range, and
full support with Fourier uniqueness gives injectivity; finally $`\mathcal G_\mu1=\widehat\mu`.
:::
