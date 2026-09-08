import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Transform.Infra

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Infrastructure and roadmap" =>
%%%
file := "roadmap"
%%%

This chapter collects the infrastructure that Mathlib v4.32.0 lacks and that the manuscript
takes from the literature. Each item is either stated separately in Lean, outside the
comparator scheme (its proof is `sorry` until the construction is available), or is a planned
statement without a Lean association. Nodes without a Lean association are planned work, not
axioms: the manuscript items that cite them carry them as dependencies, so their proof status
stays "not ready" until the infrastructure is in place.

The definition modules also record obligations that the definitions leave open on purpose
(the Mathlib style of closing a definition with a junk value and stating the property as a
theorem): the value of the trace and of the Fredholm determinant does not depend on the
basis, the Hilbert–Schmidt norm equals $`\sum_n\|Ae_n\|^2` along every Hilbert basis, the
polar decomposition of a Hilbert-space-valued measure of bounded variation exists, and the
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

:::theorem "roadmap:gaussian-strong-law" (uses := "aux:centered-gaussian")
Strong law of large numbers for the normalized Gaussian coordinates: if $`W` has eigenvectors
$`e_j` and eigenvalues $`w_j>0`, then under $`\mathcal N(0,tW)` the averages
$`\frac1n\sum_{j\le n}\langle x,e_j\rangle^2/w_j` converge to $`t` almost surely. This is
the special case of the Feldman–Hájek dichotomy used by {bpref "prop:dilation-obstruction"}[].
:::

:::theorem "roadmap:wick-totality" (uses := "aux:centered-gaussian")
Finite products $`\prod_j\mathrm{He}_{n_j}(Y_j)` of Hermite polynomials in the independent
normalized coordinates $`Y_j=\langle x,e_j\rangle/\sqrt{q_j}` form a complete orthogonal
system in $`L^2(H,\mu_Q)` (the Wiener–Itô chaos decomposition), and polarization of the Wick
powers of $`\sum_jt_jY_j` expresses them through the directional Wick powers
$`\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))`. This is what the totality statement of
{bpref "lem:hermite-totality"}[] needs.
:::

:::theorem "roadmap:trace-and-determinant" (uses := "aux:centered-gaussian")
For a positive operator the trace $`\sum_i\langle Pe_i,e_i\rangle` has the same value along
every Hilbert basis, the Fredholm determinant $`\prod_i(1+m_i)` of a positive trace-class
operator has the same value along every orthonormal eigenbasis, and the intrinsic
Hilbert–Schmidt norm equals $`\sum_n\|Ae_n\|^2` along every Hilbert basis. These are the
basis-independence obligations left open by the definitions of the trace, the determinant,
and the Hilbert–Schmidt class.
:::

:::theorem "roadmap:polar-decomposition"
Every complex or Hilbert-space-valued measure $`\Gamma` of bounded variation has a polar
decomposition $`\Gamma=h|\Gamma|` with $`\|h\|=1` $`|\Gamma|`-almost everywhere (the
Radon–Nikodym theorem for vector measures). The sampled network of Section 6 is defined
through a density chosen when one exists; this statement removes the choice.
:::

:::theorem "roadmap:contraction-principle"
The contraction principle for Rademacher averages: for a real Lipschitz $`\psi` with
$`\psi(0)=0` and vectors $`u_j` in a compact index set,
$`\mathbb E\sup_x|\sum_j\varepsilon_j\psi(u_j(x))|\le2\operatorname{Lip}(\psi)\,\mathbb E\sup_x|\sum_j\varepsilon_ju_j(x)|`,
together with the scalar and Hilbert-space Khintchine inequalities. The proof of
{bpref "thm:lipschitz-barron"}[] applies it to the Lipschitz activation; finite-sample
versions live in the project's `ToFoML` modules.
:::

:::theorem "roadmap:finite-dim-universality"
The finite-dimensional universal approximation theorem: for a continuous non-polynomial
$`\beta:\mathbb R\to\mathbb R`, finite linear combinations of $`\beta(\langle a,x\rangle+c)`
are dense in $`C(\mathbb R^m)` for uniform convergence on compact sets. The reduction argument
of {bpref "prop:scalar-universality"}[] composes it with finite-rank projections.
:::
