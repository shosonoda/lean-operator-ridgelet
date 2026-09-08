import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Formalization roadmap" =>
%%%
file := "roadmap"
%%%

Nodes without an associated Lean declaration are planned work, not axioms. The statistical-learning
components in `OperatorRidgelet.ToFoML` are tracked by the LeanArchitect bridge and will receive
blueprint nodes when the sampling chapter is written.

The Gaussian-weighted chapter is a different kind of planned work: its statements are already
formalized in Lean and only their proofs are outstanding, so they appear in the work queue with
`statementStatus` formalized and `proofStatus` incomplete. The items below are the analytic
prerequisites that those proofs will need.

:::theorem "roadmap:gaussian-mixture" (uses := "gauss-ridgelet:homogeneous-exists")
Construct the Gaussian mixture $`\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)s^{\alpha/2-1}\mathrm ds`
on a separable Hilbert space and prove the small-ball estimate that makes it finite on balls. This
needs centred Gaussian measures with a prescribed trace-class covariance, together with their
supports and characteristic functionals.
:::

:::theorem "roadmap:feldman-hajek" (uses := "gauss-ridgelet:dilation-obstruction")
Prove the Feldman--H\'ajek dichotomy in the special case needed here: two centred Gaussian measures
with proportional trace-class covariances are mutually singular on an infinite-dimensional space
unless the proportionality constant is one.
:::

:::theorem "roadmap:wick-powers-total" (uses := "gauss-ridgelet:de-gaussianized-determines")
Prove that the Wick powers $`:\langle x,\xi\rangle^n:`, over all $`n` and all $`\xi`, are total in
$`L^2(H,\mu)` for a centred Gaussian $`\mu`. This is the Wiener--It\^o chaos decomposition together
with polarization on symmetric tensor powers, and it is what makes the inversion of the analysis
map unambiguous.
:::

:::theorem "roadmap:gaussian-relu" (uses := "operator-ridgelet:kernel-obstruction")
Formalize the infinite-rank Gaussian ReLU representation on $`\ell^2` and prove that it is not
cylindrical through any finite-rank observation.
:::

:::theorem "roadmap:compact-open-atomic"
Formalize finite-atomic approximation in the compact-open topology for the general activation
class used in the manuscript.
:::

:::theorem "roadmap:maurey-jones-barron" (uses := "roadmap:compact-open-atomic")
Formalize the Hilbert-valued Maurey--Jones--Barron variance identity and its $`N^{-1/2}` rate.
:::

:::theorem "roadmap:e3-equivariant" (uses := "roadmap:compact-open-atomic")
Formalize the E(3)-equivariant convolution--activation example and its compact-open approximation.
:::

:::theorem "roadmap:elliptic-solution-operator" (uses := "operator-ridgelet:spectral-relu-exact, operator-ridgelet:kernel-obstruction")
Formalize the Dirichlet elliptic solution operator and its $`O(N^{-2})` spectral truncation rate.
:::
