import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Examples
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

#doc (Manual) "Appendix E. Details of the examples" =>
%%%
file := "appendix-e"
number := false
%%%

A Gaussian integral gives the closed-form transform of the Gaussian target and the
operator-layer formula. The Gaussian activation also has an exact ReLU hinge representation.
These identities concern the exact infinite-dimensional objects; the numerical experiments
in Section 8 use finite representations of their directions.

# E.1 A Gaussian integral
%%%
number := false
%%%

:::lemma_ "lem:E.1" (lean := "OperatorRidgelet.Paper.lem_E_1_i, OperatorRidgelet.Paper.lem_E_1_ii") (uses := "aux:trace-class-operators, aux:centered-gaussian")
Let $`\Sigma` be a positive self-adjoint trace-class operator, $`S` a bounded positive
self-adjoint operator, and $`x\in H`. Then $`M=\Sigma^{1/2}S\Sigma^{1/2}` is trace class (i),
and
$`\int_He^{i\langle x,\xi\rangle-\langle S\xi,\xi\rangle/2}\,\mathcal N(0,\Sigma)(\mathrm d\xi)=\det(I+M)^{-1/2}\exp\bigl(-\tfrac12\langle\Sigma^{1/2}(I+M)^{-1}\Sigma^{1/2}x,x\rangle\bigr)`
(ii).
:::

:::proof "lem:E.1"
In an orthonormal eigenbasis $`(u_j)` of $`M` with eigenvalues $`m_j`, the Gaussian series
$`\xi=\sum_j\eta_j\Sigma^{1/2}u_j` has law $`\mathcal N(0,\Sigma)`,
$`\langle S\xi,\xi\rangle=\sum_jm_j\eta_j^2`, and the expectation factorizes into
one-dimensional Gaussian integrals $`(1+m_j)^{-1/2}e^{-x_j^2/(2(1+m_j))}`.
:::

# E.2 Proof of Example 7.1
%%%
number := false
%%%

We prove {bpref "ex:7.1"}[].

:::proof "ex:7.1" (uses := "lem:E.1, lem:3.4, lem:3.9, lem:A.2, thm:4.3, lem:D.3, thm:6.4")
{bpref "lem:E.1"}[] with $`\Sigma=Q`, $`S=W` gives $`F_Qf_W`, Fourier
inversion in the bias gives the convolution, $`(I+M)^{-1}\ge(1+\|M\|)^{-1}I` gives the decay
needed by {bpref "lem:3.9"}[], and $`f_W(x)<1=f_W(0)` for $`x\ne0` in the kernel
of a finite-rank map. Part (ii) is {bpref "thm:4.3"}[] (iii) with the Gaussian integral applied
on each Gaussian component of $`\nu_\alpha`; part (iii) is {bpref "lem:D.3"}[] (a) with
$`S_W\ge(1+\|M\|)^{-1}Q` followed by {bpref "thm:6.4"}[].
:::

# E.3 The hinge representation of the Gaussian
%%%
number := false
%%%

:::definition "aux:relu-identities" (lean := "LeanRidgelet.relu, OperatorRidgelet.relu_sub_relu_neg, OperatorRidgelet.spectralReLUNetwork, OperatorRidgelet.spectralReLUNetwork_eq")
$`\operatorname{ReLU}(x)=\max(x,0)` and its odd part is the identity,
$`\operatorname{ReLU}(x)-\operatorname{ReLU}(-x)=x`. For a finite spectral index set, the
paired-ReLU network $`\sum_i\lambda_i[\operatorname{ReLU}(\langle e_i,x\rangle)-\operatorname{ReLU}(-\langle e_i,x\rangle)]e_i`
therefore equals the spectral truncation $`\sum_i\lambda_i\langle e_i,x\rangle e_i` exactly.
:::

:::lemma_ "lem:E.2" (lean := "OperatorRidgelet.Paper.lem_E_2_i_a, OperatorRidgelet.Paper.lem_E_2_i_b, OperatorRidgelet.Paper.lem_E_2_ii") (uses := "aux:gaussian-target, aux:relu-identities")
For $`\phi(u)=e^{-u^2/2}`, the integral $`\int_{\mathbb R}(u-b)_+\phi''(b)\,\mathrm db`
converges absolutely for each $`u` (i a) and equals $`\phi(u)` (i b), and
$`\int_{\mathbb R}(1+|b|^k)|\phi''(b)|\,\mathrm db<\infty` for every $`k\ge0` (ii).
:::

:::proof "lem:E.2"
$`\phi''(b)=(b^2-1)e^{-b^2/2}` has all polynomially weighted absolute integrals finite, and
integrating by parts on $`(-L,u)` gives
$`\int_{-L}^u(u-b)\phi''(b)\mathrm db=\phi(u)-\phi(-L)-(u+L)\phi'(-L)\to\phi(u)`.
:::

# E.4 Proof of Example 7.4
%%%
number := false
%%%

We prove {bpref "ex:7.4"}[].

:::proof "ex:7.4" (uses := "cor:6.6, thm:6.3, lem:3.4, lem:3.9, lem:D.3, thm:4.6, lem:E.2")
Part (i) is the change of variables for the pushforward measure and
$`\|\iota(y)\|^2\le\|A\|_\infty^2`. For (ii), the pair
$`(\langle a_y,x\rangle,\langle x,\xi\rangle)` is centred Gaussian under $`\mu_Q` and
$`\mathbb E[e^{-Z^2/2}e^{-iW}]=(1+\sigma^2)^{-1/2}\exp(-\tau^2/2+r^2/(2(1+\sigma^2)))`;
Cauchy–Schwarz gives the lower bound on $`S_y`, {bpref "lem:D.3"}[] (a) and
(c) give the condition in {bpref "def:4.1"}[], and {bpref "thm:4.3"}[], {bpref "thm:6.4"}[], and
{bpref "thm:4.6"}[] give the rest. Part (iii) is Fubini with
{bpref "lem:E.2"}[]; for (iv), a vector $`x\in\ker L\setminus\ker A` gives
$`F_\varphi(tx)=F_\varphi(0)` for all $`t`, while dominated convergence gives
$`F_\varphi(tx)\to\int w_\varphi\mathbf 1_{\{Ax=0\}}\mathrm dm<F_\varphi(0)`.
:::
