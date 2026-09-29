import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Sampling
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

#doc (Manual) "Appendix D. Proofs for Section 6 and supplementary approximation results" =>
%%%
file := "appendix-d"
number := false
%%%

The uniform approximation estimates require a Banach-valued law of large numbers for
Rademacher averages and, for the explicit rate, a Hilbert-valued contraction argument.
We then verify regularity along rays, prove the spectral moment and universality results,
and record concentration, Hilbert-norm approximation and input-truncation estimates.

:::lemma_ "lem:D.1" (lean := "OperatorRidgelet.Paper.lem_D_1_i, OperatorRidgelet.Paper.lem_D_1_ii") (uses := "def:6.1")
Let $`X` be a separable Banach space, $`p` a probability measure, and $`\Phi\in L^1(p;X)`.
For independent samples $`\theta_j\sim p` and independent Rademacher signs $`\varepsilon_j`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X\to0`.
Moreover, for $`N\ge1` and $`m=\int\Phi\,\mathrm dp`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\Phi(\theta_j)-m\|_X\le2\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X`.
:::

:::proof "lem:D.1"
Approximate $`\Phi` in $`L^1` by a simple function
$`\Psi=\sum_{k=1}^Jx_k\mathbf1_{E_k}`. The signed-average error has expected norm at most
$`\|\Phi-\Psi\|_{L^1}`. For $`\Psi`, the scalar second-moment identity and Cauchy–Schwarz
bound the expected norm by $`\sum_k\|x_k\|\sqrt{p(E_k)/N}`, which tends to zero.
For symmetrization, introduce a ghost sample, apply Jensen, and insert independent signs
using exchangeability of each pair. The triangle inequality gives the factor two.
Bochner integrability justifies every expectation.
:::

# D.1 Proof of Theorem 6.3
%%%
number := false
%%%

We prove {bpref "thm:6.3"}[].

:::proof "thm:6.3" (uses := "thm:6.2, lem:D.2")
Write the output norm as a supremum of real inner products over the unit ball of $`Y`, so that
the signed process is indexed by $`K\times B_Y`. The increments of
$`\psi_j(x,y)=\beta(\langle a_j,x\rangle+c_j)\langle y,h_j\rangle` are dominated by those
of $`\operatorname{Lip}(\beta)(\langle a_j,x\rangle+c_j)` and of
$`B_j\langle y,h_j\rangle` with $`B_j=|\beta(0)|+\operatorname{Lip}(\beta)R_K\|(a_j,c_j)\|`,
so {bpref "lem:D.2"}[] applies. Hilbert duality and the Khintchine
inequality bound the two resulting averages by
$`\operatorname{Lip}(\beta)R_K(\sum_j\|(a_j,c_j)\|^2)^{1/2}` and
$`(\sum_jB_j^2)^{1/2}`, and symmetrization and Jensen's inequality give (i). An integrable
random variable cannot exceed its expectation almost surely, which gives (ii).
:::

:::lemma_ "lem:D.2" (lean := "OperatorRidgelet.Paper.lem_D_2") (uses := "def:6.1")
Let $`S` be a nonempty set and let $`\psi_i,u_i,v_i:S\to\mathbb R` be bounded with
$`|\psi_i(s)-\psi_i(t)|\le|u_i(s)-u_i(t)|+|v_i(s)-v_i(t)|` for all $`s,t`. Then
$`\mathbb E\sup_s\sum_i\varepsilon_i\psi_i(s)
  \le2\mathbb E\sup_s\sum_i(\varepsilon_{i1}u_i(s)+\varepsilon_{i2}v_i(s))`
for independent Rademacher signs.
:::

:::proof "lem:D.2"
Fix all signs but $`\varepsilon_i`. Choosing near-maximizers $`s_\pm` of $`F\pm\psi_i` and
using $`\mathbb E|A+D|\ge\mathbb E|D|` for a symmetric $`D`, together with
$`\mathbb E|\eta_1r+\eta_2q|=\max\{|r|,|q|\}\ge(|r|+|q|)/2`, gives the one-sign comparison
with an arbitrary bounded offset $`F`. Replacing one coordinate at a time and averaging over
the remaining signs proves the statement.
:::

:::lemma_ "lem:D.3" (lean := "OperatorRidgelet.Paper.lem_D_3_a, OperatorRidgelet.Paper.lem_D_3_b_i, OperatorRidgelet.Paper.lem_D_3_b_ii, OperatorRidgelet.Paper.lem_D_3_c_i, OperatorRidgelet.Paper.lem_D_3_c_ii") (uses := "def:4.1")
The following functions satisfy {bpref "def:4.1"}[] for every band-pass $`\rho`.
(a) $`G(\xi)=q(\xi)e^{-\kappa(\xi)/2}`, where $`\kappa(\xi)=\langle S\xi,\xi\rangle`,
$`S` is bounded and positive, $`S\ge\theta Q` for some $`\theta>0`, and $`q` is a
polynomial in $`\kappa` and finitely many bounded linear functionals $`\ell_i` satisfying
$`|\ell_i(\xi)|^2\le C_i\kappa(\xi)` for every $`\xi`. Equivalently,
$`\ell_i=\langle S^{1/2}v_i,\cdot\rangle` for some $`v_i\in H`. A polynomial in
$`\kappa` alone requires no further condition.
(b) $`G(\xi)=\varphi(\|\xi-\xi_0\|^2)` for $`\varphi\in C_c^\infty(\mathbb R)`;
more generally, bounded densities with bounded support, smooth restrictions
$`G_a(\omega)=G(\omega a)` near $`I`, and
$`\sup_{\omega\in I}|\partial_\omega^kG(\omega a)|\le C_k(1+\|a\|)^{p_k}` for every $`k`.
(c) Finite linear combinations, and Bochner integrals $`G=\int_\Omega G_y\,m(\mathrm dy)`
of uniformly bounded measurable families over a finite measure, subject to these
neighbourhood bounds: there is an open $`U\supset I` where every function
$`\omega\mapsto G_y(\omega a)` is smooth, and finite-valued Borel $`h_k:H\to[0,\infty)` such that
$`\sup_{\omega\in U}|\partial_\omega^kG_y(\omega a)|\le h_k(a)` for every $`y,a,k`, and
$`\int_H(1+\|a\|)^{m+2}\max_{k\le m}h_k(a)\,\nu_\alpha(\mathrm da)<\infty` for every $`m`.
The bounds hold on the open neighbourhood and for every direction.
:::

:::proof "lem:D.3" (uses := "lem:3.9, lem:3.1")
For (a), domination of the linear functionals gives $`|q(\xi)|\le C(1+\kappa(\xi))^p`,
so $`G` is bounded. Derivatives of $`G_a(\omega)=G(\omega a)` with respect to $`\omega`
are polynomials times $`e^{-\omega^2\kappa(a)/2}`;
on $`I\subset\{r\le|\omega|\le R\}` their bound is
$`C_k(1+\|a\|)^{p_k}e^{-r^2\theta\langle Qa,a\rangle/2}`. Apply
{bpref "lem:3.9"}[]. For (b), derivatives vanish outside a bounded set of
directions, on which $`\nu_\alpha` is finite. For (c), the finite neighbourhood bounds
justify differentiation under the Bochner integral for each direction. The triangle
inequality and Tonelli give
$`M_m(G)\le m(\Omega)\int_H(1+\|a\|)^{m+2}\max_{k\le m}h_k(a)\,\nu_\alpha(\mathrm da)<\infty`.
:::

# D.2 Proof of Theorem 6.4
%%%
number := false
%%%

We prove {bpref "thm:6.4"}[].

:::proof "thm:6.4" (uses := "lem:B.3, thm:4.2, thm:6.3, lem:3.1")
Apply {bpref "lem:B.3"}[] and $`A_{r+2,r}(G)\le M_{r+2}(G)`.
The coefficient decays as $`(1+|c|)^{-r-2}`; two powers give an integrable bias weight and
the other $`r` powers control the parameter moment. The scalar constant is independent of $`Y`.
Use $`1+\|a\|^2+|c|^2\le(1+\|a\|+|c|)^2` for the second moment, then
{bpref "thm:4.2"}[] (iii) and {bpref "thm:6.3"}[] for synthesis and sampling.
:::

# D.3 Proof of Theorem 6.5
%%%
number := false
%%%

We prove {bpref "thm:6.5"}[].

:::proof "thm:6.5" (uses := "thm:5.2, lem:D.3, thm:4.2, thm:6.4, lem:D.4, cor:6.6, thm:4.6")
Finite sums of characters $`e^{i\langle x,\xi\rangle}` form a self-conjugate algebra
containing the constants and separating points, so Stone–Weierstrass gives a trigonometric
approximant on $`K`; each character is within $`r_K\delta` of $`g_{G_j}` for a normalized
smooth bump $`G_j` supported in the ball of radius $`\delta` around $`\xi_j`. Full support
makes its normalizing integral positive, and finiteness on bounded sets makes it finite.
By {bpref "lem:D.3"}[], the sum $`G=\sum_jw_jG_j` satisfies
{bpref "def:4.1"}[]. Then {bpref "thm:4.2"}[] (iii), {bpref "thm:6.4"}[], and
{bpref "thm:6.3"}[] give (ii) and (iii); the vector-valued case uses a partition
of unity and {bpref "thm:4.6"}[].
:::

# D.4 Supplementary approximation results
%%%
number := false
%%%

:::lemma_ "lem:D.4" (lean := "OperatorRidgelet.Paper.lem_D_4") (uses := "def:2.2, def:6.1, aux:sampling-data")
Let $`\beta:\mathbb R\to\mathbb C` be continuous, $`K\subset H` compact, and
$`\int\|\beta(\langle a,\cdot\rangle+c)\|_{C(K)}\,\mathrm d|\Gamma|(a,c)<\infty`. Then for
every $`\varepsilon>0` there is a finite atomic complex measure $`\Gamma_\varepsilon` with
$`\|S_\beta\Gamma_\varepsilon-S_\beta\Gamma\|_{C(K)}<\varepsilon`.
:::

:::proof "lem:D.4"
The atom map is continuous into the separable Banach space $`C(K)`, so
$`Y(a,c)=h(a,c)\beta(\langle a,\cdot\rangle+c)|_K` is Bochner integrable and its mean lies in
the closed convex hull of its essential range by Hahn–Banach separation; approximate the mean
by a finite convex combination of essential-range values.
:::

:::corollary "cor:D.5" (lean := "OperatorRidgelet.Paper.cor_D_5") (uses := "thm:6.3, aux:sampling-data")
Under the hypotheses of {bpref "thm:6.3"}[], suppose $`\|a\|^2+|c|^2\le B^2`
almost surely and put $`M_K=|\beta(0)|+\operatorname{Lip}(\beta)R_KB`. With probability at
least $`1-\delta`,
$`\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)+VM_K\sqrt{2\log(1/\delta)/N}`.
:::

:::proof "cor:D.5"
Each atom has norm at most $`M_K`, so replacing one sample changes $`\|f_N-f\|_{C(K)}` by at
most $`2VM_K/N`; the bounded-difference inequality bounds the excess over the expectation.
:::

:::lemma_ "lem:D.6" (lean := "OperatorRidgelet.Paper.lem_D_6_i, OperatorRidgelet.Paper.lem_D_6_ii, OperatorRidgelet.Paper.lem_D_6_iii") (uses := "def:6.1")
Let $`X` be a separable Hilbert space and $`Y\in L^2(p;X)`. For independent copies $`Y_j`,
$`f=V\,\mathbb EY`, and $`f_N=VN^{-1}\sum_jY_j`,
$`\mathbb E\|f_N-f\|_X^2=\frac{V^2}N(\mathbb E\|Y\|_X^2-\|\mathbb EY\|_X^2)` (i), which is
at most $`\frac{V^2}N\mathbb E\|Y\|_X^2` (ii), and a deterministic sample satisfies the same
upper bound (iii).
:::

:::proof "lem:D.6"
With $`Z_j=Y_j-\mathbb EY`, independence and zero means make
$`\mathbb E\langle Z_j,Z_k\rangle=0` for $`j\ne k`, so the expanded squared norm leaves
$`N\,\mathbb E\|Z_1\|^2`.
:::

:::corollary "cor:D.7" (lean := "OperatorRidgelet.Paper.cor_D_7_i, OperatorRidgelet.Paper.cor_D_7_ii") (uses := "aux:sampling-data")
Let $`\Gamma_{\mathrm{op}}` be a finite complex measure on $`\mathcal L_2(H)\times H` with
polar decomposition $`h_{\mathrm{op}}|\Gamma_{\mathrm{op}}|`, $`V_{\mathrm{op}}>0`,
$`p_{\mathrm{op}}=|\Gamma_{\mathrm{op}}|/V_{\mathrm{op}}`, let $`\beta` be real and globally
Lipschitz, and assume $`M_{\mathrm{op}}^2<\infty`. Sampling $`(A_j,b_j)` from
$`p_{\mathrm{op}}` with the weights $`h_{\mathrm{op}}` gives
$`\mathbb E\|f_{\mathrm{op},N}-S_{\mathrm{op}}\Gamma_{\mathrm{op}}\|_{C(K)}\le8V_{\mathrm{op}}N^{-1/2}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_{\mathrm{op}})`
(i), and $`M_{\mathrm{op}}^2\le\|\psi\|^2\int(\|A\|_{\mathcal L_2}^2+\|b\|^2)\,\mathrm dp_{\mathrm{op}}`
(ii).
:::

:::proof "cor:D.7" (uses := "thm:6.3, lem:F.4")
The atom is the scalar ridge with parameter $`\pi_\psi(A,b)`, so the proof of
{bpref "thm:6.3"}[] applies on the operator probability space with $`M_2`
replaced by $`M_{\mathrm{op}}`; Cauchy–Schwarz and $`\|A\|_{\mathrm{op}}\le\|A\|_{\mathcal L_2}`
give the last estimate.
:::

:::corollary "cor:D.8" (lean := "OperatorRidgelet.Paper.cor_D_8_i, OperatorRidgelet.Paper.cor_D_8_ii") (uses := "thm:6.3, aux:sampling-data")
Let $`\Pi_m` be finite-rank orthogonal projections converging strongly to the identity. For
$`f\in C(H)` and compact $`K`, $`\|f-f\circ\Pi_m\|_{C(K)}\to0` (i). If $`f=S_\beta\Gamma`
satisfies the hypotheses of {bpref "thm:6.3"}[] and the same samples are used
with directions $`\Pi_ma_j`, then
$`\mathbb E\|f-f_{m,N}\|_{C(K)}\le\operatorname{Lip}(\beta)\bigl(\int\|a\|\,\mathrm d|\Gamma|\bigr)\sup_K\|x-\Pi_mx\|+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`
(ii).
:::

:::proof "cor:D.8"
A finite-net argument gives $`\sup_K\|x-\Pi_mx\|\to0`, and uniform convergence of
$`f\circ\Pi_m` on $`K` follows by compactness and continuity of $`f`; the triangle inequality
separates truncation from sampling, and projecting directions does not increase their second
moment.
:::
