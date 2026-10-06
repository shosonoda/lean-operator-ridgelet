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

#doc (Manual) "Representation and reconstruction" =>
%%%
file := "reconstruction"
%%%

A spectral density determines explicit network coefficients. We first establish the spectral-target and coefficient-decay estimates, then prove the integral representation. For reconstruction in $`\mathcal E_\alpha`, we next identify weak synthesis with the integral network and prove Hermite recovery. The frame operator and vector-valued extension follow from these preceding ingredients.

# Spectral targets and coefficient estimates

:::lemma_ "lem:4.1" (lean := "OperatorRidgelet.Paper.lem_4_1_i, OperatorRidgelet.Paper.lem_4_1_ii, OperatorRidgelet.Paper.lem_4_1_iii") (uses := "aux:conventions")
Let $`\nu` be a Borel measure on $`H`, let $`Y` be a separable complex Hilbert
space, and let $`G\in L^1(\nu;Y)`. Then
$`g_G(x)=\int_H e^{i\langle x,\xi\rangle}G(\xi)\,\nu(\mathrm d\xi)` belongs to
$`C_b(H;Y)`, satisfies $`\|g_G\|_\infty\le\|G\|_{L^1(\nu;Y)}`, and determines $`G` up to
$`\nu`-almost-everywhere equality. No input weight, filter, homogeneity, or full-support
assumption is needed.
:::

:::proof "lem:4.1"
The integral triangle inequality gives the norm bound, and dominated convergence with
majorant $`\|G(\xi)\|_Y` gives continuity. If $`g_G=0`, pair the finite vector measure
$`G\nu` with vectors in a countable dense subset of $`Y`. Fourier uniqueness makes each
resulting scalar measure zero: finite-dimensional Fourier uniqueness determines all cylinder
sets, which generate the Borel sigma-algebra of $`H`. Intersect the countably many
full-measure sets and use continuity of the pairing to obtain $`G=0` almost everywhere.
Apply the argument to a difference for uniqueness.
:::

:::definition "def:4.2" (lean := "OperatorRidgelet.IsFrequencyWindow, OperatorRidgelet.rayDerivBound, OperatorRidgelet.rayMoment, OperatorRidgelet.IsRegularAlongRays, OperatorRidgelet.spectralTarget, OperatorRidgelet.Paper.def_4_2") (uses := "def:3.3, aux:gaussian-mixture, lem:3.2")
Fix a symmetric compact set
$`I\subset\mathbb R\setminus\{0\}` containing $`\operatorname{supp}\rho^\sharp` (a frequency
window). Write $`G_a(\omega):=G(\omega a)`, the restriction to the line through the origin
spanned by $`a\ne0`, with $`G_0` constant. A bounded Borel $`G:H\to\mathbb C` is
regular along rays if every $`G_a` is $`C^\infty` on a neighbourhood of $`I` and
$`M_m(G)=\int_H(1+\|a\|)^{m+2}\max_{k\le m}\sup_{\omega\in I}|\partial_\omega^kG(\omega a)|\,\nu_\alpha(\mathrm da)<\infty`
for every integer $`m\ge0`. Such a $`G` belongs to $`L^1(\nu_\alpha)\cap L^2(\nu_\alpha)`
(the theorem part of the definition).
:::

:::lemma_ "lem:4.3" (lean := "OperatorRidgelet.Paper.lem_4_3_i, OperatorRidgelet.Paper.lem_4_3_ii, OperatorRidgelet.Paper.lem_4_3_iii, OperatorRidgelet.Paper.lem_4_3_iv, OperatorRidgelet.Paper.lem_4_3_v") (uses := "def:4.2, def:3.3, def:3.7")
Fix a band-pass $`\rho`, a symmetric compact frequency window $`I` away from zero, and an
integer $`r\ge0`. Let $`Y` be a separable complex Hilbert space and let $`G:H\to Y` be
bounded and Borel, with $`\omega\mapsto G(\omega a)` of class $`C^{r+2}` near $`I` for
every $`a`. Write
$`D_m(a)=\max_{k\le m}\sup_{\omega\in I}\|\partial_\omega^kG(\omega a)\|_Y` and
$`A_{m,r}(G)=\int_H(1+\|a\|)^rD_m(a)\,\nu_\alpha(\mathrm da)`.
If $`A_{r+2,r}(G)<\infty`, then $`G\in L^1(\nu_\alpha;Y)\cap L^2(\nu_\alpha;Y)`, and the
inverse Fourier integral is a jointly measurable representative $`\gamma_G` of $`W_\rho G`.
Moreover,
$`(1+|c|)^{r+2}\|\gamma_G(a,c)\|_Y\le C_{\rho,I,r}D_{r+2}(a)` and
$`\int_{H\times\mathbb R}(1+\|a\|+|c|)^r\|\gamma_G(a,c)\|_Y\,\mathrm d\lambda_\alpha\le c_{\rho,I,r}A_{r+2,r}(G)`.
The constants do not depend on $`G` or the dimension of $`Y`.
:::

:::proof "lem:4.3" (uses := "lem:3.8, lem:3.2")
Difference quotients and countable dense subsets of $`I` give measurability of $`D_m`.
Homogeneity at one fixed nonzero frequency gives $`G\in L^1`; boundedness gives $`G\in L^2`.
Set $`m=r+2` and $`h_a(\omega)=\rho^\sharp(\omega)G(-\omega a)`. Leibniz' rule bounds
$`\|h_a\|_1+\|h_a^{(m)}\|_1` by a filter-dependent constant times $`D_m(a)`. The function
$`h_a` is compactly supported and $`C^m`; the derivatives of the filter vanish at its support
boundary. Bound the inverse Fourier integral directly for $`|c|\le1`, and integrate by parts
$`m` times for $`|c|>1`. This proves the decay estimate. Finally use
$`1+\|a\|+|c|\le(1+\|a\|)(1+|c|)` and
$`\int_{\mathbb R}(1+|c|)^{-2}\,\mathrm dc=2` to obtain the moment bound by Tonelli.
No synthesis identity enters this argument.
:::

:::lemma_ "lem:4.4" (lean := "OperatorRidgelet.Paper.lem_4_4_a, OperatorRidgelet.Paper.lem_4_4_b_i, OperatorRidgelet.Paper.lem_4_4_b_ii, OperatorRidgelet.Paper.lem_4_4_c_i, OperatorRidgelet.Paper.lem_4_4_c_ii") (uses := "def:4.2")
The following functions satisfy {bpref "def:4.2"}[] for every band-pass $`\rho`.
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

:::proof "lem:4.4" (uses := "lem:3.12, lem:3.2")
For (a), domination of the linear functionals gives $`|q(\xi)|\le C(1+\kappa(\xi))^p`,
so $`G` is bounded. Derivatives of $`G_a(\omega)=G(\omega a)` with respect to $`\omega`
are polynomials times $`e^{-\omega^2\kappa(a)/2}`;
on $`I\subset\{r\le|\omega|\le R\}` their bound is
$`C_k(1+\|a\|)^{p_k}e^{-r^2\theta\langle Qa,a\rangle/2}`. Apply
{bpref "lem:3.12"}[]. For (b), derivatives vanish outside a bounded set of
directions, on which $`\nu_\alpha` is finite. For (c), the finite neighbourhood bounds
justify differentiation under the Bochner integral for each direction. The triangle
inequality and Tonelli give
$`M_m(G)\le m(\Omega)\int_H(1+\|a\|)^{m+2}\max_{k\le m}h_k(a)\,\nu_\alpha(\mathrm da)<\infty`.
:::

# Integral representation

:::definition "aux:tempered-activation" (lean := "OperatorRidgelet.IsTemperedFunction, OperatorRidgelet.temperedTestFilter, OperatorRidgelet.temperedAdmissibilityConst") (uses := "def:3.3, aux:conventions")
This is the activation and distributional-pairing setup for Theorem 4.5(iii).

A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` that is a continuous function of
polynomial growth is the pair of $`\beta` and a continuous $`b:\mathbb R\to\mathbb R` with
$`|b(t)|\le C(1+|t|)^p` and $`\langle\beta,\varphi\rangle=\int b\varphi`. For a band-pass
$`\rho` the test filter $`\omega\mapsto\rho^\sharp(-\omega)|\omega|^{-\alpha}` is a Schwartz
function, and the distributional admissibility constant is
$`C_{\beta,\rho}^{(\alpha)}=\frac1{2\pi}\langle\beta^\sharp,\rho^\sharp(-\,\cdot\,)|\cdot|^{-\alpha}\rangle`.
:::

:::theorem "thm:4.5" (lean := "OperatorRidgelet.Paper.thm_4_5_i_a, OperatorRidgelet.Paper.thm_4_5_i_b, OperatorRidgelet.Paper.thm_4_5_i_c, OperatorRidgelet.Paper.thm_4_5_ii_a, OperatorRidgelet.Paper.thm_4_5_ii_b, OperatorRidgelet.Paper.thm_4_5_ii_c, OperatorRidgelet.Paper.thm_4_5_iii_a, OperatorRidgelet.Paper.thm_4_5_iii_b, OperatorRidgelet.Paper.thm_4_5_iii_c, OperatorRidgelet.Paper.thm_4_5_iii_d, OperatorRidgelet.Paper.thm_4_5_iii_e") (uses := "def:4.2, aux:tempered-activation, def:3.7, def:2.2")
Let $`\alpha>0`. Part (ii) assumes an $`\alpha`-admissible Schwartz filter $`\rho`; part
(iii) assumes a band-pass filter. (i) For $`G\in L^1(\nu_\alpha)`, the function $`g_G` is
bounded with $`\|g_G\|_\infty\le\|G\|_{L^1(\nu_\alpha)}` and continuous,
and $`g_G=0` only if $`G=0` $`\nu_\alpha`-almost everywhere. (ii) For
$`G\in L^1(\nu_\alpha)\cap L^2(\nu_\alpha)` and every $`x`, the iterated integral
$`\int_H[\int_{\mathbb R}\gamma_G(a,c)\rho(\langle a,x\rangle+c)\,\mathrm dc]\,\nu_\alpha(\mathrm da)=(\!(\rho,\rho)\!)_\alpha g_G(x)`
converges absolutely, and if $`\gamma_G\in L^1(\lambda_\alpha)` its left side is the integral
network $`S_\rho[\gamma_G\lambda_\alpha](x)`. (iii) For a tempered $`\beta` that is a
continuous function of polynomial growth and $`G` satisfying {bpref "def:4.2"}[], the integrand
$`\gamma_G(a,c)\beta(\langle a,x\rangle+c)` is absolutely integrable on the product space.
Its integral is the ordinary network with finite coefficient measure $`\gamma_G\lambda_\alpha`
and equals $`C_{\beta,\rho}^{(\alpha)}g_G(x)`. This identity allows a zero constant.
Non-polynomiality is needed separately to choose a band-pass filter with a nonzero constant,
then normalize it for reconstruction or universality. A polynomial activation has zero
band-pass pairing.
:::

:::proof "thm:4.5" (uses := "lem:3.8, lem:4.1, lem:4.3, lem:3.2")
Part (i) is {bpref "lem:4.1"}[]. Parseval in the bias turns the inner
integral into a frequency integral of
$`\rho^\sharp(\omega)G(-\omega a)` against $`\rho^\sharp(-\omega)e^{-i\omega\langle a,x\rangle}`,
and the homogeneous substitution $`\xi=-\omega a` separates the admissibility constant from
$`g_G(x)`. For a tempered $`\beta` the bias integral is a distributional pairing with a test
function supported in $`-\operatorname{supp}\rho^\sharp`; {bpref "def:4.2"}[] makes
$`a\mapsto` (test function) Bochner integrable in a $`C^m` norm, so the pairing commutes with
the direction integral. Joint absolute integrability follows independently from
{bpref "lem:4.3"}[], choosing a moment at least as large as the
activation's polynomial growth order. If every band-pass test function paired to zero with
$`\beta^\sharp`, its support would be $`\{0\}` and $`\beta` a polynomial.
:::

# Synthesis, Hermite recovery, and reconstruction

:::definition "aux:frame-operator" (lean := "OperatorRidgelet.SpectralAntiDual, OperatorRidgelet.antiDualConj, OperatorRidgelet.rieszMap, OperatorRidgelet.rieszInv, OperatorRidgelet.transposeEmbed, OperatorRidgelet.frameOperator, OperatorRidgelet.ridgeletExtension, OperatorRidgelet.ridgeletRange, OperatorRidgelet.synthesis") (uses := "def:3.10, thm:3.14")
These are the anti-dual, transpose, and frame-operator definitions preceding Theorem 4.8 in Section 4.2.

Let $`\mathcal E_\alpha'` be the continuous anti-dual of $`\mathcal E_\alpha`, represented as
the continuous conjugate-linear functionals on $`\mathcal K_\alpha`. The Riesz map is
$`T_\alpha f[g]=\langle f,g\rangle_{\mathcal E_\alpha}`, with inverse $`T_\alpha^{-1}` from the
Riesz representation theorem; the transpose of $`F_Q` is
$`F_Q'F[g]=\langle F,F_Q g\rangle_{L^2(\nu_\alpha)}` for $`F\in L^2(\nu_\alpha)`, and
the frame operator is $`T_\alpha=F_Q'F_Q`. With $`R_\rho:\mathcal E_\alpha\to
L^2(\lambda_\alpha)` the bounded extension of {bpref "thm:3.14"}[] (ii) and
$`\operatorname{Ran}R_\rho` its range, synthesis with the analysis filter is the transpose
$`S_\rho=R_\rho'`, $`(S_\rho\gamma)[g]=\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}`.
Here $`F_Q':L^2(\nu_\alpha)\to\mathcal E_\alpha'` is formed from the
completed input space. The prime denotes transpose into the anti-dual,
while the star denotes the Hilbert adjoint. No adjoint into the ambient
$`L^2(\mu_Q)` is asserted. With $`C=(\!(\rho,\rho)\!)_\alpha`, the Plancherel identity gives
$`R_\rho^*R_\rho=C I_{\mathcal E_\alpha}` and
$`R_\rho'R_\rho=CT_\alpha`.
:::



:::lemma_ "lem:4.6" (lean := "OperatorRidgelet.Paper.lem_4_6_i, OperatorRidgelet.Paper.lem_4_6_ii") (uses := "def:2.2, def:3.4, def:3.10, aux:frame-operator")
Let $`\rho\in\mathcal S(\mathbb R)` be real and
$`\gamma\in L^1(\lambda_\alpha)\cap L^2(\lambda_\alpha)`. Then the integral network
$`S_\rho[\gamma\lambda_\alpha]` is a bounded Borel function on $`H` (i), and for every
$`g\in\mathcal D_\alpha`,
$`\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}=\int_HS_\rho[\gamma\lambda_\alpha](x)\,\overline{g(x)}\,\mu_Q(\mathrm dx)`
(ii), so the synthesis functional $`S_\rho\gamma` is the integral network paired with $`g`
through $`\mu_Q`.
:::

:::proof "lem:4.6"
$`|S_\rho[\gamma\lambda_\alpha]|\le\|\gamma\|_{L^1}\|\rho\|_\infty`, and the double integral
of $`|\gamma||g||\rho(\langle a,x\rangle+c)|` is at most
$`\|\gamma\|_{L^1}\|\rho\|_\infty\|g\|_{L^1(\mu_Q)}`, so Fubini applies; $`\rho` is real.
:::



:::lemma_ "lem:4.7" (lean := "OperatorRidgelet.Paper.lem_4_7_i, OperatorRidgelet.Paper.lem_4_7_ii, OperatorRidgelet.Paper.lem_4_7_iii, OperatorRidgelet.Paper.lem_4_7_iv, OperatorRidgelet.Paper.lem_4_7_v, OperatorRidgelet.Paper.lem_4_7_vi, OperatorRidgelet.gaussFourierLine, OperatorRidgelet.hermiteExtension, OperatorRidgelet.hermiteCoefficient, OperatorRidgelet.gaussFourierInv") (uses := "aux:centered-gaussian, def:3.4, def:3.10")
For $`f\in L^2(\mu_Q)`, $`\xi\ne0`, and $`\tau(\xi)=\langle Q\xi,\xi\rangle^{1/2}`, the
analytic continuation $`z\mapsto F_Qf(z\xi)=\int_Hf(x)e^{-iz\langle x,\xi\rangle}\mu_Q(\mathrm dx)`
and the entire function $`G_f(z\xi)=e^{z^2\tau(\xi)^2/2}F_Qf(z\xi)`; the Hermite
coefficients $`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]` with the
probabilists' Hermite polynomials; and $`\Delta_Q`, the inverse of $`F_Q` on its
range on $`\mathcal D_\alpha`, chosen as the element of $`\mathcal D_\alpha` with the given
transform.

For $`f\in L^2(\mu_Q)` and $`\xi\ne0`, the function $`z\mapsto G_f(z\xi)` is entire (i),
$`G_f(z\xi)=\sum_{n\ge0}\frac{(-iz\tau(\xi))^n}{n!}\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]`
(ii) with locally uniform convergence (iii),
$`|G_f(z\xi)|\le\|f\|_{L^2(\mu_Q)}e^{|z|^2\tau(\xi)^2/2}` (iv), and the Hermite inversion
formula
$`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]=\frac{i^n}{\tau(\xi)^n}\frac{\mathrm d^n}{\mathrm dt^n}\bigl(e^{t^2\tau(\xi)^2/2}F_Qf(t\xi)\bigr)\big|_{t=0}`
holds (v). The coefficients, over all $`\xi\ne0` and $`n`, determine $`f` in $`L^2(\mu_Q)`
(vi).
:::

:::proof "lem:4.7"
The generating function $`e^{tZ-t^2/2}=\sum_n\mathrm{He}_n(Z)t^n/n!` of a standard normal
$`Z` converges in $`L^2` locally uniformly in $`t\in\mathbb C`; pairing with $`f` gives the
series, the bound, and termwise differentiation. For totality, finite products of Hermite
polynomials in independent coordinates form a complete orthogonal system (the Wiener–Itô chaos
decomposition), and polarization of Wick powers expresses them through the directional Wick
powers.
:::

:::theorem "thm:4.8" (lean := "OperatorRidgelet.Paper.thm_4_8_i_a, OperatorRidgelet.Paper.thm_4_8_i_b, OperatorRidgelet.Paper.thm_4_8_i_c, OperatorRidgelet.Paper.thm_4_8_i_d, OperatorRidgelet.Paper.thm_4_8_ii_a, OperatorRidgelet.Paper.thm_4_8_ii_b, OperatorRidgelet.Paper.thm_4_8_iii_a, OperatorRidgelet.Paper.thm_4_8_iii_b, OperatorRidgelet.Paper.thm_4_8_iii_c, OperatorRidgelet.Paper.thm_4_8_iii_d, OperatorRidgelet.Paper.thm_4_8_iii_e, OperatorRidgelet.Paper.thm_4_8_iv_a, OperatorRidgelet.Paper.thm_4_8_iv_b, OperatorRidgelet.Paper.thm_4_8_iv_c, OperatorRidgelet.Paper.thm_4_8_iv_d, OperatorRidgelet.Paper.thm_4_8_iv_e, OperatorRidgelet.Paper.thm_4_8_iv_f, OperatorRidgelet.Paper.thm_4_8_iv_completion") (uses := "aux:frame-operator, lem:3.9, lem:4.7, def:4.2")
Let $`\alpha>0` and let $`\rho` be an $`\alpha`-admissible Schwartz filter. (i) The frame operator
$`T_\alpha=F_Q'F_Q` is the Riesz map, an isometric bijection
$`\mathcal E_\alpha\to\mathcal E_\alpha'`, and $`S_\rho R_\rho f=(\!(\rho,\rho)\!)_\alpha T_\alpha f`
for $`f\in\mathcal E_\alpha`. (ii) For $`f\in\mathcal E_\alpha` and $`g\in\mathcal E_\alpha'`,
$`f=((\!(\rho,\rho)\!)_\alpha)^{-1}T_\alpha^{-1}S_\rho R_\rho f` and
$`g=((\!(\rho,\rho)\!)_\alpha)^{-1}S_\rho(R_\rho T_\alpha^{-1}g)`. (iii) If $`f\in\mathcal D_\alpha`
and $`F_Qf\in L^1(\nu_\alpha)`, then $`T_\alpha f` is represented by
$`g_{F_Qf}` against $`\mu_Q`; conversely, for $`G\in\mathcal K_\alpha`,
$`R_\rho T_\alpha^{-1}F_Q'G=W_\rho G`, and when $`G\in L^1(\nu_\alpha)`, $`F_Q'G` is
represented by $`g_G` and the second reconstruction formula is the spectral synthesis identity
of {bpref "thm:4.5"}[] (ii). (iv) The backprojection $`W_\rho^*` is a bounded operator
$`L^2(\lambda_\alpha)\to L^2(\nu_\alpha)` with $`W_\rho^* W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}`,
and $`W_\rho^* R_\rho f=(\!(\rho,\rho)\!)_\alpha F_Q f` holds in $`L^2(\nu_\alpha)` for
every $`f\in\mathcal E_\alpha`. For an input $`f\in\mathcal D_\alpha`, choose the Gaussian integral
as the representative of $`F_Qf`. The identity then holds pointwise with
the continuous Fourier-slice representative.
The remaining inversion step uses Gaussian input: the Hermite formula at $`\xi\ne0`
recovers the Hermite coefficients of $`f` from $`F_Qf`, these coefficients determine
$`f` in $`L^2(\mu_Q)`, and $`f=\Delta_Q[((\!(\rho,\rho)\!)_\alpha)^{-1}W_\rho^* R_\rho f]`.
:::

:::proof "thm:4.8" (uses := "thm:3.14, lem:3.11, lem:3.5, lem:3.2, lem:4.6, lem:4.7")
Since $`F_Q` is unitary onto $`\mathcal K_\alpha`,
$`F_Q'F_Q f[g]=\langle F_Q f,F_Q g\rangle=\langle f,g\rangle_{\mathcal E_\alpha}`,
the Riesz representation theorem makes $`T_\alpha` an isometric bijection, and the Plancherel
identity gives $`(S_\rho R_\rho f)[g]=\langle R_\rho f,R_\rho g\rangle=(\!(\rho,\rho)\!)_\alpha T_\alpha f[g]`;
(ii) follows by applying $`T_\alpha^{-1}` or substituting $`f=T_\alpha^{-1}g`.
For (iii), $`|G(\xi)||v(x)|` is integrable against $`\nu_\alpha\otimes\mu_Q`
when $`G\in L^1(\nu_\alpha)` and $`v\in\mathcal D_\alpha`, so Fubini identifies
$`F_Q'G` with the functional represented by $`g_G`. For
$`u=T_\alpha^{-1}F_Q'G`, unitarity gives $`F_Q u=G`, hence $`R_\rho u=W_\rho G`.
When also $`\gamma_G\in L^1(\lambda_\alpha)`, {bpref "lem:4.6"}[] identifies weak
synthesis with the ordinary network integral. Part (iv) first uses $`W_\rho^* W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}` from
{bpref "lem:3.9"}[] and $`R_\rho=W_\rho F_Q` on the completion.
The pointwise core formula uses the continuous Fourier-slice representative; only the final
Hermite inversion invokes {bpref "lem:4.7"}[] and Gaussian input.
:::

:::corollary "cor:4.9" (lean := "OperatorRidgelet.Paper.cor_4_9_i, OperatorRidgelet.Paper.cor_4_9_ii, OperatorRidgelet.Paper.cor_4_9_iii, OperatorRidgelet.Paper.cor_4_9_iv") (uses := "aux:frame-operator")
Let $`\rho` be $`\alpha`-admissible, put $`C=(\!(\rho,\rho)\!)_\alpha>0`, and define
$`D_\rho=C^{-1}T_\alpha^{-1}S_\rho`. Then $`D_\rho R_\rho=\mathrm{Id}` and
$`\|D_\rho\|\le C^{-1/2}`. If $`f\in\mathcal E_\alpha`,
$`\gamma_\delta\in L^2(\lambda_\alpha)`, and $`\|\gamma_\delta-R_\rho f\|_2\le\delta`, then
$`\|D_\rho\gamma_\delta-f\|_{\mathcal E_\alpha}\le\delta/\sqrt C`.
This is an estimate in the completion norm, not an ambient $`L^2(\mu_Q)` or pointwise estimate.
:::

:::proof "cor:4.9" (uses := "thm:4.8, lem:3.8")
The left-inverse identity is {bpref "thm:4.8"}[] (ii). Since the transpose $`S_\rho` has norm
at most $`\sqrt C` and $`T_\alpha^{-1}` is an isometry, the decoder has norm at most
$`C^{-1}\sqrt C=C^{-1/2}`. Apply this bound to $`\gamma_\delta-R_\rho f`.
:::

*Remark 4.10 (Which inverse is bounded).*

The inverse $`T_\alpha^{-1}:\mathcal E_\alpha'\to\mathcal E_\alpha` is bounded
with norm one. This is the Hilbert-space norm of the construction; no bounded inverse in
the ambient $`L^2(\mu_Q)` norm is asserted. On the core, inversion factors through
$`F_Qf`, Fourier uniqueness of $`f\mu_Q`, and the Radon–Nikodym derivative. The Hermite
expansion makes the last two steps constructive.

# Vector-valued targets

:::definition "aux:vector-valued" (lean := "OperatorRidgelet.gaussFourierVec, OperatorRidgelet.ridgeletVec, OperatorRidgelet.coefficientFormulaVec, OperatorRidgelet.biasFourierVec, OperatorRidgelet.HasBiasFourierVec, OperatorRidgelet.spectralCoefficientVec, OperatorRidgelet.spectralInnerVec, OperatorRidgelet.spectralCoreVec, OperatorRidgelet.gaussFourierLpVec, OperatorRidgelet.spectralRangeVec, OperatorRidgelet.spectralEmbedVec, OperatorRidgelet.ridgeletExtensionVec, OperatorRidgelet.ridgeletRangeVec, OperatorRidgelet.SpectralAntiDualVec, OperatorRidgelet.rieszMapVec, OperatorRidgelet.rieszInvVec, OperatorRidgelet.transposeEmbedVec, OperatorRidgelet.frameOperatorVec, OperatorRidgelet.synthesisVec, OperatorRidgelet.backprojectionOfVec, OperatorRidgelet.backprojectionVec, OperatorRidgelet.backprojectionLpVec, OperatorRidgelet.coefficientProjectionVec, OperatorRidgelet.gaussFourierLineVec, OperatorRidgelet.hermiteExtensionVec, OperatorRidgelet.hermiteCoefficientVec, OperatorRidgelet.gaussFourierInvVec") (uses := "def:3.4, def:3.7, def:3.10, aux:frame-operator, lem:3.9, lem:4.7")
These are the vector-valued objects introduced for Theorem 4.11 in Section 4.3.

Let $`Y` be a separable complex Hilbert space. All objects above have $`Y`-valued versions:
$`L^2(\mu_Q;Y)`, the Bochner integral
$`F_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\mu_Q(\mathrm dx)\in Y`, the core
$`\mathcal D_\alpha(Y)`, the completion $`\mathcal E_\alpha(Y)` with inner product
$`\int\langle F_Qf,F_Qg\rangle_Y\mathrm d\nu_\alpha`, the transform
$`R_\rho f\in L^2(\lambda_\alpha;Y)`, the coefficient $`W_\rho G` of a density
$`G\in L^2(\nu_\alpha;Y)`, the anti-dual, Riesz map, frame and synthesis operators, the
backprojection, and the Hermite extension. The target $`g_G` and the condition in
{bpref "def:4.2"}[] are
already polymorphic in the target.
:::

:::theorem "thm:4.11" (lean := "OperatorRidgelet.Paper.thm_4_11_representation_i_a, OperatorRidgelet.Paper.thm_4_11_representation_i_b, OperatorRidgelet.Paper.thm_4_11_representation_i_c, OperatorRidgelet.Paper.thm_4_11_representation_ii_a, OperatorRidgelet.Paper.thm_4_11_representation_ii_b, OperatorRidgelet.Paper.thm_4_11_representation_ii_c, OperatorRidgelet.Paper.thm_4_11_representation_iii_a, OperatorRidgelet.Paper.thm_4_11_representation_iii_b, OperatorRidgelet.Paper.thm_4_11_representation_iii_c, OperatorRidgelet.Paper.thm_4_11_plancherel_i_a, OperatorRidgelet.Paper.thm_4_11_plancherel_i_b, OperatorRidgelet.Paper.thm_4_11_plancherel_ii_a, OperatorRidgelet.Paper.thm_4_11_plancherel_ii_b, OperatorRidgelet.Paper.thm_4_11_plancherel_ii_c, OperatorRidgelet.Paper.thm_4_11_plancherel_ii_d, OperatorRidgelet.Paper.thm_4_11_plancherel_iii, OperatorRidgelet.Paper.thm_4_11_frame_i_a, OperatorRidgelet.Paper.thm_4_11_frame_i_b, OperatorRidgelet.Paper.thm_4_11_frame_i_c, OperatorRidgelet.Paper.thm_4_11_frame_i_d, OperatorRidgelet.Paper.thm_4_11_frame_ii_a, OperatorRidgelet.Paper.thm_4_11_frame_ii_b, OperatorRidgelet.Paper.thm_4_11_frame_iii_a, OperatorRidgelet.Paper.thm_4_11_frame_iii_b, OperatorRidgelet.Paper.thm_4_11_frame_iii_c, OperatorRidgelet.Paper.thm_4_11_frame_iii_d, OperatorRidgelet.Paper.thm_4_11_frame_iii_e, OperatorRidgelet.Paper.thm_4_11_frame_iv_a, OperatorRidgelet.Paper.thm_4_11_frame_iv_b, OperatorRidgelet.Paper.thm_4_11_frame_iv_c, OperatorRidgelet.Paper.thm_4_11_frame_iv_d, OperatorRidgelet.Paper.thm_4_11_frame_iv_e, OperatorRidgelet.Paper.thm_4_11_frame_iv_f, OperatorRidgelet.Paper.thm_4_11_representation_iii_e, OperatorRidgelet.Paper.thm_4_11_frame_iv_completion") (uses := "aux:vector-valued, thm:4.5, thm:3.14, thm:4.8")
{bpref "thm:4.5"}[], {bpref "thm:3.14"}[], and {bpref "thm:4.8"}[] hold for $`Y`-valued targets,
with the same constants, with absolute values replaced by norms in $`Y`, scalar integrals by
Bochner integrals, and $`L^2` spaces by their $`Y`-valued counterparts. The Riesz map and its
inverse are isometries; their operator norms are one for $`Y\ne\{0\}` and zero for
$`Y=\{0\}`. The $`L^1` input injectivity statement, admissible Schwartz synthesis and frame
identities, completed $`L^2` backprojection, and jointly absolutely integrable tempered
synthesis all retain the corresponding scalar assumptions. The Lean statements
are one theorem per part of the three scalar theorems, with general input and
homogeneous direction measures where appropriate; the scalar existence claim of
{bpref "thm:4.5"}[] (iii)
is not repeated.
:::

:::proof "thm:4.11" (uses := "lem:3.6, lem:4.1, lem:4.3, lem:3.9")
Use {bpref "lem:3.6"}[] for jointly measurable Fourier representatives and
Hilbert-valued Plancherel, {bpref "lem:4.1"}[] for spectral synthesis and
uniqueness, and {bpref "lem:4.3"}[] for coefficient moments and joint
absolute integrability. The vector adjoint identity and integral formula are
{bpref "lem:3.9"}[]. These common lemmas justify the Fubini and Parseval
steps with the same constants. Completing the vector core and applying Riesz representation
proves the frame and reconstruction statements; the Gaussian Hermite expansion is applied
componentwise. If $`Y\ne\{0\}`, a nonzero constant vector belongs to the Gaussian core by
{bpref "lem:3.12"}[], so its Riesz isometries have norm one; when $`Y=\{0\}`, both
spaces and norms are zero. The integral representation with a continuous activation of
polynomial growth uses the fixed-support $`C^m` Bochner argument and the distributional
pairing tensored with the identity of $`Y`.
:::
