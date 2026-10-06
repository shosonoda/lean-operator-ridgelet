import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Reconstruction
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

#doc (Manual) "Appendix B. Proofs for Section 4" =>
%%%
file := "appendix-b"
number := false
%%%

The coefficient isometry and elementary properties of spectral targets are followed by
finite-order decay estimates. These estimates justify synthesis before any interchange of
integrals is made. The frame-operator proof uses Hermite totality, and the final subsection
identifies the coefficient projection and minimum-norm synthesis coefficient.

:::lemma_ "lem:B.1" (lean := "OperatorRidgelet.Paper.lem_B_1_i, OperatorRidgelet.Paper.lem_B_1_ii, OperatorRidgelet.Paper.lem_B_1_iii, OperatorRidgelet.Paper.lem_B_1_iv, OperatorRidgelet.Paper.def_3_5, OperatorRidgelet.Paper.lem_B_1_v") (uses := "def:3.5")
$`W_\rho:L^2(\nu_\alpha)\to L^2(\lambda_\alpha)` is well defined (i), independent of the Borel
representative of $`G` (ii), and
$`\|W_\rho G\|_{L^2(\lambda_\alpha)}^2=(\!(\rho,\rho)\!)_\alpha\|G\|_{L^2(\nu_\alpha)}^2` (iii). If
$`G\in L^1(\nu_\alpha)`, then $`\omega\mapsto G(-\omega a)` is integrable on compact subsets of
$`\mathbb R\setminus\{0\}` for $`\nu_\alpha`-almost every $`a` (iv), and the explicit formula
for $`\gamma_G` holds already for $`G\in L^2(\nu_\alpha)`, with absolute convergence on
almost every $`a` and every bias. In this notation the Fourier-slice identity reads
$`R_\rho f=W_\rho\,F_Qf`.
:::

:::proof "lem:B.1" (uses := "lem:3.1")
$`(a,\omega)\mapsto G(-\omega a)` is Borel, and the homogeneous change of variables with
Tonelli gives
$`\frac1{2\pi}\int\int|\rho^\sharp(\omega)|^2|G(-\omega a)|^2\,\nu_\alpha(\mathrm da)\,\mathrm d\omega=(\!(\rho,\rho)\!)_\alpha\|G\|^2_{L^2(\nu_\alpha)}`;
the same computation with $`|G|` on a compact set gives local integrability, and the inverse
Fourier transform in $`\omega` for almost every $`a` gives the formula.
:::

:::lemma_ "lem:B.2" (lean := "OperatorRidgelet.Paper.lem_B_2_i, OperatorRidgelet.Paper.lem_B_2_ii, OperatorRidgelet.Paper.lem_B_2_iii") (uses := "aux:conventions")
Let $`\nu` be a Borel measure on $`H`, let $`Y` be a separable complex Hilbert
space, and let $`G\in L^1(\nu;Y)`. Then
$`g_G(x)=\int_H e^{i\langle x,\xi\rangle}G(\xi)\,\nu(\mathrm d\xi)` belongs to
$`C_b(H;Y)`, satisfies $`\|g_G\|_\infty\le\|G\|_{L^1(\nu;Y)}`, and determines $`G` up to
$`\nu`-almost-everywhere equality. No input weight, filter, homogeneity, or full-support
assumption is needed.
:::

:::proof "lem:B.2"
The integral triangle inequality gives the norm bound, and dominated convergence with
majorant $`\|G(\xi)\|_Y` gives continuity. If $`g_G=0`, pair the finite vector measure
$`G\nu` with vectors in a countable dense subset of $`Y`. Fourier uniqueness makes each
resulting scalar measure zero: finite-dimensional Fourier uniqueness determines all cylinder
sets, which generate the Borel sigma-algebra of $`H`. Intersect the countably many
full-measure sets and use continuity of the pairing to obtain $`G=0` almost everywhere.
Apply the argument to a difference for uniqueness.
:::

# B.1 Coefficient decay before synthesis
%%%
number := false
%%%

:::lemma_ "lem:B.3" (lean := "OperatorRidgelet.Paper.lem_B_3_i, OperatorRidgelet.Paper.lem_B_3_ii, OperatorRidgelet.Paper.lem_B_3_iii, OperatorRidgelet.Paper.lem_B_3_iv, OperatorRidgelet.Paper.lem_B_3_v") (uses := "def:4.1, def:3.2, def:3.5")
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

:::proof "lem:B.3" (uses := "lem:B.1, lem:3.1")
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

# B.2 Proof of Theorem 4.2
%%%
number := false
%%%

We prove {bpref "thm:4.2"}[].

:::proof "thm:4.2" (uses := "lem:B.1, lem:B.2, lem:B.3, lem:3.1")
Part (i) is {bpref "lem:B.2"}[]. Parseval in the bias turns the inner
integral into a frequency integral of
$`\rho^\sharp(\omega)G(-\omega a)` against $`\rho^\sharp(-\omega)e^{-i\omega\langle a,x\rangle}`,
and the homogeneous substitution $`\xi=-\omega a` separates the admissibility constant from
$`g_G(x)`. For a tempered $`\beta` the bias integral is a distributional pairing with a test
function supported in $`-\operatorname{supp}\rho^\sharp`; {bpref "def:4.1"}[] makes
$`a\mapsto` (test function) Bochner integrable in a $`C^m` norm, so the pairing commutes with
the direction integral. Joint absolute integrability follows independently from
{bpref "lem:B.3"}[], choosing a moment at least as large as the
activation's polynomial growth order. If every band-pass test function paired to zero with
$`\beta^\sharp`, its support would be $`\{0\}` and $`\beta` a polynomial.
:::

# B.3 The synthesis operator on integrable coefficients
%%%
number := false
%%%

:::lemma_ "lem:B.4" (lean := "OperatorRidgelet.Paper.lem_B_4_i, OperatorRidgelet.Paper.lem_B_4_ii") (uses := "def:2.2, def:3.3, def:3.7, aux:frame-operator")
Let $`\rho\in\mathcal S(\mathbb R)` be real and
$`\gamma\in L^1(\lambda_\alpha)\cap L^2(\lambda_\alpha)`. Then the integral network
$`S_\rho[\gamma\lambda_\alpha]` is a bounded Borel function on $`H` (i), and for every
$`g\in\mathcal D_\alpha`,
$`\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}=\int_HS_\rho[\gamma\lambda_\alpha](x)\,\overline{g(x)}\,\mu_Q(\mathrm dx)`
(ii), so the synthesis functional $`S_\rho\gamma` is the integral network paired with $`g`
through $`\mu_Q`.
:::

:::proof "lem:B.4"
$`|S_\rho[\gamma\lambda_\alpha]|\le\|\gamma\|_{L^1}\|\rho\|_\infty`, and the double integral
of $`|\gamma||g||\rho(\langle a,x\rangle+c)|` is at most
$`\|\gamma\|_{L^1}\|\rho\|_\infty\|g\|_{L^1(\mu_Q)}`, so Fubini applies; $`\rho` is real.
:::

# B.4 Proof of Theorem 4.3(iii) and (iv)
%%%
number := false
%%%

We prove {bpref "thm:4.3"}[].

:::proof "thm:4.3" (uses := "thm:3.11, lem:3.8, lem:3.4, lem:3.1, lem:B.4, lem:B.5, prop:B.8")
Since $`F_Q` is unitary onto $`\mathcal K_\alpha`,
$`F_Q'F_Q f[g]=\langle F_Q f,F_Q g\rangle=\langle f,g\rangle_{\mathcal E_\alpha}`,
the Riesz representation theorem makes $`T_\alpha` an isometric bijection, and the Plancherel
identity gives $`(S_\rho R_\rho f)[g]=\langle R_\rho f,R_\rho g\rangle=(\!(\rho,\rho)\!)_\alpha T_\alpha f[g]`;
(ii) follows by applying $`T_\alpha^{-1}` or substituting $`f=T_\alpha^{-1}g`. Part (iii) is a
Fubini computation with $`u=T_\alpha^{-1}F_Q'G` and {bpref "lem:B.4"}[],
and (iv) first uses $`W_\rho^* W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}` from
{bpref "lem:3.6"}[] and $`R_\rho=W_\rho F_Q` on the completion.
The pointwise core formula uses the continuous Fourier-slice representative; only the final
Hermite inversion invokes {bpref "lem:B.5"}[] and Gaussian input.
:::

:::definition "aux:hermite" (lean := "OperatorRidgelet.gaussFourierLine, OperatorRidgelet.hermiteExtension, OperatorRidgelet.hermiteCoefficient, OperatorRidgelet.gaussFourierInv") (uses := "aux:centered-gaussian, def:3.3, def:3.7")
For $`f\in L^2(\mu_Q)`, $`\xi\ne0`, and $`\tau(\xi)=\langle Q\xi,\xi\rangle^{1/2}`, the
analytic continuation $`z\mapsto F_Qf(z\xi)=\int_Hf(x)e^{-iz\langle x,\xi\rangle}\mu_Q(\mathrm dx)`
and the entire function $`G_f(z\xi)=e^{z^2\tau(\xi)^2/2}F_Qf(z\xi)`; the Hermite
coefficients $`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]` with the
probabilists' Hermite polynomials; and $`\Delta_Q`, the inverse of $`F_Q` on its
range on $`\mathcal D_\alpha`, chosen as the element of $`\mathcal D_\alpha` with the given
transform.
:::

:::lemma_ "lem:B.5" (lean := "OperatorRidgelet.Paper.lem_B_5_i, OperatorRidgelet.Paper.lem_B_5_ii, OperatorRidgelet.Paper.lem_B_5_iii, OperatorRidgelet.Paper.lem_B_5_iv, OperatorRidgelet.Paper.lem_B_5_v, OperatorRidgelet.Paper.lem_B_5_vi") (uses := "aux:hermite, aux:centered-gaussian")
For $`f\in L^2(\mu_Q)` and $`\xi\ne0`, the function $`z\mapsto G_f(z\xi)` is entire (i),
$`G_f(z\xi)=\sum_{n\ge0}\frac{(-iz\tau(\xi))^n}{n!}\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]`
(ii) with locally uniform convergence (iii),
$`|G_f(z\xi)|\le\|f\|_{L^2(\mu_Q)}e^{|z|^2\tau(\xi)^2/2}` (iv), and the Hermite inversion
formula
$`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]=\frac{i^n}{\tau(\xi)^n}\frac{\mathrm d^n}{\mathrm dt^n}\bigl(e^{t^2\tau(\xi)^2/2}F_Qf(t\xi)\bigr)\big|_{t=0}`
holds (v). The coefficients, over all $`\xi\ne0` and $`n`, determine $`f` in $`L^2(\mu_Q)`
(vi).
:::

:::proof "lem:B.5"
The generating function $`e^{tY-t^2/2}=\sum_n\mathrm{He}_n(Y)t^n/n!` of a standard normal
$`Y` converges in $`L^2` locally uniformly in $`t\in\mathbb C`; pairing with $`f` gives the
series, the bound, and termwise differentiation. For totality, finite products of Hermite
polynomials in independent coordinates form a complete orthogonal system (the Wiener–Itô chaos
decomposition), and polarization of Wick powers expresses them through the directional Wick
powers.
:::

*Remark B.6 (A Riesz-type kernel for the frame operator).*

The regularized characteristic functional in {bpref "lem:A.3"}[] suggests
the kernel $`\Gamma(\alpha/2)\langle P(x-y),x-y\rangle^{-\alpha/2}` for the frame
operator. This is only a formal interchange against an infinite oscillatory measure and is
not used as an identity. In finite dimension, with $`P=I` and $`0<\alpha<m`, it agrees
with the Riesz-potential interpretation of {bpref "cor:F.2"}[].

*Remark B.7 (Range of the analysis operator).*

The closed range is $`R_\rho\mathcal E_\alpha=W_\rho\mathcal K_\alpha`, which is
contained in the closed space $`W_\rho L^2(\nu_\alpha)`. Their orthogonal projections
are respectively $`C^{-1}W_\rho P_{\mathcal K_\alpha}W_\rho^*` and
$`C^{-1}W_\rho W_\rho^*`. Retaining the closed spectral subspace distinguishes
coefficients obtained by analysis from arbitrary synthesis coefficients. The next result
also identifies the minimum-norm coefficient and the kernel of synthesis.

# B.5 Coefficient projection
%%%
number := false
%%%

:::proposition "prop:B.8" (lean := "OperatorRidgelet.Paper.prop_B_8_i, OperatorRidgelet.Paper.prop_B_8_ii, OperatorRidgelet.Paper.prop_B_8_iii, OperatorRidgelet.Paper.prop_B_8_iv, OperatorRidgelet.Paper.prop_B_8_v, OperatorRidgelet.Paper.prop_B_8_vi, OperatorRidgelet.Paper.prop_B_8_vii, OperatorRidgelet.Paper.prop_B_8_viii") (uses := "aux:backprojection, aux:frame-operator")
Let $`\rho` be $`\alpha`-admissible with $`C=(\!(\rho,\rho)\!)_\alpha` and
$`\mathcal Y=L^2(\lambda_\alpha)`. The integral defining $`W_\rho^*\gamma`
converges absolutely for $`\nu_\alpha`-almost every $`\xi` (i), is independent as an $`L^2`
class of the jointly measurable Fourier representative (ii), and satisfies
$`\|W_\rho^*\gamma\|_{L^2(\nu_\alpha)}\le\sqrt C\|\gamma\|_{\mathcal Y}` (iii);
$`W_\rho^*` is the Hilbert adjoint of $`W_\rho` (iv) and $`W_\rho^* W_\rho=C\,\mathrm{Id}`
(v). The operator $`C^{-1}W_\rho W_\rho^*` projects onto $`W_\rho L^2(\nu_\alpha)`.
The operator $`\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}W_\rho^*` is the orthogonal
projection onto $`\operatorname{Ran}R_\rho` (vi), the minimum-norm solution of
$`S_\rho\gamma=F\in\mathcal E_\alpha'` is $`C^{-1}R_\rho T_\alpha^{-1}F` (vii), and all
solutions differ from it by an element of $`(\operatorname{Ran}R_\rho)^\perp` (viii).
:::

:::proof "prop:B.8" (uses := "lem:B.1, lem:3.1, thm:3.11")
The change of variables $`\xi=-\omega a` gives
$`\frac1{2\pi}\int\int|\omega|^{-\alpha}|\gamma^\sharp(-\xi/\omega,\omega)|^2\mathrm d\omega\,\nu_\alpha(\mathrm d\xi)=\|\gamma\|_{\mathcal Y}^2`,
and weighted Cauchy–Schwarz in $`\omega` proves absolute convergence, representative
independence, the bound, and the adjoint identity. Since $`R_\rho=W_\rho F_Q` with
$`F_Q` unitary onto $`\mathcal K_\alpha`, $`C^{-1/2}W_\rho|_{\mathcal K_\alpha}` is an
isometry with closed image, and $`R_\rho'R_\rho=CT_\alpha` (the frame identity, which is the
Plancherel identity read through the transpose) identifies the kernel of $`R_\rho'` with
$`(\operatorname{Ran}R_\rho)^\perp`.
:::
