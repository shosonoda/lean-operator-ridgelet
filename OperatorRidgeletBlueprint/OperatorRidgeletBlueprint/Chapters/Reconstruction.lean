import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Reconstruction
import OperatorRidgelet.Paper.Revision

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Representation and reconstruction" =>
%%%
file := "reconstruction"
%%%

This chapter is Section 4 of the manuscript together with Appendix B. The Fourier-slice
identity, read backwards, produces a network from a spectral density
({bpref "thm:A"}[]); the transpose of the transform is the synthesis operator, and the frame
operator $`T_\alpha=U_\alpha'U_\alpha` is the Riesz map of $`\mathcal E_\alpha`
({bpref "thm:C"}[]). The Lean statements are for the abstract pair $`(\mu,\nu)` of Appendix H
wherever the manuscript allows it; the Hermite inversion needs the Gaussian input measure.

# Targets with a spectral density

:::lemma_ "lem:spectral-target-basic" (lean := "OperatorRidgelet.Paper.lem_spectral_target_basic_i, OperatorRidgelet.Paper.lem_spectral_target_basic_ii, OperatorRidgelet.Paper.lem_spectral_target_basic_iii") (uses := "aux:conventions")
Let $`\nu` be a Borel measure on $`H`, let $`Y` be a separable complex Hilbert
space, and let $`G\in L^1(\nu;Y)`. Then
$`g_G(x)=\int_H e^{i\langle x,\xi\rangle}G(\xi)\,\nu(\mathrm d\xi)` belongs to
$`C_b(H;Y)`, satisfies $`\|g_G\|_\infty\le\|G\|_{L^1(\nu;Y)}`, and determines $`G` up to
$`\nu`-almost-everywhere equality. No input weight, filter, homogeneity, or full-support
assumption is needed.
:::

:::proof "lem:spectral-target-basic"
The integral triangle inequality gives the norm bound, and dominated convergence with
majorant $`\|G(\xi)\|_Y` gives continuity. If $`g_G=0`, pair the finite vector measure
$`G\nu` with vectors in a countable dense subset of $`Y`. Fourier uniqueness makes each
resulting scalar measure zero: finite-dimensional Fourier uniqueness determines all cylinder
sets, which generate the Borel sigma-algebra of $`H`. Intersect the countably many
full-measure sets and use continuity of the pairing to obtain $`G=0` almost everywhere.
Apply the argument to a difference for uniqueness.
:::

The coefficient operator $`W_\rho G` and its almost-everywhere absolutely convergent inverse
Fourier formula require only $`G\in L^2(\nu_\alpha)`
({bpref "lem:coefficient-isometry"}[]). The additional $`L^1` assumption below defines the
continuous spectral target and justifies its synthesis.

:::definition "def:ray-regular" (lean := "OperatorRidgelet.IsFrequencyWindow, OperatorRidgelet.rayDerivBound, OperatorRidgelet.rayMoment, OperatorRidgelet.IsRegularAlongRays, OperatorRidgelet.spectralTarget, OperatorRidgelet.Paper.def_ray_regular") (uses := "def:admissible-filter, aux:gaussian-mixture, lem:homogeneous-mixture")
Fix a symmetric compact set
$`I\subset\mathbb R\setminus\{0\}` containing $`\operatorname{supp}\widehat\rho` (a frequency
window). A bounded Borel $`G:H\to\mathbb C` is regular along rays if for every $`a\in H` the
function $`\omega\mapsto G(\omega a)` is $`C^\infty` on a neighbourhood of $`I` and
$`M_m(G)=\int_H(1+\|a\|)^{m+2}\max_{k\le m}\sup_{\omega\in I}|\partial_\omega^kG(\omega a)|\,\nu_\alpha(\mathrm da)<\infty`
for every integer $`m\ge0`. Such a $`G` belongs to $`L^1(\nu_\alpha)\cap L^2(\nu_\alpha)`
(the theorem part of the definition).
:::

:::lemma_ "lem:coefficient-finite-order" (lean := "OperatorRidgelet.Paper.lem_coefficient_finite_order_i, OperatorRidgelet.Paper.lem_coefficient_finite_order_ii, OperatorRidgelet.Paper.lem_coefficient_finite_order_iii, OperatorRidgelet.Paper.lem_coefficient_finite_order_iv, OperatorRidgelet.Paper.lem_coefficient_finite_order_v") (uses := "def:ray-regular, def:admissible-filter, def:spectral-coefficient, lem:coefficient-isometry, lem:homogeneous-mixture")
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

:::proof "lem:coefficient-finite-order"
Difference quotients and countable dense subsets of $`I` give measurability of $`D_m`.
Homogeneity at one fixed nonzero frequency gives $`G\in L^1`; boundedness gives $`G\in L^2`.
Set $`m=r+2` and $`h_a(\omega)=\widehat\rho(\omega)G(-\omega a)`. Leibniz' rule bounds
$`\|h_a\|_1+\|h_a^{(m)}\|_1` by a filter-dependent constant times $`D_m(a)`. The function
$`h_a` is compactly supported and $`C^m`; the derivatives of the filter vanish at its support
boundary. Bound the inverse Fourier integral directly for $`|c|\le1`, and integrate by parts
$`m` times for $`|c|>1`. This proves the decay estimate. Finally use
$`1+\|a\|+|c|\le(1+\|a\|)(1+|c|)` and
$`\int_{\mathbb R}(1+|c|)^{-2}\,\mathrm dc=2` to obtain the moment bound by Tonelli.
No synthesis identity enters this argument.
:::

This is the coefficient estimate placed before the representation proof in Appendix B.
In particular, $`C^4` ray regularity and $`A_{4,2}(G)<\infty` suffice for a second parameter
moment. Full regularity along rays gives $`A_{r+2,r}(G)\le M_{r+2}(G)` and hence moments of
all orders. The finite-order estimate alone does not assert tempered synthesis.

:::definition "aux:tempered-activation" (lean := "OperatorRidgelet.IsTemperedFunction, OperatorRidgelet.temperedTestFilter, OperatorRidgelet.temperedAdmissibilityConst") (uses := "def:admissible-filter, aux:conventions")
A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` that is a continuous function of
polynomial growth is the pair of $`\beta` and a continuous $`b:\mathbb R\to\mathbb R` with
$`|b(t)|\le C(1+|t|)^p` and $`\langle\beta,\varphi\rangle=\int b\varphi`. For a band-pass
$`\rho` the test filter $`\omega\mapsto\widehat\rho(-\omega)|\omega|^{-\alpha}` is a Schwartz
function, and the distributional admissibility constant is
$`C_{\beta,\rho}^{(\alpha)}=\frac1{2\pi}\langle\widehat\beta,\widehat\rho(-\,\cdot\,)|\cdot|^{-\alpha}\rangle`.
:::

:::theorem "thm:A" (lean := "OperatorRidgelet.Paper.thm_A_i_a, OperatorRidgelet.Paper.thm_A_i_b, OperatorRidgelet.Paper.thm_A_i_c, OperatorRidgelet.Paper.thm_A_ii_a, OperatorRidgelet.Paper.thm_A_ii_b, OperatorRidgelet.Paper.thm_A_ii_c, OperatorRidgelet.Paper.thm_A_iii_a, OperatorRidgelet.Paper.thm_A_iii_b, OperatorRidgelet.Paper.thm_A_iii_c, OperatorRidgelet.Paper.thm_A_iii_d, OperatorRidgelet.Paper.thm_A_iii_e") (uses := "def:ray-regular, aux:tempered-activation, def:spectral-coefficient, lem:coefficient-isometry, lem:spectral-target-basic, lem:coefficient-finite-order, lem:homogeneous-mixture, def:integral-network")
Let $`\alpha>0`. Part (ii) assumes an $`\alpha`-admissible Schwartz filter $`\rho`; part
(iii) assumes a band-pass filter. (i) For $`G\in L^1(\nu_\alpha)`, the function $`g_G` is
bounded with $`\|g_G\|_\infty\le\|G\|_{L^1(\nu_\alpha)}` and continuous,
and $`g_G=0` only if $`G=0` $`\nu_\alpha`-almost everywhere. (ii) For
$`G\in L^1(\nu_\alpha)\cap L^2(\nu_\alpha)` and every $`x`, the iterated integral
$`\int_H[\int_{\mathbb R}\gamma_G(a,c)\rho(\langle a,x\rangle+c)\,\mathrm dc]\,\nu_\alpha(\mathrm da)=C_\rho^{(\alpha)}g_G(x)`
converges absolutely, and if $`\gamma_G\in L^1(\lambda_\alpha)` its left side is the integral
network $`S_\rho[\gamma_G\lambda_\alpha](x)`. (iii) For a tempered $`\beta` that is a
continuous function of polynomial growth and $`G` regular along rays, the integrand
$`\gamma_G(a,c)\beta(\langle a,x\rangle+c)` is absolutely integrable on the product space.
Its integral is the ordinary network with finite coefficient measure $`\gamma_G\lambda_\alpha`
and equals $`C_{\beta,\rho}^{(\alpha)}g_G(x)`. This identity allows a zero constant.
Non-polynomiality is needed separately to choose a band-pass filter with a nonzero constant,
then normalize it for reconstruction or universality. A polynomial activation has zero
band-pass pairing.
:::

:::proof "thm:A"
Part (i) is {bpref "lem:spectral-target-basic"}[]. Parseval in the bias turns the inner
integral into a frequency integral of
$`\widehat\rho(\omega)G(-\omega a)` against $`\widehat\rho(-\omega)e^{-i\omega\langle a,x\rangle}`,
and the homogeneous substitution $`\xi=-\omega a` separates the admissibility constant from
$`g_G(x)`. For a tempered $`\beta` the bias integral is a distributional pairing with a test
function supported in $`-\operatorname{supp}\widehat\rho`; regularity along rays makes
$`a\mapsto` (test function) Bochner integrable in a $`C^m` norm, so the pairing commutes with
the direction integral. Joint absolute integrability follows independently from
{bpref "lem:coefficient-finite-order"}[], choosing a moment at least as large as the
activation's polynomial growth order. If every band-pass test function paired to zero with
$`\widehat\beta`, its support would be $`\{0\}` and $`\beta` a polynomial.
:::

# The frame operator and the reconstruction formula

:::definition "aux:frame-operator" (lean := "OperatorRidgelet.SpectralAntiDual, OperatorRidgelet.antiDualConj, OperatorRidgelet.rieszMap, OperatorRidgelet.rieszInv, OperatorRidgelet.transposeEmbed, OperatorRidgelet.frameOperator, OperatorRidgelet.ridgeletExtension, OperatorRidgelet.ridgeletRange, OperatorRidgelet.synthesis") (uses := "def:spectral-space, thm:B")
Let $`\mathcal E_\alpha'` be the continuous anti-dual of $`\mathcal E_\alpha`, represented as
the continuous conjugate-linear functionals on $`\mathcal K_\alpha`. The Riesz map is
$`J_\alpha f[g]=\langle f,g\rangle_{\mathcal E_\alpha}`, with inverse $`J_\alpha^{-1}` from the
Riesz representation theorem; the transpose of $`U_\alpha` is
$`U_\alpha'F[g]=\langle F,U_\alpha g\rangle_{L^2(\nu_\alpha)}` for $`F\in L^2(\nu_\alpha)`, and
the frame operator is $`T_\alpha=U_\alpha'U_\alpha`. With $`R_\rho:\mathcal E_\alpha\to
L^2(\lambda_\alpha)` the bounded extension of {bpref "thm:B"}[] (ii) and
$`\operatorname{Ran}R_\rho` its range, synthesis with the analysis filter is the transpose
$`S_\rho=R_\rho'`, $`(S_\rho\gamma)[g]=\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}`.
:::

:::definition "aux:backprojection" (lean := "OperatorRidgelet.backprojectionOf, OperatorRidgelet.backprojection, OperatorRidgelet.backprojectionLp, OperatorRidgelet.coefficientProjection") (uses := "def:spectral-coefficient, def:spectral-space, lem:partial-fourier-l2, lem:coefficient-adjoint")
For $`\gamma\in L^2(\lambda_\alpha)`, define the backprojection as $`\Lambda_\rho=W_\rho^*`.
By {bpref "lem:coefficient-adjoint"}[], it is represented by the ray average
$`\Lambda_\rho\gamma(\xi)=\frac1{2\pi}\int_{\mathbb R}\overline{\widehat\rho(\omega)}\,|\omega|^{-\alpha}\,\widehat\gamma(-\xi/\omega,\omega)\,\mathrm d\omega`,
computed from any jointly strongly measurable partial Fourier representative supplied by
{bpref "lem:partial-fourier-l2"}[]. The integral converges absolutely for almost every
$`\xi`, and its $`L^2(\nu_\alpha)` class is independent of the representative. With $`P_{\mathcal K_\alpha}` the
orthogonal projection onto $`\mathcal K_\alpha`, the coefficient projection is
$`\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}\Lambda_\rho`.
:::

:::definition "aux:hermite" (lean := "OperatorRidgelet.gaussFourierLine, OperatorRidgelet.hermiteExtension, OperatorRidgelet.hermiteCoefficient, OperatorRidgelet.gaussFourierInv") (uses := "aux:centered-gaussian, def:ridgelet-analysis, def:spectral-space")
For $`f\in L^2(\mu_Q)`, $`\xi\ne0`, and $`\tau(\xi)=\langle Q\xi,\xi\rangle^{1/2}`, the
analytic continuation $`z\mapsto\mathcal G_Qf(z\xi)=\int_Hf(x)e^{-iz\langle x,\xi\rangle}\mu_Q(\mathrm dx)`
and the entire function $`G_f(z\xi)=e^{z^2\tau(\xi)^2/2}\mathcal G_Qf(z\xi)`; the Hermite
coefficients $`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]` with the
probabilists' Hermite polynomials; and $`\Delta_Q`, the inverse of $`\mathcal G_Q` on its
range on $`\mathcal D_\alpha`, chosen as the element of $`\mathcal D_\alpha` with the given
transform.
:::

:::lemma_ "lem:weak-equals-strong" (lean := "OperatorRidgelet.Paper.lem_weak_equals_strong_i, OperatorRidgelet.Paper.lem_weak_equals_strong_ii") (uses := "def:integral-network, def:ridgelet-analysis, def:spectral-space, aux:frame-operator")
Let $`\rho\in\mathcal S(\mathbb R)` be real and
$`\gamma\in L^1(\lambda_\alpha)\cap L^2(\lambda_\alpha)`. Then the integral network
$`S_\rho[\gamma\lambda_\alpha]` is a bounded Borel function on $`H` (i), and for every
$`g\in\mathcal D_\alpha`,
$`\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}=\int_HS_\rho[\gamma\lambda_\alpha](x)\,\overline{g(x)}\,\mu_Q(\mathrm dx)`
(ii), so the synthesis functional $`S_\rho\gamma` is the integral network paired with $`g`
through $`\mu_Q`.
:::

:::proof "lem:weak-equals-strong"
$`|S_\rho[\gamma\lambda_\alpha]|\le\|\gamma\|_{L^1}\|\rho\|_\infty`, and the double integral
of $`|\gamma||g||\rho(\langle a,x\rangle+c)|` is at most
$`\|\gamma\|_{L^1}\|\rho\|_\infty\|g\|_{L^1(\mu_Q)}`, so Fubini applies; $`\rho` is real.
:::

:::lemma_ "lem:hermite-totality" (lean := "OperatorRidgelet.Paper.lem_hermite_totality_i, OperatorRidgelet.Paper.lem_hermite_totality_ii, OperatorRidgelet.Paper.lem_hermite_totality_iii, OperatorRidgelet.Paper.lem_hermite_totality_iv, OperatorRidgelet.Paper.lem_hermite_totality_v, OperatorRidgelet.Paper.lem_hermite_totality_vi") (uses := "aux:hermite, aux:centered-gaussian, roadmap:wick-totality")
For $`f\in L^2(\mu_Q)` and $`\xi\ne0`, the function $`z\mapsto G_f(z\xi)` is entire (i),
$`G_f(z\xi)=\sum_{n\ge0}\frac{(-iz\tau(\xi))^n}{n!}\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]`
(ii) with locally uniform convergence (iii),
$`|G_f(z\xi)|\le\|f\|_{L^2(\mu_Q)}e^{|z|^2\tau(\xi)^2/2}` (iv), and the Hermite inversion
formula
$`\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]=\frac{i^n}{\tau(\xi)^n}\frac{\mathrm d^n}{\mathrm dt^n}\bigl(e^{t^2\tau(\xi)^2/2}\mathcal G_Qf(t\xi)\bigr)\big|_{t=0}`
holds (v). The coefficients, over all $`\xi\ne0` and $`n`, determine $`f` in $`L^2(\mu_Q)`
(vi).
:::

:::proof "lem:hermite-totality"
The generating function $`e^{tY-t^2/2}=\sum_n\mathrm{He}_n(Y)t^n/n!` of a standard normal
$`Y` converges in $`L^2` locally uniformly in $`t\in\mathbb C`; pairing with $`f` gives the
series, the bound, and termwise differentiation. For totality, finite products of Hermite
polynomials in independent coordinates form a complete orthogonal system (the Wiener–Itô chaos
decomposition), and polarization of Wick powers expresses them through the directional Wick
powers.
:::

:::proposition "prop:coefficient-projection" (lean := "OperatorRidgelet.Paper.prop_coefficient_projection_i, OperatorRidgelet.Paper.prop_coefficient_projection_ii, OperatorRidgelet.Paper.prop_coefficient_projection_iii, OperatorRidgelet.Paper.prop_coefficient_projection_iv, OperatorRidgelet.Paper.prop_coefficient_projection_v, OperatorRidgelet.Paper.prop_coefficient_projection_vi, OperatorRidgelet.Paper.prop_coefficient_projection_vii, OperatorRidgelet.Paper.prop_coefficient_projection_viii") (uses := "aux:backprojection, aux:frame-operator, lem:coefficient-isometry, lem:homogeneous-mixture, thm:B")
Let $`\rho` be $`\alpha`-admissible with $`C=C_\rho^{(\alpha)}` and
$`\mathcal Y=L^2(\lambda_\alpha)`. The ray-average integral defining $`\Lambda_\rho\gamma`
converges absolutely for $`\nu_\alpha`-almost every $`\xi` (i), is independent as an $`L^2`
class of the jointly measurable Fourier representative (ii), and satisfies
$`\|\Lambda_\rho\gamma\|_{L^2(\nu_\alpha)}\le\sqrt C\|\gamma\|_{\mathcal Y}` (iii);
$`\Lambda_\rho` is the Hilbert adjoint of $`W_\rho` (iv) and $`\Lambda_\rho W_\rho=C\,\mathrm{Id}`
(v). The operator $`C^{-1}W_\rho\Lambda_\rho` projects onto $`W_\rho L^2(\nu_\alpha)`.
The operator $`\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}\Lambda_\rho` is the orthogonal
projection onto $`\operatorname{Ran}R_\rho` (vi), the minimum-norm solution of
$`S_\rho\gamma=F\in\mathcal E_\alpha'` is $`C^{-1}R_\rho J_\alpha^{-1}F` (vii), and all
solutions differ from it by an element of $`(\operatorname{Ran}R_\rho)^\perp` (viii).
:::

:::proof "prop:coefficient-projection"
The change of variables $`\xi=-\omega a` gives
$`\frac1{2\pi}\int\int|\omega|^{-\alpha}|\widehat\gamma(-\xi/\omega,\omega)|^2\mathrm d\omega\,\nu_\alpha(\mathrm d\xi)=\|\gamma\|_{\mathcal Y}^2`,
and weighted Cauchy–Schwarz in $`\omega` proves absolute convergence, representative
independence, the bound, and the adjoint identity. Since $`R_\rho=W_\rho U_\alpha` with
$`U_\alpha` unitary onto $`\mathcal K_\alpha`, $`C^{-1/2}W_\rho|_{\mathcal K_\alpha}` is an
isometry with closed image, and $`R_\rho'R_\rho=CJ_\alpha` (the frame identity, which is the
Plancherel identity read through the transpose) identifies the kernel of $`R_\rho'` with
$`(\operatorname{Ran}R_\rho)^\perp`.
:::

:::theorem "thm:C" (lean := "OperatorRidgelet.Paper.thm_C_i_a, OperatorRidgelet.Paper.thm_C_i_b, OperatorRidgelet.Paper.thm_C_i_c, OperatorRidgelet.Paper.thm_C_i_d, OperatorRidgelet.Paper.thm_C_ii_a, OperatorRidgelet.Paper.thm_C_ii_b, OperatorRidgelet.Paper.thm_C_iii_a, OperatorRidgelet.Paper.thm_C_iii_b, OperatorRidgelet.Paper.thm_C_iii_c, OperatorRidgelet.Paper.thm_C_iii_d, OperatorRidgelet.Paper.thm_C_iii_e, OperatorRidgelet.Paper.thm_C_iv_a, OperatorRidgelet.Paper.thm_C_iv_b, OperatorRidgelet.Paper.thm_C_iv_c, OperatorRidgelet.Paper.thm_C_iv_d, OperatorRidgelet.Paper.thm_C_iv_e, OperatorRidgelet.Paper.thm_C_iv_f, OperatorRidgelet.Paper.thm_C_iv_completion") (uses := "aux:frame-operator, aux:backprojection, aux:hermite, def:ray-regular, thm:B, lem:spectral-unitary, lem:fourier-slice, lem:homogeneous-mixture, lem:weak-equals-strong, lem:hermite-totality, prop:coefficient-projection")
Let $`\alpha>0` and let $`\rho` be an $`\alpha`-admissible Schwartz filter. (i) The frame operator
$`T_\alpha=U_\alpha'U_\alpha` equals the Riesz map $`J_\alpha`, an isometric bijection
$`\mathcal E_\alpha\to\mathcal E_\alpha'`, and $`S_\rho R_\rho f=C_\rho^{(\alpha)}T_\alpha f`
for $`f\in\mathcal E_\alpha`. (ii) For $`f\in\mathcal E_\alpha` and $`g\in\mathcal E_\alpha'`,
$`f=(C_\rho^{(\alpha)})^{-1}T_\alpha^{-1}S_\rho R_\rho f` and
$`g=(C_\rho^{(\alpha)})^{-1}S_\rho(R_\rho T_\alpha^{-1}g)`. (iii) If $`f\in\mathcal D_\alpha`
and $`\mathcal G_Qf\in L^1(\nu_\alpha)`, then $`T_\alpha f` is represented by
$`g_{\mathcal G_Qf}` against $`\mu_Q`; conversely, for $`G\in\mathcal K_\alpha`,
$`R_\rho T_\alpha^{-1}U_\alpha'G=W_\rho G`, and when $`G\in L^1(\nu_\alpha)`, $`U_\alpha'G` is
represented by $`g_G` and the second reconstruction formula is the spectral synthesis identity
of {bpref "thm:A"}[] (ii). (iv) The backprojection $`\Lambda_\rho` is a bounded operator
$`L^2(\lambda_\alpha)\to L^2(\nu_\alpha)` with $`\Lambda_\rho W_\rho=C_\rho^{(\alpha)}\mathrm{Id}`,
and $`\Lambda_\rho R_\rho f=C_\rho^{(\alpha)}U_\alpha f` holds in $`L^2(\nu_\alpha)` for
every $`f\in\mathcal E_\alpha`. For a concrete core input, it holds pointwise with
$`U_\alpha f=\mathcal G_Qf` when the continuous Fourier-slice representative is used.
The remaining inversion step uses Gaussian input: the Hermite formula at $`\xi\ne0`
recovers the Hermite coefficients of $`f` from $`\mathcal G_Qf`, these coefficients determine
$`f` in $`L^2(\mu_Q)`, and $`f=\Delta_Q[(C_\rho^{(\alpha)})^{-1}\Lambda_\rho R_\rho f]`.
:::

:::proof "thm:C"
Since $`U_\alpha` is unitary onto $`\mathcal K_\alpha`,
$`U_\alpha'U_\alpha f[g]=\langle U_\alpha f,U_\alpha g\rangle=\langle f,g\rangle_{\mathcal E_\alpha}`,
the Riesz representation theorem makes $`J_\alpha` an isometric bijection, and the Plancherel
identity gives $`(S_\rho R_\rho f)[g]=\langle R_\rho f,R_\rho g\rangle=C_\rho^{(\alpha)}J_\alpha f[g]`;
(ii) follows by applying $`T_\alpha^{-1}` or substituting $`f=T_\alpha^{-1}g`. Part (iii) is a
Fubini computation with $`u=J_\alpha^{-1}U_\alpha'G` and {bpref "lem:weak-equals-strong"}[],
and (iv) first uses $`\Lambda_\rho W_\rho=C_\rho^{(\alpha)}\mathrm{Id}` from
{bpref "lem:coefficient-adjoint"}[] and $`R_\rho=W_\rho U_\alpha` on the completion.
The pointwise core formula uses the continuous Fourier-slice representative; only the final
Hermite inversion invokes {bpref "lem:hermite-totality"}[] and Gaussian input.
:::

:::corollary "cor:coefficient-stability" (lean := "OperatorRidgelet.Paper.cor_coefficient_stability_i, OperatorRidgelet.Paper.cor_coefficient_stability_ii, OperatorRidgelet.Paper.cor_coefficient_stability_iii, OperatorRidgelet.Paper.cor_coefficient_stability_iv") (uses := "thm:C, aux:frame-operator, lem:coefficient-isometry")
Let $`\rho` be $`\alpha`-admissible, put $`C=C_\rho^{(\alpha)}>0`, and define
$`D_\rho=C^{-1}T_\alpha^{-1}S_\rho`. Then $`D_\rho R_\rho=\mathrm{Id}` and
$`\|D_\rho\|\le C^{-1/2}`. If $`f\in\mathcal E_\alpha`,
$`\gamma_\delta\in L^2(\lambda_\alpha)`, and $`\|\gamma_\delta-R_\rho f\|_2\le\delta`, then
$`\|D_\rho\gamma_\delta-f\|_{\mathcal E_\alpha}\le\delta/\sqrt C`.
This is an estimate in the completion norm, not an ambient $`L^2(\mu_Q)` or pointwise estimate.
:::

:::proof "cor:coefficient-stability"
The left-inverse identity is {bpref "thm:C"}[] (ii). Since the transpose $`S_\rho` has norm
at most $`\sqrt C` and $`T_\alpha^{-1}` is an isometry, the decoder has norm at most
$`C^{-1}\sqrt C=C^{-1/2}`. Apply this bound to $`\gamma_\delta-R_\rho f`.
:::

# Vector-valued targets

:::definition "aux:vector-valued" (lean := "OperatorRidgelet.gaussFourierVec, OperatorRidgelet.ridgeletVec, OperatorRidgelet.coefficientFormulaVec, OperatorRidgelet.biasFourierVec, OperatorRidgelet.HasBiasFourierVec, OperatorRidgelet.spectralCoefficientVec, OperatorRidgelet.spectralInnerVec, OperatorRidgelet.spectralCoreVec, OperatorRidgelet.gaussFourierLpVec, OperatorRidgelet.spectralRangeVec, OperatorRidgelet.spectralEmbedVec, OperatorRidgelet.ridgeletExtensionVec, OperatorRidgelet.ridgeletRangeVec, OperatorRidgelet.SpectralAntiDualVec, OperatorRidgelet.rieszMapVec, OperatorRidgelet.rieszInvVec, OperatorRidgelet.transposeEmbedVec, OperatorRidgelet.frameOperatorVec, OperatorRidgelet.synthesisVec, OperatorRidgelet.backprojectionOfVec, OperatorRidgelet.backprojectionVec, OperatorRidgelet.backprojectionLpVec, OperatorRidgelet.coefficientProjectionVec, OperatorRidgelet.gaussFourierLineVec, OperatorRidgelet.hermiteExtensionVec, OperatorRidgelet.hermiteCoefficientVec, OperatorRidgelet.gaussFourierInvVec") (uses := "def:ridgelet-analysis, def:spectral-coefficient, def:spectral-space, aux:frame-operator, aux:backprojection, aux:hermite")
Let $`Y` be a separable complex Hilbert space. All objects above have $`Y`-valued versions:
$`L^2(\mu_Q;Y)`, the Bochner integral
$`\mathcal G_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\mu_Q(\mathrm dx)\in Y`, the core
$`\mathcal D_\alpha(Y)`, the completion $`\mathcal E_\alpha(Y)` with inner product
$`\int\langle\mathcal G_Qf,\mathcal G_Qg\rangle_Y\mathrm d\nu_\alpha`, the transform
$`R_\rho f\in L^2(\lambda_\alpha;Y)`, the coefficient $`W_\rho G` of a density
$`G\in L^2(\nu_\alpha;Y)`, the anti-dual, Riesz map, frame and synthesis operators, the
backprojection, and the Hermite extension. The target $`g_G` and regularity along rays are
already polymorphic in the target.
:::

:::theorem "thm:vector-valued" (lean := "OperatorRidgelet.Paper.thm_vector_valued_A_i_a, OperatorRidgelet.Paper.thm_vector_valued_A_i_b, OperatorRidgelet.Paper.thm_vector_valued_A_i_c, OperatorRidgelet.Paper.thm_vector_valued_A_ii_a, OperatorRidgelet.Paper.thm_vector_valued_A_ii_b, OperatorRidgelet.Paper.thm_vector_valued_A_ii_c, OperatorRidgelet.Paper.thm_vector_valued_A_iii_a, OperatorRidgelet.Paper.thm_vector_valued_A_iii_b, OperatorRidgelet.Paper.thm_vector_valued_A_iii_c, OperatorRidgelet.Paper.thm_vector_valued_B_i_a, OperatorRidgelet.Paper.thm_vector_valued_B_i_b, OperatorRidgelet.Paper.thm_vector_valued_B_ii_a, OperatorRidgelet.Paper.thm_vector_valued_B_ii_b, OperatorRidgelet.Paper.thm_vector_valued_B_ii_c, OperatorRidgelet.Paper.thm_vector_valued_B_ii_d, OperatorRidgelet.Paper.thm_vector_valued_B_iii, OperatorRidgelet.Paper.thm_vector_valued_C_i_a, OperatorRidgelet.Paper.thm_vector_valued_C_i_b, OperatorRidgelet.Paper.thm_vector_valued_C_i_c, OperatorRidgelet.Paper.thm_vector_valued_C_i_d, OperatorRidgelet.Paper.thm_vector_valued_C_ii_a, OperatorRidgelet.Paper.thm_vector_valued_C_ii_b, OperatorRidgelet.Paper.thm_vector_valued_C_iii_a, OperatorRidgelet.Paper.thm_vector_valued_C_iii_b, OperatorRidgelet.Paper.thm_vector_valued_C_iii_c, OperatorRidgelet.Paper.thm_vector_valued_C_iii_d, OperatorRidgelet.Paper.thm_vector_valued_C_iii_e, OperatorRidgelet.Paper.thm_vector_valued_C_iv_a, OperatorRidgelet.Paper.thm_vector_valued_C_iv_b, OperatorRidgelet.Paper.thm_vector_valued_C_iv_c, OperatorRidgelet.Paper.thm_vector_valued_C_iv_d, OperatorRidgelet.Paper.thm_vector_valued_C_iv_e, OperatorRidgelet.Paper.thm_vector_valued_C_iv_f, OperatorRidgelet.Paper.thm_vector_valued_A_iii_e, OperatorRidgelet.Paper.thm_vector_valued_C_iv_completion") (uses := "aux:vector-valued, thm:A, thm:B, thm:C, lem:partial-fourier-l2, lem:spectral-target-basic, lem:coefficient-finite-order, lem:coefficient-adjoint")
{bpref "thm:A"}[], {bpref "thm:B"}[], and {bpref "thm:C"}[] hold for $`Y`-valued targets,
with the same constants, with absolute values replaced by norms in $`Y`, scalar integrals by
Bochner integrals, and $`L^2` spaces by their $`Y`-valued counterparts. The Riesz map and its
inverse are isometries; their operator norms are one for $`Y\ne\{0\}` and zero for
$`Y=\{0\}`. The $`L^1` input injectivity statement, admissible Schwartz synthesis and frame
identities, completed $`L^2` backprojection, and jointly absolutely integrable tempered
synthesis all retain the corresponding scalar assumptions. The Lean statements
are one theorem per part of the three scalar theorems ({bpref "thm:B"}[] in the abstract-pair
form of {bpref "thm:general-weights"}[]); the scalar existence claim of {bpref "thm:A"}[] (iii)
is not repeated.
:::

:::proof "thm:vector-valued"
Use {bpref "lem:partial-fourier-l2"}[] for jointly measurable Fourier representatives and
Hilbert-valued Plancherel, {bpref "lem:spectral-target-basic"}[] for spectral synthesis and
uniqueness, and {bpref "lem:coefficient-finite-order"}[] for coefficient moments and joint
absolute integrability. The vector adjoint identity and ray formula are
{bpref "lem:coefficient-adjoint"}[]. These common lemmas justify the Fubini and Parseval
steps with the same constants. Completing the vector core and applying Riesz representation
proves the frame and reconstruction statements; the Gaussian Hermite expansion is applied
componentwise. If $`Y\ne\{0\}`, a nonzero constant vector belongs to the Gaussian core by
{bpref "lem:gaussian-decay"}[], so its Riesz isometries have norm one; when $`Y=\{0\}`, both
spaces and norms are zero. Tempered synthesis uses the fixed-support $`C^m` Bochner argument
and the distributional pairing tensored with the identity of $`Y`.
:::
