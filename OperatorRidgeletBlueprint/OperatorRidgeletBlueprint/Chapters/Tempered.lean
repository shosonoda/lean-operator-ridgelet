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

#doc (Manual) "Reconstruction formulas and activation functions" =>
%%%
file := "tempered"
%%%

The analysis filter is Schwartz, while the synthesis activation may be a tempered
distribution, an element of $`\mathcal S'(\mathbb R)`. This includes unbounded activation
functions such as ReLU. For a non-polynomial tempered distribution, a filter supported
away from zero in frequency gives a nonzero distributional reconstruction pairing.
ReLU is admissible in this sense and is the primary exact example.

A dual-space identity and an ordinary integral network have different integrability
requirements. The Sobolev criterion below supplies an absolutely convergent network
integral, including non-band-pass filters, under direct conditions on the inverse Fourier
transform of $`h_a(\omega)=\rho^\sharp(-\omega)G(\omega a)`.
Appendix C gives the pairing and its estimates; Appendix G gives explicit filters.

:::definition "aux:tempered-distributions" (lean := "OperatorRidgelet.IsPolynomialDistribution, OperatorRidgelet.schwartzOfFun, OperatorRidgelet.tanhDistribution, OperatorRidgelet.gaussianCdfDistribution, OperatorRidgelet.gaussianDistribution") (uses := "aux:conventions")
A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` is a polynomial, equivalently
$`\beta=0` in $`\mathcal S'/\mathcal P`, when it acts by integration against some polynomial.
The Schwartz function with prescribed values is obtained by choice when one exists. The
standard activations $`\tanh`, the Gaussian distribution function $`\Phi`, and the Gaussian
$`e^{-u^2/2}` are realized as tempered distributions acting by integration against the
function; ReLU is treated in {bpref "cor:5.3"}[].
:::

:::definition "def:5.1" (lean := "OperatorRidgelet.IsRealDistribution, OperatorRidgelet.IsCutoff, OperatorRidgelet.IsApproximateIdentity, OperatorRidgelet.distributionConvolution, OperatorRidgelet.regularizedSpectrum, OperatorRidgelet.regularizedActivation, OperatorRidgelet.regularizedSynthesis, OperatorRidgelet.temperedSynthesis, OperatorRidgelet.Paper.def_5_1_i, OperatorRidgelet.Paper.def_5_1_ii, OperatorRidgelet.Paper.def_5_1_iii, OperatorRidgelet.Paper.def_5_1_iv, OperatorRidgelet.Paper.def_5_1_v, OperatorRidgelet.Paper.def_5_1_vi") (uses := "def:3.2, aux:conventions, aux:tempered-distributions, aux:frame-operator, thm:3.11")
Let $`\beta\in\mathcal S'(\mathbb R)` be real, that is, fixed by distributional conjugation,
and let $`\rho` be a band-pass filter. Choose an even $`\chi\in C_c^\infty(\mathbb R\setminus\{0\})`
equal to one on a neighbourhood of $`\operatorname{supp}\rho^\sharp` (i) and an even,
compactly supported, smooth approximate identity $`(\eta_\varepsilon)_{\varepsilon>0}` (ii),
and define the real Schwartz functions $`\beta_\varepsilon` by
$`\beta_\varepsilon^\sharp=\chi\,(\beta^\sharp*\eta_\varepsilon)\in C_c^\infty(\mathbb R\setminus\{0\})`
(iii–v: membership, existence, and uniqueness of $`\beta_\varepsilon`). For
$`\gamma\in\operatorname{Ran}R_\rho`, the regularized synthesis is
$`S_{\beta_\varepsilon}\gamma=R_{\beta_\varepsilon}'\gamma\in\mathcal E_\alpha'` (vi), and
the synthesis with $`\beta` is $`S_\beta\gamma=\lim_{\varepsilon\downarrow0}S_{\beta_\varepsilon}\gamma`
in the norm of $`\mathcal E_\alpha'`, whenever the limit exists.
:::

:::theorem "thm:5.2" (lean := "OperatorRidgelet.Paper.thm_5_2_i, OperatorRidgelet.Paper.thm_5_2_ii, OperatorRidgelet.Paper.thm_5_2_iii, OperatorRidgelet.Paper.thm_5_2_iv, OperatorRidgelet.Paper.thm_5_2_v, OperatorRidgelet.Paper.thm_5_2_vi") (uses := "def:5.1, aux:tempered-activation")
Let $`\beta\in\mathcal S'(\mathbb R)` be real and let $`\rho` be a band-pass filter. For every
$`f\in\mathcal E_\alpha` the limit defining $`S_\beta R_\rho f` exists (i), does not depend
on $`\chi` or $`(\eta_\varepsilon)` (ii), and
$`S_\beta R_\rho f=C_{\beta,\rho}^{(\alpha)}T_\alpha f` (iii). If
$`C_{\beta,\rho}^{(\alpha)}\ne0`, then
$`f=(C_{\beta,\rho}^{(\alpha)})^{-1}T_\alpha^{-1}S_\beta R_\rho f` for
$`f\in\mathcal E_\alpha` (iv) and
$`g=(C_{\beta,\rho}^{(\alpha)})^{-1}S_\beta(R_\rho T_\alpha^{-1}g)` for
$`g\in\mathcal E_\alpha'` (v). If $`\beta` is not a polynomial, then a band-pass $`\rho` with
$`C_{\beta,\rho}^{(\alpha)}\ne0` exists (vi).
:::

See the [proof in Appendix C](appendix-c/C___1-Proof-of-Theorem-5___2/#--informal-preview-_FLQQ_thm___5___2_FLQQ_--proof).

:::corollary "cor:5.3" (lean := "OperatorRidgelet.reluDistribution, OperatorRidgelet.reluAdmissibilityScale, OperatorRidgelet.reluNormalizedFilter, OperatorRidgelet.Paper.cor_5_3_i, OperatorRidgelet.Paper.cor_5_3_ii, OperatorRidgelet.Paper.cor_5_3_iii, OperatorRidgelet.Paper.cor_5_3_iv, OperatorRidgelet.Paper.cor_5_3_v, OperatorRidgelet.Paper.cor_5_3_vi, OperatorRidgelet.Paper.cor_5_3_vii, OperatorRidgelet.Paper.cor_5_3_viii") (uses := "thm:5.2, thm:4.2, def:3.2, aux:tempered-activation, def:4.1")
Let $`\beta=\operatorname{ReLU}`, $`\operatorname{ReLU}(t)=\max(t,0)`. Then
$`\operatorname{ReLU}^\sharp=-\operatorname{fp}(\omega^{-2})+i\pi\delta_0'` (i), which
equals $`-\omega^{-2}` away from the origin (ii). If
$`\rho^\sharp\in C_c^\infty(\mathbb R\setminus\{0\})` is nonzero, even, and nonpositive, then
$`C_{\operatorname{ReLU},\rho}^{(\alpha)}=-\frac1{2\pi}\int_{\mathbb R}\rho^\sharp(\omega)|\omega|^{-\alpha-2}\,\mathrm d\omega`
(iii), which is positive (iv). After rescaling $`\rho` the constant is one (v), and the two
reconstruction formulas of {bpref "thm:5.2"}[] (vi, vii) and
{bpref "thm:4.2"}[] (iii) (viii) hold with ReLU synthesis for every $`\alpha>0`.
:::

:::proof "cor:5.3"
From $`\operatorname{ReLU}(t)=(|t|+t)/2`, the identities $`(|t|)^\sharp=-2\operatorname{fp}(\omega^{-2})`
and $`t^\sharp=2\pi i\delta_0'` give the Fourier transform; the test function is supported
away from zero, so the $`\delta_0'` term vanishes and the finite part is ordinary
multiplication by $`\omega^{-2}`, and evenness and the sign of $`\rho^\sharp` give the
constant.
:::

:::example_ "ex:5.4" (lean := "OperatorRidgelet.Paper.lem_C_2_relu_mem, OperatorRidgelet.Paper.lem_C_2_relu_lipschitz, OperatorRidgelet.Paper.lem_C_2_relu_not_polynomial, OperatorRidgelet.Paper.lem_C_2_tanh_mem, OperatorRidgelet.Paper.lem_C_2_tanh_lipschitz, OperatorRidgelet.Paper.lem_C_2_tanh_not_polynomial, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_mem, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_C_2_gaussian_mem, OperatorRidgelet.Paper.lem_C_2_gaussian_lipschitz, OperatorRidgelet.Paper.lem_C_2_gaussian_not_polynomial, OperatorRidgelet.Paper.ex_5_4_relu, OperatorRidgelet.Paper.ex_5_4_tanh, OperatorRidgelet.Paper.ex_5_4_gaussianCdf, OperatorRidgelet.Paper.ex_5_4_gaussian") (uses := "thm:5.2, thm:4.2, thm:6.4")
ReLU, $`\tanh`, the Gaussian distribution function, and the Gaussian $`e^{-u^2/2}` are
globally Lipschitz, are not polynomials, and belong to $`\mathcal A_{0,2}`. Each of them is
therefore covered by {bpref "thm:5.2"}[], by {bpref "thm:4.2"}[] (iii), and
by the finite-width bounds of {bpref "thm:6.4"}[]; the Lean instance of this coverage is that for
every $`\alpha>0` there is a band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}\ne0` for each
of the four activations.
:::

:::proof "ex:5.4" (uses := "lem:C.2")
The three properties are {bpref "lem:C.2"}[]; a globally Lipschitz
function has polynomial growth, so {bpref "thm:4.2"}[] (iii) and {bpref "thm:6.4"}[] apply.
:::

*Remark 5.5 (Identity in the dual space versus integral network).*

The frame identity for a tempered activation holds in $`\mathcal E_\alpha'`. By itself it does not
produce a finite coefficient measure on $`H\times\mathbb R`. For a spectral density
regular along rays, {bpref "thm:4.2"}[] gives an absolutely convergent integral network;
{bpref "thm:6.4"}[] supplies finite total variation and moments. The ReLU examples use
this stronger conclusion.

# Integral representation under Sobolev conditions

The condition is imposed directly on
$`h_a(\omega)=\rho^\sharp(-\omega)G(\omega a)` through its inverse Fourier transform.
For Hilbert-valued functions the resulting weighted norm is the Bessel-potential
$`H^s` norm in the frequency variable. In a Banach space the weighted inverse-transform
norm is the assumption itself; a Fourier isometry is used only for Hilbert-valued outputs.

:::theorem "thm:5.6" (lean := "OperatorRidgelet.Paper.thm_5_6_i, OperatorRidgelet.Paper.thm_5_6_ii, OperatorRidgelet.Paper.thm_5_6_iii, OperatorRidgelet.Paper.thm_5_6_iv, OperatorRidgelet.Paper.thm_5_6_v") (uses := "def:3.2, aux:conventions")
Let $`H` be a real inner-product space with its Borel structure, and let $`\nu` be a
sigma-finite Borel measure with $`(D_t)_\#\nu=|t|^{-\alpha}\nu` for every $`t\ne0`,
where $`D_ta=ta` and $`\alpha>0`. Let $`\rho\in\mathcal S(\mathbb R;\mathbb R)` be nonzero,
let $`\sigma:\mathbb R\to\mathbb C` be continuous with
$`|\sigma(t)|\le C_\sigma(1+|t|)^p`, $`p\ge0` and $`s>p+1/2`, and let
$`g:H\to Y` be strongly measurable into a complex Banach space $`Y`. Write
$`g_a(\omega):=g(\omega a)` and $`h_a(\omega):=\rho^\sharp(-\omega)g_a(\omega)`.
Suppose there is a jointly measurable $`\gamma_g` such that for almost every $`a`,
$`\int\langle b\rangle^{2s}\|\gamma_g(a,b)\|^2\,\mathrm db<\infty` and
$`\int\gamma_g(a,b)e^{-i\omega b}\,\mathrm db=h_a(\omega)` for every $`\omega`.
For Hilbert $`Y` this means $`h_a\in H^s_\omega(\mathbb R;Y)` with
$`\check h_a=\gamma_g(a,\cdot)`. Assume also that
$`\mathfrak B_s(\rho,g)=\int(1+\|a\|)^s\|h_a\|_{H^s_\omega}\,\mathrm d\nu<\infty`, and that
$`q_{\alpha,\rho}(\omega)=\rho^\sharp(-\omega)|\omega|^{-\alpha}` lies in
$`H^s_\omega(\mathbb R)` as a Lebesgue class, without prescribing its value at zero.
Then $`g\in L^1(\nu;Y)`; for $`0\le r<s-1/2`
$`\int(1+\|a\|+|b|)^r\|\gamma_g\|\le2^{r/2}A_{s,r}\mathfrak B_s(\rho,g)`, so the coefficient
measure is finite; the direction average
$`\Psi_x(t)=\int\gamma_g(a,\langle a,x\rangle-t)\,\mathrm d\nu` is integrable and equals
$`\check q_{\alpha,\rho}(-t)f_g(x)` almost everywhere; and the absolutely convergent
network integral satisfies
$`S_\sigma[\Gamma_g](x)=(\!(\sigma,\rho)\!)_\alpha f_g(x)` with
$`(\!(\sigma,\rho)\!)_\alpha=(2\pi)^{-1}\langle\sigma^\sharp,q_{\alpha,\rho}\rangle`, uniformly
absolutely on bounded input sets and continuously in $`x`. Here
$`A_{s,r}=(2\pi)^{-1/2}(\int_{\mathbb R}(1+t^2)^{-(s-r)}\,\mathrm dt)^{1/2}`.
Admissibility of $`\rho` and non-polynomiality of $`\sigma` are not assumed for this
identity. Normalization to reproduce $`f_g` separately requires a nonzero pairing.

If in addition $`Y` is a separable complex Hilbert space,
$`(\!(\rho,\rho)\!)_\alpha<\infty` and $`g\in L^2(\nu;Y)`, then
$`\gamma_g\in L^2(\nu\otimes\mathrm db;Y)` and
$`\int_{H\times\mathbb R}\|\gamma_g(a,b)\|_Y^2\,\nu(\mathrm da)\,\mathrm db=(\!(\rho,\rho)\!)_\alpha\|g\|_{L^2(\nu;Y)}^2`.
The Hilbert structure and separability of $`Y` enter only in this last conclusion.
:::

The displayed statement includes the manuscript's product-space $`L^2` conclusion.
The associated Lean statements carry that clause in a weaker form; their verification
does not assert the full clause as written here.

See the [proof in Appendix C](appendix-c/C___4-Proof-of-Theorem-5___6/#--informal-preview-_FLQQ_thm___5___6_FLQQ_--proof).

*Remark 5.7 (What the synthesis identity uses).*

The absolutely convergent integral representation uses the inner product and Borel structure
of the input space,
homogeneity of the direction measure, and completeness of the output norm. The output
Hilbert structure is needed only for the $`L^2` coefficient conclusion. Positivity of the
admissibility constant is not required. The ray hypotheses already imply
$`G\in L^1(\nu;Y)` by evaluating the weighted inverse-transform estimate at a nonzero
frequency where $`\rho^\sharp` does not vanish and then using homogeneity.

A second parameter moment needs $`s>5/2`. With a globally Lipschitz activation,
{bpref "thm:6.3"}[] then applies; reconstruction of $`f_G` also requires
division by a nonzero synthesis pairing. Appendix G verifies a concrete non-band-pass
example.

*Examples of filters for the reconstruction formula.*

The following explicit filters meet the Sobolev criterion without band-pass support.
Their coefficient estimates and constants are proved in Appendix G.

:::proposition "prop:5.8" (lean := "OperatorRidgelet.gaussDerivFilter, OperatorRidgelet.gaussTarget, OperatorRidgelet.gaussRayCoefficient, OperatorRidgelet.gaussSobolevRay, OperatorRidgelet.Paper.prop_5_8_i, OperatorRidgelet.Paper.prop_5_8_ii, OperatorRidgelet.Paper.prop_5_8_iii, OperatorRidgelet.Paper.prop_5_8_iv, OperatorRidgelet.Paper.prop_5_8_v, OperatorRidgelet.Paper.prop_5_8_vi, OperatorRidgelet.Paper.prop_5_8_vii, OperatorRidgelet.Paper.prop_5_8_viii, OperatorRidgelet.Paper.prop_5_8_ix") (uses := "thm:5.6, def:3.2, aux:conventions")
Under the input-space and sigma-finite Borel measure hypotheses of {bpref "thm:5.6"}[],
let $`\nu` be homogeneous of degree $`\alpha>0` and finite on the unit ball. Fix $`s>1/2` and an
integer $`k\ge1` with $`2k>\alpha+2s-1/2`, and let
$`\rho_k^\sharp(\omega)=\omega^{2k}e^{-\omega^2}`, $`g(\xi)=e^{-\|\xi\|^2}v`. Then $`\rho_k` is
a real Schwartz filter (i) that is not band pass (ii) but is $`\alpha`-admissible for
$`\alpha<4k+1` (iii). The homogeneous moments $`\int(1+\|a\|^2)^{-d/2}\mathrm d\nu` are finite
for $`d>\alpha` (iv); the coefficient $`\gamma_g` is jointly measurable (v), each function
$`h_a(\omega)=\rho_k^\sharp(-\omega)g(\omega a)` lies in $`H^s_\omega` (vi), and
$`\mathfrak B_s(\rho_k,g)<\infty` (vii). The Sobolev test $`q_{\alpha,\rho_k}` lies in
$`H^s_\omega` (viii). Hence {bpref "thm:5.6"}[] applies to this filter for
every continuous activation of growth order $`p<s-1/2` (ix).

Put $`\delta=2k-\alpha`. For $`\sigma(t)=e^{-t^2/2}`, the reconstruction constant is
$`(\!(\sigma,\rho_k)\!)_\alpha=\Gamma((\delta+1)/2)(3/2)^{-(\delta+1)/2}/\sqrt{2\pi}>0`.
If $`s>3/2`, ReLU also satisfies the hypotheses and
$`(\!(\operatorname{ReLU},\rho_k)\!)_\alpha=-(2\pi)^{-1}\Gamma((\delta-1)/2)\ne0`.
The unit-ball finiteness hypothesis holds for the homogeneous Gaussian mixtures on the
infinite-dimensional Hilbert space used in the main construction.
:::

The two closed-form constants are part of the manuscript statement. The associated
Lean statements retain their Sobolev-pairing formulations; they do not assert these
closed-form evaluations.

See the [proof in Appendix G](appendix-g/proof-5-8/#--informal-preview-_FLQQ_prop___5___8_FLQQ_--proof).
