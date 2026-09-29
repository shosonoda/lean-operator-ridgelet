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

#doc (Manual) "The Gaussian-weighted ridgelet transform" =>
%%%
file := "transform"
%%%

The input and direction measures have different roles. A Gaussian probability measure
allows integration of a target over its input space. A homogeneous Gaussian mixture supplies
the scaling law for the direction integral. Fourier transformation in the bias then reduces
the ridgelet transform to restrictions of the weighted Fourier transform along lines.

We construct the coefficient operator, the Hilbert space $`\mathcal E_\alpha`, and the
Plancherel identity in that order. Appendix A contains the Gaussian and Fourier details;
Appendix B supplies the coefficient isometry used here. The statements use the coordinate
$`c=-b` and write $`\mathcal G_Qf` for the manuscript's $`F_Qf`.

# The input and direction measures

:::definition "aux:centered-gaussian" (lean := "OperatorRidgelet.IsTraceClassCovariance, OperatorRidgelet.IsCenteredGaussian")
A covariance is an injective, positive, self-adjoint, trace-class operator; the trace is taken
along a Hilbert basis. The centred Gaussian measure $`\mu=\mathcal N(0,Q)` is the Borel
probability measure with characteristic functional
$`\int_He^{i\langle x,\xi\rangle}\mu(\mathrm dx)=e^{-\langle Q\xi,\xi\rangle/2}`.
:::

:::definition "aux:gaussian-mixture" (lean := "OperatorRidgelet.IsCenteredGaussianLayers, OperatorRidgelet.mixtureWeight, OperatorRidgelet.gaussianMixtureOn, OperatorRidgelet.gaussianMixture") (uses := "aux:centered-gaussian, roadmap:gaussian-layers")
The Gaussian components of the mixture form a family $`N_s=\mathcal N(0,2sP)`, $`s>0`, with characteristic
functionals $`e^{-s\langle P\xi,\xi\rangle}`. For $`\alpha>0` the homogeneous Gaussian mixture
is $`\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`, the Giry-monad
bind of the weight $`s^{\alpha/2-1}\mathrm ds` against these components; the truncated mixture over a
set of scales is used in Appendix A.
:::

:::lemma_ "lem:3.1" (lean := "OperatorRidgelet.Paper.lem_3_1_i, OperatorRidgelet.Paper.lem_3_1_ii, OperatorRidgelet.Paper.lem_3_1_iii, OperatorRidgelet.Paper.lem_3_1_iv, OperatorRidgelet.Paper.lem_3_1_v, OperatorRidgelet.Paper.lem_3_1_vi") (uses := "aux:gaussian-mixture, aux:conventions")
Assume $`\dim H=\infty` and $`\alpha>0`. Then $`\nu_\alpha` is $`\sigma`-finite (i), finite
on bounded Borel sets (ii), infinite on $`H` (iii), and has full support (iv). For
$`\omega\ne0`, $`(D_\omega)_\#\nu_\alpha=|\omega|^{-\alpha}\nu_\alpha` (v), equivalently
$`\int_HF(\omega a)\,\nu_\alpha(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu_\alpha`
for every nonnegative Borel $`F` (vi).
:::

See the [proof in Appendix A](appendix-a/A___2-Proof-of-Lemma-3___1/#--informal-preview-_FLQQ_lem___3___1_FLQQ_--proof).

# Admissible filters, the transform, and the Fourier slice

:::definition "aux:conventions" (lean := "OperatorRidgelet.character, OperatorRidgelet.lineFourier, OperatorRidgelet.filterFourier, OperatorRidgelet.biasFourier, OperatorRidgelet.IsHomogeneous")
The Fourier convention is $`\widehat h(\omega)=\int_{\mathbb R}h(t)e^{-it\omega}\,\mathrm dt`
for functions on the line (for a real filter $`\rho` this is $`\widehat\rho`), and the partial
Fourier transform in the bias of a coefficient is
$`\widehat\gamma(a,\omega)=\int_{\mathbb R}\gamma(a,c)e^{-i\omega c}\,\mathrm dc`; the analysis
character on $`H` is $`x\mapsto e^{-i\langle x,\xi\rangle}`. A measure $`\nu` on $`H` is
homogeneous of degree $`\alpha` when $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for every
$`\omega\ne0`. The Lean network uses $`\langle a,x\rangle+c`; the manuscript bias is
$`b=-c`, so a coefficient written in $`b` has its bias Fourier transform reflected in
$`\omega` relative to the coefficient written in $`c`.
:::

:::definition "def:3.2" (lean := "OperatorRidgelet.IsAdmissible, OperatorRidgelet.admissibilityConst, OperatorRidgelet.IsBandPass, OperatorRidgelet.crossAdmissibilityConst, OperatorRidgelet.Paper.def_3_2") (uses := "aux:conventions")
A real $`\rho\in\mathcal S(\mathbb R)` is $`\alpha`-admissible if
$`0<(\!(\rho,\rho)\!)_\alpha=\frac1{2\pi}\int_{\mathbb R}|\widehat\rho(\omega)|^2|\omega|^{-\alpha}\,\mathrm d\omega<\infty`.
It is a band-pass filter if moreover $`\widehat\rho\in C_c^\infty(\mathbb R\setminus\{0\})`
(and $`\rho\ne0`): band-pass here specifies compact Fourier support away from zero.
Such a filter is $`\alpha`-admissible for every $`\alpha>0`. For two
admissible filters,
$`(\!(\rho_1,\rho_2)\!)_\alpha=\frac1{2\pi}\int_{\mathbb R}\widehat\rho_1(\omega)\overline{\widehat\rho_2(\omega)}|\omega|^{-\alpha}\,\mathrm d\omega`;
self-admissibility is the case $`\rho_1=\rho_2=\rho` of this pairing, since $`\rho` is real.
:::

:::definition "def:3.3" (lean := "OperatorRidgelet.ridgelet, OperatorRidgelet.parameterMeasure, OperatorRidgelet.gaussFourier") (uses := "aux:centered-gaussian, aux:gaussian-mixture, aux:conventions")
For $`f\in L^1(H,\mu_Q)` and $`\rho\in\mathcal S(\mathbb R)`, the Gaussian-weighted ridgelet
transform is $`R_\rho f(a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu_Q(\mathrm dx)`, and
$`\lambda_\alpha=\nu_\alpha\otimes\mathrm dc` is the parameter measure on $`H\times\mathbb R`.
The analogue of the Fourier transform of $`f` is the Fourier transform of the finite measure
$`f\mu_Q`, $`\mathcal G_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu_Q(\mathrm dx)`,
which is bounded and continuous; for a general input measure $`\mu` it is written
$`\mathcal G_\mu f`.
:::

:::lemma_ "lem:3.4" (lean := "OperatorRidgelet.Paper.lem_3_4_i, OperatorRidgelet.Paper.lem_3_4_ii, OperatorRidgelet.Paper.lem_3_4_iii, OperatorRidgelet.Paper.lem_3_4_iv, OperatorRidgelet.Paper.lem_3_4_v") (uses := "def:3.3, aux:conventions")
Let $`f\in L^1(H,\mu)` and $`\rho\in\mathcal S(\mathbb R)`. Then $`R_\rho f` is bounded (i)
and jointly continuous (ii) on $`H\times\mathbb R`, and for every $`a`,
$`\|R_\rho f(a,\cdot)\|_{L^1(\mathbb R)}\le\|f\|_{L^1(\mu)}\|\rho\|_{L^1}` (iii) and
$`\|R_\rho f(a,\cdot)\|_{L^2(\mathbb R)}^2\le\|f\|_{L^2(\mu)}^2\|\rho\|_{L^2}^2` if
$`f\in L^2(\mu)` (iv). For every $`a\in H` and $`\omega\in\mathbb R`,
$`\widehat{R_\rho f}(a,\omega)=\widehat\rho(\omega)\,\mathcal G_\mu f(-\omega a)` (v).
:::

:::proof "lem:3.4"
Boundedness is $`|R_\rho f|\le\|f\|_1\|\rho\|_\infty`, joint continuity is dominated
convergence, the bounds are Cauchy–Schwarz and Tonelli in the probability measure $`\mu`, and
the substitution $`u=\langle a,x\rangle+c` in the inner Fourier transform gives the slice
identity. For nonzero $`a`, the function $`\omega\mapsto\mathcal G_\mu f(\omega a)` is
the restriction of $`\mathcal G_\mu f` to the line through the origin spanned by $`a`.
:::

:::definition "def:3.5" (lean := "OperatorRidgelet.HasBiasFourier, OperatorRidgelet.spectralCoefficient, OperatorRidgelet.coefficientFormula, OperatorRidgelet.Paper.def_3_5") (uses := "def:3.2, def:3.3, aux:conventions")
For a function $`g` on $`H`, write $`g_a(\omega):=g(\omega a)`, $`\omega\in\mathbb R`.
For $`a\ne0` this is the restriction of $`g` to the line through the origin spanned by
$`a`; for $`a=0` it is constant. We write $`G_a` when the density is denoted by $`G`.
Let $`\rho` be $`\alpha`-admissible and $`G\in L^2(\nu_\alpha)` Borel. The coefficient
$`W_\rho G\in L^2(\lambda_\alpha)` is the function whose partial Fourier transform in the bias
is $`\widehat{W_\rho G}(a,\omega)=\widehat\rho(\omega)\,G_a(-\omega)`, characterized through
Parseval's identity against Schwartz test functions in the bias. For every such
$`G\in L^2(\nu_\alpha)` and $`\nu_\alpha`-almost every $`a`,
$`\gamma_G(a,c)=W_\rho G(a,c)=\frac1{2\pi}\int_{\mathbb R}\widehat\rho(\omega)G(-\omega a)e^{i\omega c}\,\mathrm d\omega`;
the integral converges absolutely for every $`c`. This formula is the theorem part of the definition.
:::

:::lemma_ "lem:3.6" (lean := "OperatorRidgelet.Paper.lem_3_6_i, OperatorRidgelet.Paper.lem_3_6_ii, OperatorRidgelet.Paper.lem_3_6_iii")
For an admissible Schwartz filter and a sigma-finite homogeneous direction measure,
the backprojection $`\Lambda_\rho=W_\rho^*` is the Hilbert adjoint of the coefficient operator,
with values in the frequency space $`L^2(\nu_\alpha)`. It satisfies
$`\Lambda_\rho W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}` and
$`\|\Lambda_\rho\gamma\|_2\le\sqrt{(\!(\rho,\rho)\!)_\alpha}\|\gamma\|_2`.
Its integral formula is
$`\Lambda_\rho\gamma(\xi)=(2\pi)^{-1}\int\overline{\widehat\rho(\omega)}\widehat\gamma(-\xi/\omega,\omega)|\omega|^{-\alpha}\,\mathrm d\omega`;
this integral is absolutely convergent for almost every $`\xi` and is independent of the
jointly measurable Fourier representative.
:::

:::proof "lem:3.6" (uses := "lem:A.1, lem:B.1")
Plancherel in the bias and the substitution $`\xi=-\omega a` identify the inner product
with the integral formula. Weighted Cauchy–Schwarz and Tonelli give its absolute convergence and
norm bound; polarization of the coefficient isometry gives the left inverse identity.
:::

# The Hilbert space E-alpha

:::definition "def:3.7" (lean := "OperatorRidgelet.spectralCore, OperatorRidgelet.spectralInner, OperatorRidgelet.spectralRange, OperatorRidgelet.gaussFourierLp, OperatorRidgelet.spectralEmbed") (uses := "def:3.3, aux:gaussian-mixture")
$`\mathcal D_\alpha=\{f\in L^2(H,\mu_Q):\mathcal G_Qf\in L^2(H,\nu_\alpha)\}` with
$`\langle f,g\rangle_{\mathcal E_\alpha}=\int_H\mathcal G_Qf\,\overline{\mathcal G_Qg}\,\mathrm d\nu_\alpha`.
The Hilbert space $`\mathcal E_\alpha` is the completion of $`\mathcal D_\alpha` in this norm,
and $`\mathcal K_\alpha=\overline{\mathcal G_Q(\mathcal D_\alpha)}^{L^2(\nu_\alpha)}` is the
closure of the range of $`\mathcal G_Q` on $`\mathcal D_\alpha`. The formalization represents
$`\mathcal E_\alpha` by $`\mathcal K_\alpha` and the unitary $`U_\alpha` by the map
$`U:\mathcal D_\alpha\to\mathcal K_\alpha`, $`f\mapsto\mathcal G_Qf`.
:::

:::lemma_ "lem:3.8" (lean := "OperatorRidgelet.Paper.lem_3_8_i, OperatorRidgelet.Paper.lem_3_8_ii, OperatorRidgelet.Paper.lem_3_8_iii") (uses := "def:3.7")
The spectral form is positive definite on $`\mathcal D_\alpha` (i), $`\mathcal G_Q` is an
isometry from $`(\mathcal D_\alpha,\langle\cdot,\cdot\rangle_{\mathcal E_\alpha})` into
$`\mathcal K_\alpha` (ii), and its image is dense (iii), so that $`\mathcal G_Q` extends
uniquely to a unitary $`U_\alpha:\mathcal E_\alpha\to\mathcal K_\alpha`.
:::

:::proof "lem:3.8" (uses := "lem:3.1")
If the norm of $`f\in\mathcal D_\alpha` vanishes, then $`\mathcal G_Qf=0` almost everywhere,
hence everywhere by continuity and full support of $`\nu_\alpha`; the Fourier transform
determines finite complex Borel measures on a separable Hilbert space, so $`f\mu_Q=0`.
:::

:::lemma_ "lem:3.9" (lean := "OperatorRidgelet.Paper.lem_3_9_i, OperatorRidgelet.Paper.lem_3_9_ii") (uses := "aux:centered-gaussian, def:3.7")
For every $`t>0`, $`\alpha>0`, and integer $`m\ge0`,
$`\int_H\|\xi\|^{2m}e^{-t\langle Q\xi,\xi\rangle}\,\nu_\alpha(\mathrm d\xi)<\infty` (i).
Consequently, if $`f\in L^2(\mu_Q)` and
$`|\mathcal G_Qf(\xi)|\le C(1+\|\xi\|)^pe^{-t\langle Q\xi,\xi\rangle/2}`, then
$`f\in\mathcal D_\alpha` for every $`\alpha>0` (ii).
:::

See the [proof in Appendix A](appendix-a/A___3-Proof-of-Lemma-3___9/#--informal-preview-_FLQQ_lem___3___9_FLQQ_--proof).

:::example_ "ex:3.10" (lean := "OperatorRidgelet.Paper.ex_3_10_i, OperatorRidgelet.Paper.ex_3_10_ii, OperatorRidgelet.Paper.ex_3_10_iii, OperatorRidgelet.Paper.ex_3_10_iv, OperatorRidgelet.Paper.ex_3_10_v") (uses := "def:3.7, aux:centered-gaussian, ex:7.1, ex:7.4")
The constant function $`1` has $`\mathcal G_Q1(\xi)=e^{-\langle Q\xi,\xi\rangle/2}` (i), so
$`1\in\mathcal D_\alpha` for every $`\alpha>0` (ii) and $`\mathcal E_\alpha\ne\{0\}` (iii).
The non-cylindrical Gaussian target $`f_W(x)=e^{-\langle Wx,x\rangle/2}` of
{bpref "ex:7.1"}[] belongs to every $`\mathcal D_\alpha` (iv), and so do the
components of the neural-operator layers with Gaussian activation of
{bpref "ex:7.4"}[] (v).
:::

:::proof "ex:3.10" (uses := "lem:3.9")
The Gaussian characteristic functional gives $`\mathcal G_Q1`, and the decay lemma with
$`m=0`, $`p=0`, $`t=1` gives $`1\in\mathcal D_\alpha`; the other two assertions are proved with
the examples, using only the decay lemma and the Fourier-slice identity.
:::

# Plancherel identity, closed range, and injectivity

:::theorem "thm:3.11" (lean := "OperatorRidgelet.Paper.thm_3_11_i_a, OperatorRidgelet.Paper.thm_3_11_i_b, OperatorRidgelet.Paper.thm_3_11_ii_a, OperatorRidgelet.Paper.thm_3_11_ii_b, OperatorRidgelet.Paper.thm_3_11_ii_c, OperatorRidgelet.Paper.thm_3_11_ii_d, OperatorRidgelet.Paper.thm_3_11_iii") (uses := "def:3.2, def:3.3, def:3.7")
Let $`\alpha>0`. (i) For $`f,g\in\mathcal D_\alpha` and $`\alpha`-admissible
$`\rho_1,\rho_2`, the transforms $`R_{\rho_1}f` and $`R_{\rho_2}g` belong to
$`L^2(\lambda_\alpha)`, and
$`\langle R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha)}=(\!(\rho_1,\rho_2)\!)_\alpha\langle f,g\rangle_{\mathcal E_\alpha}`.
(ii) An $`\alpha`-admissible $`\rho` determines a unique bounded extension
$`R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)` with
$`\|R_\rho f\|^2=(\!(\rho,\rho)\!)_\alpha\|f\|_{\mathcal E_\alpha}^2`; its range is closed, and
$`R_\rho=W_\rho U_\alpha`. (iii) If $`\rho` is $`\alpha`-admissible and
$`f\in L^1(H,\mu_Q)`, then $`R_\rho f=0` $`\lambda_\alpha`-almost everywhere implies $`f=0`
$`\mu_Q`-almost everywhere.
:::

See the [proof in Appendix A](appendix-a/A___4-Proof-of-Theorem-3___11_LPAR_i_RPAR_-and-_LPAR_ii_RPAR_/#--informal-preview-_FLQQ_thm___3___11_FLQQ_--proof).

# Examples of analysis filters

A band-pass filter is available for every positive homogeneity exponent. The Mexican
hat separates admissibility from the additional support condition used for band-pass
reconstruction. Appendix G supplies the calculations.

:::definition "aux:explicit-filters" (lean := "OperatorRidgelet.Filters.bump, OperatorRidgelet.Filters.bandPassHat, OperatorRidgelet.Filters.bandPassFun, OperatorRidgelet.Filters.bandPass, OperatorRidgelet.Filters.mexicanHatFun, OperatorRidgelet.Filters.mexicanHat") (uses := "aux:conventions")
With the bump $`\eta(u)=\exp(-1/(1-u^2))` for $`|u|<1` and $`0` otherwise, the band-pass
filter $`\rho_{\mathrm{bp}}` is the real even Schwartz function with
$`\widehat\rho_{\mathrm{bp}}(\omega)=-\eta(2|\omega|-3)`, obtained by Fourier inversion; the
Mexican hat is $`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}`. Both are taken as Schwartz maps by
choice, with junk value $`0` should the explicit function fail to be Schwartz.
:::

:::example_ "ex:3.12" (lean := "OperatorRidgelet.Paper.ex_3_12_i, OperatorRidgelet.Paper.ex_3_12_ii, OperatorRidgelet.Paper.ex_3_12_iii, OperatorRidgelet.Paper.ex_3_12_iv, OperatorRidgelet.Paper.ex_3_12_v, OperatorRidgelet.Paper.ex_3_12_vi, OperatorRidgelet.Paper.ex_3_12_vii, OperatorRidgelet.Paper.ex_3_12_viii, OperatorRidgelet.Paper.ex_3_12_ix, OperatorRidgelet.Paper.ex_3_12_x") (uses := "aux:explicit-filters, def:3.2, aux:conventions")
$`\widehat\rho_{\mathrm{bp}}` is smooth (i), nonpositive (ii), nonzero (iii), and supported in
$`\{1\le|\omega|\le2\}` (iv), so $`\rho_{\mathrm{bp}}\in\mathcal S(\mathbb R)` is real (v)
and even (vi) with the prescribed Fourier transform (vii), satisfies the band-pass condition
(viii), and is $`\alpha`-admissible for every $`\alpha>0` (ix); multiplying by
$`((\!(\rho_{\mathrm{bp}},\rho_{\mathrm{bp}})\!)_\alpha)^{-1/2}` normalizes the admissibility constant to one (x).
The sign makes it admissible for ReLU synthesis in the sense of {bpref "cor:5.3"}[].
:::

See the [proof in Appendix G](appendix-g/proof-3-12/#--informal-preview-_FLQQ_ex___3___12_FLQQ_--proof).

:::example_ "ex:3.13" (lean := "OperatorRidgelet.Paper.ex_3_13_i, OperatorRidgelet.Paper.ex_3_13_ii, OperatorRidgelet.Paper.ex_3_13_iii, OperatorRidgelet.Paper.ex_3_13_iv, OperatorRidgelet.Paper.ex_3_13_v, OperatorRidgelet.Paper.ex_3_13_vi") (uses := "aux:explicit-filters, def:3.2, aux:conventions")
$`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}` is a Schwartz function (i) with
$`\widehat\rho_{\mathrm{MH}}(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}` (ii). It is
$`\alpha`-admissible exactly for $`0<\alpha<5` (iii), with
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\Gamma((5-\alpha)/2)` (iv) and
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_1=1` (v). It is not band pass (vi).
When $`0<\alpha<5`, {bpref "thm:3.11"}[], {bpref "thm:4.3"}[] and part (ii) of
{bpref "thm:4.2"}[] apply. The band-pass statements in part (iii) of
{bpref "thm:4.2"}[] and in {bpref "thm:5.2"}[] do not apply to this filter.
:::

See the [proof in Appendix G](appendix-g/proof-3-13/#--informal-preview-_FLQQ_ex___3___13_FLQQ_--proof).
