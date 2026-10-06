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

We construct the input and direction measures, the partial Fourier transform, and the coefficient operator before proving Plancherel and injectivity. Every supporting statement and proof needed below is given here, before its use. The coordinates are $`c=-b`, as in the Lean declarations.

# Gaussian input and homogeneous direction measures

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

For an eigenbasis $`Pe_j=p_je_j` with $`\sum_jp_j<\infty`, independent standard Gaussians give the almost surely convergent series $`X=\sum_j\sqrt{p_j}Z_je_j`. The scaled random variables $`\sqrt{2s}X` realize every Gaussian component on one probability space. Joint measurability in $`s` and the sample variable gives the mixture integration formula.

:::lemma_ "lem:3.1" (lean := "OperatorRidgelet.Paper.lem_3_1_i, OperatorRidgelet.Paper.lem_3_1_ii, OperatorRidgelet.Paper.lem_3_1_iii, OperatorRidgelet.Paper.lem_3_1_iv") (uses := "aux:gaussian-mixture")
For every Borel set $`E`, the map $`s\mapsto\mathcal N(0,2sP)(E)` is Borel measurable (i), and
the mixture defines a countably additive Borel measure with
$`\nu_\alpha(E)=\int_0^\infty\mathcal N(0,2sP)(E)\,s^{\alpha/2-1}\,\mathrm ds` (ii). For every
nonnegative Borel $`F`,
$`\int_HF\,\mathrm d\nu_\alpha=\int_0^\infty\int_HF\,\mathrm d\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`
(iii), and the identity holds for complex $`F` with $`\int_H|F|\,\mathrm d\nu_\alpha<\infty`
(iv).
:::

:::proof "lem:3.1"
$`\mathcal N(0,2sP)(E)=\int\mathbf 1_E(\sqrt{2s}\,x)\,\mathcal N(0,P)(\mathrm dx)` with a
jointly Borel integrand; monotone convergence gives countable additivity and extends the
integral identity from indicators to nonnegative Borel functions.
:::

:::lemma_ "lem:3.2" (lean := "OperatorRidgelet.Paper.lem_3_2_i, OperatorRidgelet.Paper.lem_3_2_ii, OperatorRidgelet.Paper.lem_3_2_iii, OperatorRidgelet.Paper.lem_3_2_iv, OperatorRidgelet.Paper.lem_3_2_v, OperatorRidgelet.Paper.lem_3_2_vi") (uses := "aux:gaussian-mixture, aux:conventions")
Assume $`\dim H=\infty` and $`\alpha>0`. Then $`\nu_\alpha` is $`\sigma`-finite (i), finite
on bounded Borel sets (ii), infinite on $`H` (iii), and has full support (iv). For
$`\omega\ne0`, $`(D_\omega)_\#\nu_\alpha=|\omega|^{-\alpha}\nu_\alpha` (v), equivalently
$`\int_HF(\omega a)\,\nu_\alpha(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu_\alpha`
for every nonnegative Borel $`F` (vi).
:::

:::proof "lem:3.2" (uses := "lem:3.1")
Coordinate small-ball estimates of order $`s^{-k/2}` with $`k>\alpha` give finite mass on
bounded sets, the part $`s\le1` is integrable because $`s^{\alpha/2-1}` is, balls exhaust
$`H` while $`\nu_\alpha(H)=\int_0^\infty s^{\alpha/2-1}\mathrm ds=\infty`, injectivity of
$`P` gives full support, and the substitution $`u=s\omega^2` in each component proves homogeneity.
:::

# Filters, the ridgelet transform, and the Fourier slice

:::definition "aux:conventions" (lean := "OperatorRidgelet.character, OperatorRidgelet.lineFourier, OperatorRidgelet.filterFourier, OperatorRidgelet.biasFourier, OperatorRidgelet.IsHomogeneous")
The Fourier convention is $`h^\sharp(\omega)=\int_{\mathbb R}h(t)e^{-it\omega}\,\mathrm dt`
for functions on the line (for a real filter $`\rho` this is $`\rho^\sharp`), and the partial
Fourier transform in the bias of a coefficient is
$`\gamma^\sharp(a,\omega)=\int_{\mathbb R}\gamma(a,c)e^{-i\omega c}\,\mathrm dc`; the analysis
character on $`H` is $`x\mapsto e^{-i\langle x,\xi\rangle}`. A measure $`\nu` on $`H` is
homogeneous of degree $`\alpha` when $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for every
$`\omega\ne0`. The Lean network uses $`\langle a,x\rangle+c`; the manuscript bias is
$`b=-c`, so a coefficient written in $`b` has its bias Fourier transform reflected in
$`\omega` relative to the coefficient written in $`c`.
:::

:::definition "def:3.3" (lean := "OperatorRidgelet.IsAdmissible, OperatorRidgelet.admissibilityConst, OperatorRidgelet.IsBandPass, OperatorRidgelet.crossAdmissibilityConst, OperatorRidgelet.Paper.def_3_3") (uses := "aux:conventions")
A real $`\rho\in\mathcal S(\mathbb R)` is $`\alpha`-admissible if
$`0<(\!(\rho,\rho)\!)_\alpha=\frac1{2\pi}\int_{\mathbb R}|\rho^\sharp(\omega)|^2|\omega|^{-\alpha}\,\mathrm d\omega<\infty`.
It is a band-pass filter if moreover $`\rho^\sharp\in C_c^\infty(\mathbb R\setminus\{0\})`
(and $`\rho\ne0`): band-pass here specifies compact Fourier support away from zero.
Such a filter is $`\alpha`-admissible for every $`\alpha>0`. For two
admissible filters,
$`(\!(\rho_1,\rho_2)\!)_\alpha=\frac1{2\pi}\int_{\mathbb R}\rho_1^\sharp(\omega)\overline{\rho_2^\sharp(\omega)}|\omega|^{-\alpha}\,\mathrm d\omega`;
self-admissibility is the case $`\rho_1=\rho_2=\rho` of this pairing, since $`\rho` is real.
:::

:::definition "def:3.4" (lean := "OperatorRidgelet.ridgelet, OperatorRidgelet.parameterMeasure, OperatorRidgelet.gaussFourier") (uses := "aux:centered-gaussian, aux:gaussian-mixture, aux:conventions")
For $`f\in L^1(H,\mu_Q)` and $`\rho\in\mathcal S(\mathbb R)`, the Gaussian-weighted ridgelet
transform is $`R_\rho f(a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu_Q(\mathrm dx)`, and
$`\lambda_\alpha=\nu_\alpha\otimes\mathrm dc` is the parameter measure on $`H\times\mathbb R`.
The analogue of the Fourier transform of $`f` is the Fourier transform of the finite measure
$`f\mu_Q`, $`F_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu_Q(\mathrm dx)`,
which is bounded and continuous; for a general input measure $`\mu` it is written
$`F_\mu f`.
:::

:::lemma_ "lem:3.5" (lean := "OperatorRidgelet.Paper.lem_3_5_i, OperatorRidgelet.Paper.lem_3_5_ii, OperatorRidgelet.Paper.lem_3_5_iii, OperatorRidgelet.Paper.lem_3_5_iv, OperatorRidgelet.Paper.lem_3_5_v") (uses := "def:3.4, aux:conventions")
Let $`f\in L^1(H,\mu)` and $`\rho\in\mathcal S(\mathbb R)`. Then $`R_\rho f` is bounded (i)
and jointly continuous (ii) on $`H\times\mathbb R`, and for every $`a`,
$`\|R_\rho f(a,\cdot)\|_{L^1(\mathbb R)}\le\|f\|_{L^1(\mu)}\|\rho\|_{L^1}` (iii) and
$`\|R_\rho f(a,\cdot)\|_{L^2(\mathbb R)}^2\le\|f\|_{L^2(\mu)}^2\|\rho\|_{L^2}^2` if
$`f\in L^2(\mu)` (iv). For every $`a\in H` and $`\omega\in\mathbb R`,
$`(R_\rho f)^\sharp(a,\omega)=\rho^\sharp(\omega)\,F_\mu f(-\omega a)` (v).
:::

:::proof "lem:3.5"
Boundedness is $`|R_\rho f|\le\|f\|_1\|\rho\|_\infty`, joint continuity is dominated
convergence, the bounds are Cauchy–Schwarz and Tonelli in the probability measure $`\mu`, and
the substitution $`u=\langle a,x\rangle+c` in the inner Fourier transform gives the slice
identity. For nonzero $`a`, the function $`\omega\mapsto F_\mu f(\omega a)` is
the restriction of $`F_\mu f` to the line through the origin spanned by $`a`.
:::

# Partial Fourier transformation and the coefficient operator

We first construct the partial bias transform on the product $`L^2` space. The coefficient formula, its isometry, and the adjoint then follow in sequence.

:::lemma_ "lem:3.6" (lean := "OperatorRidgelet.Paper.lem_3_6, OperatorRidgelet.Paper.lem_3_6_uniqueness") (uses := "aux:conventions")
For a separable complex Hilbert space $`Y`, partial Fourier transformation in the bias is a
unitary map from $`L^2(\nu\otimes\mathrm dc;Y)` onto
$`L^2(\nu\otimes\mathrm d\omega/(2\pi);Y)`. Each transform admits a jointly strongly
measurable representative agreeing with the one-dimensional Plancherel transform of
$`c\mapsto\gamma(a,c)` for almost every $`a`. Such representatives agree almost everywhere.
:::

:::proof "lem:3.6"
Apply the one-dimensional Fourier unitary to the fibers of the product $`L^2` space. Its
inverse on the fibers proves surjectivity; the product $`L^2` identification supplies joint
measurability. Fiberwise uniqueness and Fubini prove independence of the representative.
:::

:::definition "def:3.7" (lean := "OperatorRidgelet.HasBiasFourier, OperatorRidgelet.spectralCoefficient, OperatorRidgelet.coefficientFormula, OperatorRidgelet.Paper.def_3_7") (uses := "def:3.3, def:3.4, aux:conventions")
For a function $`g` on $`H`, write $`g_a(\omega):=g(\omega a)`, $`\omega\in\mathbb R`.
For $`a\ne0` this is the restriction of $`g` to the line through the origin spanned by
$`a`; for $`a=0` it is constant. We write $`G_a` when the density is denoted by $`G`.
Let $`\rho` be $`\alpha`-admissible and $`G\in L^2(\nu_\alpha)` Borel. The coefficient
$`W_\rho G\in L^2(\lambda_\alpha)` is the function whose partial Fourier transform in the bias
is $`(W_\rho G)^\sharp(a,\omega)=\rho^\sharp(\omega)\,G_a(-\omega)`, characterized through
Parseval's identity against Schwartz test functions in the bias. For every such
$`G\in L^2(\nu_\alpha)` and $`\nu_\alpha`-almost every $`a`,
$`\gamma_G(a,c)=W_\rho G(a,c)=\frac1{2\pi}\int_{\mathbb R}\rho^\sharp(\omega)G(-\omega a)e^{i\omega c}\,\mathrm d\omega`;
the integral converges absolutely for every $`c`. This formula is the theorem part of the definition.
:::

:::lemma_ "lem:3.8" (lean := "OperatorRidgelet.Paper.lem_3_8_i, OperatorRidgelet.Paper.lem_3_8_ii, OperatorRidgelet.Paper.lem_3_8_iii, OperatorRidgelet.Paper.lem_3_8_iv, OperatorRidgelet.Paper.def_3_7, OperatorRidgelet.Paper.lem_3_8_v") (uses := "def:3.7")
$`W_\rho:L^2(\nu_\alpha)\to L^2(\lambda_\alpha)` is well defined (i), independent of the Borel
representative of $`G` (ii), and
$`\|W_\rho G\|_{L^2(\lambda_\alpha)}^2=(\!(\rho,\rho)\!)_\alpha\|G\|_{L^2(\nu_\alpha)}^2` (iii). If
$`G\in L^1(\nu_\alpha)`, then $`\omega\mapsto G(-\omega a)` is integrable on compact subsets of
$`\mathbb R\setminus\{0\}` for $`\nu_\alpha`-almost every $`a` (iv), and the explicit formula
for $`\gamma_G` holds already for $`G\in L^2(\nu_\alpha)`, with absolute convergence on
almost every $`a` and every bias. In this notation the Fourier-slice identity reads
$`R_\rho f=W_\rho\,F_Qf`.
:::

:::proof "lem:3.8" (uses := "lem:3.2")
$`(a,\omega)\mapsto G(-\omega a)` is Borel, and the homogeneous change of variables with
Tonelli gives
$`\frac1{2\pi}\int\int|\rho^\sharp(\omega)|^2|G(-\omega a)|^2\,\nu_\alpha(\mathrm da)\,\mathrm d\omega=(\!(\rho,\rho)\!)_\alpha\|G\|^2_{L^2(\nu_\alpha)}`;
the same computation with $`|G|` on a compact set gives local integrability, and the inverse
Fourier transform in $`\omega` for almost every $`a` gives the formula.
:::

:::lemma_ "lem:3.9" (lean := "OperatorRidgelet.Paper.lem_3_9_i, OperatorRidgelet.Paper.lem_3_9_ii, OperatorRidgelet.Paper.lem_3_9_iii")
For an admissible Schwartz filter and a sigma-finite homogeneous direction measure,
the backprojection $`W_\rho^*` is the Hilbert adjoint of the coefficient operator,
with values in the frequency space $`L^2(\nu_\alpha)`. It satisfies
$`W_\rho^* W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}` and
$`\|W_\rho^*\gamma\|_2\le\sqrt{(\!(\rho,\rho)\!)_\alpha}\|\gamma\|_2`.
Its integral formula is
$`W_\rho^*\gamma(\xi)=(2\pi)^{-1}\int_{\mathbb R\setminus\{0\}}
    \overline{\rho^\sharp(\omega)}\gamma^\sharp(-\xi/\omega,\omega)|\omega|^{-\alpha}\,\mathrm d\omega`;
this integral is absolutely convergent for almost every $`\xi` and is independent of the
jointly measurable Fourier representative.
:::

:::proof "lem:3.9" (uses := "lem:3.6, lem:3.8")
Plancherel in the bias and the substitution $`\xi=-\omega a` identify the inner product
with the integral formula. Weighted Cauchy–Schwarz and Tonelli give its absolute convergence and
norm bound; polarization of the coefficient isometry gives the left inverse identity.
:::

# The Hilbert space E-alpha

:::definition "def:3.10" (lean := "OperatorRidgelet.spectralCore, OperatorRidgelet.spectralInner, OperatorRidgelet.spectralRange, OperatorRidgelet.gaussFourierLp, OperatorRidgelet.spectralEmbed") (uses := "def:3.4, aux:gaussian-mixture")
$`\mathcal D_\alpha=\{f\in L^2(H,\mu_Q):F_Qf\in L^2(H,\nu_\alpha)\}` with
$`\langle f,g\rangle_{\mathcal E_\alpha}=\int_HF_Qf\,\overline{F_Qg}\,\mathrm d\nu_\alpha`.
The Hilbert space $`\mathcal E_\alpha` is the completion of $`\mathcal D_\alpha` in this norm,
and $`\mathcal K_\alpha=\overline{F_Q(\mathcal D_\alpha)}^{L^2(\nu_\alpha)}` is the
closure of the range of $`F_Q` on $`\mathcal D_\alpha`. The formalization represents
$`\mathcal E_\alpha` by $`\mathcal K_\alpha` and the core restriction of $`F_Q` by the map
$`F_Q:\mathcal D_\alpha\to\mathcal K_\alpha`, $`f\mapsto F_Qf`.
:::

:::lemma_ "lem:3.11" (lean := "OperatorRidgelet.Paper.lem_3_11_i, OperatorRidgelet.Paper.lem_3_11_ii, OperatorRidgelet.Paper.lem_3_11_iii") (uses := "def:3.10")
The spectral form is positive definite on $`\mathcal D_\alpha` (i), $`F_Q` is an
isometry from $`(\mathcal D_\alpha,\langle\cdot,\cdot\rangle_{\mathcal E_\alpha})` into
$`\mathcal K_\alpha` (ii), and its image is dense (iii), so that $`F_Q` extends
uniquely to a unitary $`F_Q:\mathcal E_\alpha\to\mathcal K_\alpha`.
The same symbol denotes the concrete Gaussian integral on the core and its unitary
extension. Outside the core it is an $`L^2(\nu_\alpha)` class; no pointwise
Gaussian integral representation is assumed.
:::

:::proof "lem:3.11" (uses := "lem:3.2")
If the norm of $`f\in\mathcal D_\alpha` vanishes, then $`F_Qf=0` almost everywhere,
hence everywhere by continuity and full support of $`\nu_\alpha`; the Fourier transform
determines finite complex Borel measures on a separable Hilbert space, so $`f\mu_Q=0`.
:::

:::lemma_ "lem:3.12" (lean := "OperatorRidgelet.Paper.lem_3_12_i, OperatorRidgelet.Paper.lem_3_12_ii") (uses := "aux:centered-gaussian, def:3.10")
For every $`t>0`, $`\alpha>0`, and integer $`m\ge0`,
$`\int_H\|\xi\|^{2m}e^{-t\langle Q\xi,\xi\rangle}\,\nu_\alpha(\mathrm d\xi)<\infty` (i).
Consequently, if $`f\in L^2(\mu_Q)` and
$`|F_Qf(\xi)|\le C(1+\|\xi\|)^pe^{-t\langle Q\xi,\xi\rangle/2}`, then
$`f\in\mathcal D_\alpha` for every $`\alpha>0` (ii).
:::

:::proof "lem:3.12" (uses := "lem:3.1")
On each Gaussian component, Cauchy–Schwarz separates the polynomial factor, whose moments are
finite, from the Gaussian factor, whose integral is $`\prod_j(1+8st\theta_j)^{-1/2}` with
$`\theta_j>0` the eigenvalues of $`P^{1/2}QP^{1/2}`; retaining $`k>4m+2\alpha` factors makes
the mixture integral finite.
:::

:::example_ "ex:3.13" (lean := "OperatorRidgelet.Paper.ex_3_13_i, OperatorRidgelet.Paper.ex_3_13_ii, OperatorRidgelet.Paper.ex_3_13_iii, OperatorRidgelet.Paper.ex_3_13_iv, OperatorRidgelet.Paper.ex_3_13_v") (uses := "def:3.10, aux:centered-gaussian")
The constant function $`1` has $`F_Q1(\xi)=e^{-\langle Q\xi,\xi\rangle/2}` (i), so
$`1\in\mathcal D_\alpha` for every $`\alpha>0` (ii) and $`\mathcal E_\alpha\ne\{0\}` (iii).
:::

:::proof "ex:3.13" (uses := "lem:3.12")
The Gaussian characteristic functional gives $`F_Q1`, and the decay lemma with
$`m=0`, $`p=0`, $`t=1` gives $`1\in\mathcal D_\alpha`.
:::

Further core elements are the Gaussian targets and Gaussian-activation operator layers proved in Section 7. The Lean panel for the preceding example also retains two verified facets about those later examples. They support this preview and are not used in the proof of the constant example or the next theorem.

# Plancherel identity, closed range, and injectivity

:::theorem "thm:3.14" (lean := "OperatorRidgelet.Paper.thm_3_14_i_a, OperatorRidgelet.Paper.thm_3_14_i_b, OperatorRidgelet.Paper.thm_3_14_ii_a, OperatorRidgelet.Paper.thm_3_14_ii_b, OperatorRidgelet.Paper.thm_3_14_ii_c, OperatorRidgelet.Paper.thm_3_14_ii_d, OperatorRidgelet.Paper.thm_3_14_iii") (uses := "def:3.3, def:3.4, def:3.10")
Let $`\alpha>0`. (i) For $`f,g\in\mathcal D_\alpha` and $`\alpha`-admissible
$`\rho_1,\rho_2`, the transforms $`R_{\rho_1}f` and $`R_{\rho_2}g` belong to
$`L^2(\lambda_\alpha)`, and
$`\langle R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha)}=(\!(\rho_1,\rho_2)\!)_\alpha\langle f,g\rangle_{\mathcal E_\alpha}`.
(ii) An $`\alpha`-admissible $`\rho` determines a unique bounded extension
$`R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)` with
$`\|R_\rho f\|^2=(\!(\rho,\rho)\!)_\alpha\|f\|_{\mathcal E_\alpha}^2`; its range is closed, and
$`R_\rho=W_\rho F_Q`. (iii) If $`\rho` is $`\alpha`-admissible and
$`f\in L^1(H,\mu_Q)`, then $`R_\rho f=0` $`\lambda_\alpha`-almost everywhere implies $`f=0`
$`\mu_Q`-almost everywhere.
:::

:::proof "thm:3.14" (uses := "lem:3.5, lem:3.2, lem:3.8, lem:3.11")
Apply the one-dimensional Plancherel identity in the bias to the Fourier-slice identity and
substitute $`\xi=-\omega a` by homogeneity; admissibility gives square integrability and
Cauchy–Schwarz justifies the cross identity. The norm identity extends $`R_\rho` to the
completion, an isometry up to a nonzero scalar has closed range, and
$`R_\rho=W_\rho F_Q` holds on the core and extends by continuity. For (iii), a fixed
frequency with $`\rho^\sharp\ne0` and homogeneity give $`F_Qf=0` almost everywhere,
and the argument of {bpref "lem:3.11"}[] finishes.
:::

# Examples of analysis filters

A band-pass filter works for every positive homogeneity exponent. The Mexican hat distinguishes admissibility from the extra support assumption in band-pass reconstruction.

:::definition "aux:explicit-filters" (lean := "OperatorRidgelet.Filters.bump, OperatorRidgelet.Filters.bandPassHat, OperatorRidgelet.Filters.bandPassFun, OperatorRidgelet.Filters.bandPass, OperatorRidgelet.Filters.mexicanHatFun, OperatorRidgelet.Filters.mexicanHat") (uses := "aux:conventions")
With the bump $`\eta(u)=\exp(-1/(1-u^2))` for $`|u|<1` and $`0` otherwise, the band-pass
filter $`\rho_{\mathrm{bp}}` is the real even Schwartz function with
$`\rho_{\mathrm{bp}}^\sharp(\omega)=-\eta(2|\omega|-3)`, obtained by Fourier inversion; the
Mexican hat is $`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}`. Both are taken as Schwartz maps by
choice, with junk value $`0` should the explicit function fail to be Schwartz.
:::

:::example_ "ex:3.15" (lean := "OperatorRidgelet.Paper.ex_3_15_i, OperatorRidgelet.Paper.ex_3_15_ii, OperatorRidgelet.Paper.ex_3_15_iii, OperatorRidgelet.Paper.ex_3_15_iv, OperatorRidgelet.Paper.ex_3_15_v, OperatorRidgelet.Paper.ex_3_15_vi, OperatorRidgelet.Paper.ex_3_15_vii, OperatorRidgelet.Paper.ex_3_15_viii, OperatorRidgelet.Paper.ex_3_15_ix, OperatorRidgelet.Paper.ex_3_15_x") (uses := "aux:explicit-filters, def:3.3, aux:conventions")
$`\rho_{\mathrm{bp}}^\sharp` is smooth (i), nonpositive (ii), nonzero (iii), and supported in
$`\{1\le|\omega|\le2\}` (iv), so $`\rho_{\mathrm{bp}}\in\mathcal S(\mathbb R)` is real (v)
and even (vi) with the prescribed Fourier transform (vii), satisfies the band-pass condition
(viii), and is $`\alpha`-admissible for every $`\alpha>0` (ix); multiplying by
$`((\!(\rho_{\mathrm{bp}},\rho_{\mathrm{bp}})\!)_\alpha)^{-1/2}` normalizes the admissibility constant to one (x).
The sign makes it admissible for ReLU synthesis in the sense of {bpref "cor:5.5"}[].
:::

:::proof "ex:3.15"
The bump and all its derivatives vanish at $`|u|=1`, the support stays away from
$`\omega=0`, Fourier inversion maps $`C_c^\infty` into $`\mathcal S`, even real Fourier data
give an even real inverse, and on the compact support $`|\omega|^{-\alpha}` is bounded above
and below.
:::

:::example_ "ex:3.16" (lean := "OperatorRidgelet.Paper.ex_3_16_i, OperatorRidgelet.Paper.ex_3_16_ii, OperatorRidgelet.Paper.ex_3_16_iii, OperatorRidgelet.Paper.ex_3_16_iv, OperatorRidgelet.Paper.ex_3_16_v, OperatorRidgelet.Paper.ex_3_16_vi") (uses := "aux:explicit-filters, def:3.3, aux:conventions")
$`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}` is a Schwartz function (i) with
$`\rho_{\mathrm{MH}}^\sharp(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}` (ii). It is
$`\alpha`-admissible exactly for $`0<\alpha<5` (iii), with
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\Gamma((5-\alpha)/2)` (iv) and
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_1=1` (v). It is not band pass (vi).
When $`0<\alpha<5`, {bpref "thm:3.14"}[], {bpref "thm:4.8"}[] and part (ii) of
{bpref "thm:4.5"}[] apply. The band-pass statements in part (iii) of
{bpref "thm:4.5"}[] and in {bpref "thm:5.4"}[] do not apply to this filter.
:::

:::proof "ex:3.16"
With $`g(t)=e^{-t^2/2}`, $`\rho_{\mathrm{MH}}=-g''` and the differentiation rule gives the
Fourier transform; then
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\int_{\mathbb R}|\omega|^{4-\alpha}e^{-\omega^2}\mathrm d\omega=\Gamma((5-\alpha)/2)`,
convergent at zero exactly when $`\alpha<5`.
:::
