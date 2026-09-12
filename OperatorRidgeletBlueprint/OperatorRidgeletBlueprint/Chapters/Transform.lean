import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Transform
import OperatorRidgelet.Paper.Revision
import OperatorRidgelet.Paper.Examples
import OperatorRidgelet.Transform.Infra

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The Gaussian-weighted ridgelet transform" =>
%%%
file := "transform"
%%%

This chapter is Section 3 of the manuscript together with Appendix A (the Gaussian mixture),
Appendix G (the finite-dimensional case and the dilation obstruction), Appendix H (abstract
weights), and Appendix I (explicit filters). The input measure is the centred Gaussian
$`\mu_Q=\mathcal N(0,Q)`, the direction measure is the homogeneous Gaussian mixture
$`\nu_\alpha`, and the parameter measure is $`\lambda_\alpha=\nu_\alpha\otimes\mathrm dc`.

The formalization states the core theory for an abstract pair $`(\mu,\nu)`, as in Appendix H:
$`\mu` a Borel probability measure on $`H` and $`\nu` a $`\sigma`-finite Borel measure with
full support that is homogeneous of degree $`\alpha`. The Gaussian pair
$`(\mu_Q,\nu_\alpha)` is the instance. The Hilbert space $`\mathcal E_\alpha` is represented by
the closed subspace $`\mathcal K_\alpha=\overline{\mathcal G_Q(\mathcal D_\alpha)}\subseteq
L^2(\nu_\alpha)`, to which it is unitarily equivalent by {bpref "lem:spectral-unitary"}[].

# The input and direction measures

:::definition "aux:centered-gaussian" (lean := "OperatorRidgelet.IsTraceClassCovariance, OperatorRidgelet.IsCenteredGaussian")
A covariance is an injective, positive, self-adjoint, trace-class operator; the trace is taken
along a Hilbert basis. The centred Gaussian measure $`\mu=\mathcal N(0,Q)` is the Borel
probability measure with characteristic functional
$`\int_He^{i\langle x,\xi\rangle}\mu(\mathrm dx)=e^{-\langle Q\xi,\xi\rangle/2}`.
:::

:::definition "aux:gaussian-mixture" (lean := "OperatorRidgelet.IsCenteredGaussianLayers, OperatorRidgelet.mixtureWeight, OperatorRidgelet.gaussianMixtureOn, OperatorRidgelet.gaussianMixture") (uses := "aux:centered-gaussian, roadmap:gaussian-layers")
The Gaussian layers are a family $`N_s=\mathcal N(0,2sP)`, $`s>0`, with characteristic
functionals $`e^{-s\langle P\xi,\xi\rangle}`. For $`\alpha>0` the homogeneous Gaussian mixture
is $`\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`, the Giry-monad
bind of the weight $`s^{\alpha/2-1}\mathrm ds` against the layers; the truncated mixture over a
set of scales is used in Appendix A.
:::

:::lemma_ "lem:mixture-integration" (lean := "OperatorRidgelet.Paper.lem_mixture_integration_i, OperatorRidgelet.Paper.lem_mixture_integration_ii, OperatorRidgelet.Paper.lem_mixture_integration_iii, OperatorRidgelet.Paper.lem_mixture_integration_iv") (uses := "aux:gaussian-mixture")
For every Borel set $`E`, the map $`s\mapsto\mathcal N(0,2sP)(E)` is Borel measurable (i), and
the mixture defines a countably additive Borel measure with
$`\nu_\alpha(E)=\int_0^\infty\mathcal N(0,2sP)(E)\,s^{\alpha/2-1}\,\mathrm ds` (ii). For every
nonnegative Borel $`F`,
$`\int_HF\,\mathrm d\nu_\alpha=\int_0^\infty\int_HF\,\mathrm d\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`
(iii), and the identity holds for complex $`F` with $`\int_H|F|\,\mathrm d\nu_\alpha<\infty`
(iv).
:::

:::proof "lem:mixture-integration"
$`\mathcal N(0,2sP)(E)=\int\mathbf 1_E(\sqrt{2s}\,x)\,\mathcal N(0,P)(\mathrm dx)` with a
jointly Borel integrand; monotone convergence gives countable additivity and extends the
integral identity from indicators to nonnegative Borel functions.
:::

:::lemma_ "lem:homogeneous-mixture" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_i, OperatorRidgelet.Paper.lem_homogeneous_mixture_ii, OperatorRidgelet.Paper.lem_homogeneous_mixture_iii, OperatorRidgelet.Paper.lem_homogeneous_mixture_iv, OperatorRidgelet.Paper.lem_homogeneous_mixture_v, OperatorRidgelet.Paper.lem_homogeneous_mixture_vi") (uses := "aux:gaussian-mixture, aux:conventions, lem:mixture-integration")
Assume $`\dim H=\infty` and $`\alpha>0`. Then $`\nu_\alpha` is $`\sigma`-finite (i), finite
on bounded Borel sets (ii), infinite on $`H` (iii), and has full support (iv). For
$`\omega\ne0`, $`(D_\omega)_\#\nu_\alpha=|\omega|^{-\alpha}\nu_\alpha` (v), equivalently
$`\int_HF(\omega a)\,\nu_\alpha(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu_\alpha`
for every nonnegative Borel $`F` (vi).
:::

:::proof "lem:homogeneous-mixture"
Coordinate small-ball estimates of order $`s^{-k/2}` with $`k>\alpha` give finite mass on
bounded sets, the part $`s\le1` is integrable because $`s^{\alpha/2-1}` is, balls exhaust
$`H` while $`\nu_\alpha(H)=\int_0^\infty s^{\alpha/2-1}\mathrm ds=\infty`, injectivity of
$`P` gives full support, and the substitution $`u=s\omega^2` on each layer proves homogeneity.
:::

:::lemma_ "lem:mixture-character" (lean := "OperatorRidgelet.Paper.lem_mixture_character_i, OperatorRidgelet.Paper.lem_mixture_character_ii, OperatorRidgelet.Paper.lem_mixture_character_iii, OperatorRidgelet.Paper.lem_mixture_character_iv") (uses := "aux:gaussian-mixture, lem:mixture-integration, lem:homogeneous-mixture")
For $`z\ne0` put $`q=\langle Pz,z\rangle>0` (i) and
$`\nu_\alpha^{\varepsilon,M}=\int_\varepsilon^M\mathcal N(0,2sP)s^{\alpha/2-1}\mathrm ds`.
Then $`\lim_{\varepsilon\downarrow0,M\uparrow\infty}\int_He^{i\langle z,\xi\rangle}\,\nu_\alpha^{\varepsilon,M}(\mathrm d\xi)=\Gamma(\alpha/2)q^{-\alpha/2}`
(ii), where $`\int_0^\infty e^{-sq}s^{\alpha/2-1}\mathrm ds=\Gamma(\alpha/2)q^{-\alpha/2}`
(iii). In contrast $`\int_H|e^{i\langle z,\xi\rangle}|\,\nu_\alpha(\mathrm d\xi)=\infty`
(iv), so the limit is not a Lebesgue integral against $`\nu_\alpha`.
:::

:::proof "lem:mixture-character"
The truncated mixture is finite, so Fubini and the characteristic functional of
$`\mathcal N(0,2sP)` reduce the integral to
$`\int_\varepsilon^Me^{-sq}s^{\alpha/2-1}\mathrm ds`; monotone convergence and the
substitution $`u=sq` finish the proof.
:::

# Admissible filters, the transform, and the Fourier slice

:::definition "aux:conventions" (lean := "OperatorRidgelet.character, OperatorRidgelet.lineFourier, OperatorRidgelet.filterFourier, OperatorRidgelet.biasFourier, OperatorRidgelet.IsHomogeneous")
The Fourier convention is $`\widehat h(\omega)=\int_{\mathbb R}h(t)e^{-it\omega}\,\mathrm dt`
for functions on the line (for a real filter $`\rho` this is $`\widehat\rho`), and the partial
Fourier transform in the bias of a coefficient is
$`\widehat\gamma(a,\omega)=\int_{\mathbb R}\gamma(a,c)e^{-i\omega c}\,\mathrm dc`; the analysis
character on $`H` is $`x\mapsto e^{-i\langle x,\xi\rangle}`. A measure $`\nu` on $`H` is
homogeneous of degree $`\alpha` when $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for every
$`\omega\ne0`.
:::

:::definition "def:admissible-filter" (lean := "OperatorRidgelet.IsAdmissible, OperatorRidgelet.admissibilityConst, OperatorRidgelet.IsBandPass, OperatorRidgelet.crossAdmissibilityConst, OperatorRidgelet.Paper.def_admissible_filter") (uses := "aux:conventions")
A real $`\rho\in\mathcal S(\mathbb R)` is $`\alpha`-admissible if
$`0<C_\rho^{(\alpha)}=\frac1{2\pi}\int_{\mathbb R}|\widehat\rho(\omega)|^2|\omega|^{-\alpha}\,\mathrm d\omega<\infty`.
It is a band-pass filter if moreover $`\widehat\rho\in C_c^\infty(\mathbb R\setminus\{0\})`
(and $`\rho\ne0`), in which case it is $`\alpha`-admissible for every $`\alpha>0`. For two
admissible filters,
$`C_{\rho_1,\rho_2}^{(\alpha)}=\frac1{2\pi}\int_{\mathbb R}\widehat\rho_1(\omega)\overline{\widehat\rho_2(\omega)}|\omega|^{-\alpha}\,\mathrm d\omega`.
:::

:::definition "def:ridgelet-analysis" (lean := "OperatorRidgelet.ridgelet, OperatorRidgelet.parameterMeasure, OperatorRidgelet.gaussFourier") (uses := "aux:centered-gaussian, aux:gaussian-mixture, aux:conventions")
For $`f\in L^1(H,\mu_Q)` and $`\rho\in\mathcal S(\mathbb R)`, the Gaussian-weighted ridgelet
transform is $`R_\rho f(a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu_Q(\mathrm dx)`, and
$`\lambda_\alpha=\nu_\alpha\otimes\mathrm dc` is the parameter measure on $`H\times\mathbb R`.
The analogue of the Fourier transform of $`f` is the Fourier transform of the finite measure
$`f\mu_Q`, $`\mathcal G_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu_Q(\mathrm dx)`,
which is bounded and continuous; for a general input measure $`\mu` it is written
$`\mathcal G_\mu f`.
:::

:::lemma_ "lem:fourier-slice" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_i, OperatorRidgelet.Paper.lem_fourier_slice_ii, OperatorRidgelet.Paper.lem_fourier_slice_iii, OperatorRidgelet.Paper.lem_fourier_slice_iv, OperatorRidgelet.Paper.lem_fourier_slice_v") (uses := "def:ridgelet-analysis, aux:conventions")
Let $`f\in L^1(H,\mu)` and $`\rho\in\mathcal S(\mathbb R)`. Then $`R_\rho f` is bounded (i)
and jointly continuous (ii) on $`H\times\mathbb R`, and for every $`a`,
$`\|R_\rho f(a,\cdot)\|_{L^1(\mathbb R)}\le\|f\|_{L^1(\mu)}\|\rho\|_{L^1}` (iii) and
$`\|R_\rho f(a,\cdot)\|_{L^2(\mathbb R)}^2\le\|f\|_{L^2(\mu)}^2\|\rho\|_{L^2}^2` if
$`f\in L^2(\mu)` (iv). For every $`a\in H` and $`\omega\in\mathbb R`,
$`\widehat{R_\rho f}(a,\omega)=\widehat\rho(\omega)\,\mathcal G_\mu f(-\omega a)` (v).
:::

:::proof "lem:fourier-slice"
Boundedness is $`|R_\rho f|\le\|f\|_1\|\rho\|_\infty`, joint continuity is dominated
convergence, the bounds are Cauchy–Schwarz and Tonelli in the probability measure $`\mu`, and
the substitution $`u=\langle a,x\rangle+c` in the inner Fourier transform gives the slice
identity.
:::

:::definition "def:spectral-coefficient" (lean := "OperatorRidgelet.HasBiasFourier, OperatorRidgelet.spectralCoefficient, OperatorRidgelet.coefficientFormula, OperatorRidgelet.Paper.def_spectral_coefficient") (uses := "def:admissible-filter, def:ridgelet-analysis, aux:conventions")
Let $`\rho` be $`\alpha`-admissible and $`G\in L^2(\nu_\alpha)` Borel. The coefficient
$`W_\rho G\in L^2(\lambda_\alpha)` is the function whose partial Fourier transform in the bias
is $`\widehat{W_\rho G}(a,\omega)=\widehat\rho(\omega)\,G(-\omega a)`, characterized through
Parseval's identity against Schwartz test functions in the bias. For every such
$`G\in L^2(\nu_\alpha)` and $`\nu_\alpha`-almost every $`a`,
$`\gamma_G(a,c)=W_\rho G(a,c)=\frac1{2\pi}\int_{\mathbb R}\widehat\rho(\omega)G(-\omega a)e^{i\omega c}\,\mathrm d\omega`;
the integral converges absolutely for every $`c`. This formula is the theorem part of the definition.
:::

:::lemma_ "lem:coefficient-isometry" (lean := "OperatorRidgelet.Paper.lem_coefficient_isometry_i, OperatorRidgelet.Paper.lem_coefficient_isometry_ii, OperatorRidgelet.Paper.lem_coefficient_isometry_iii, OperatorRidgelet.Paper.lem_coefficient_isometry_iv, OperatorRidgelet.Paper.def_spectral_coefficient, OperatorRidgelet.Paper.lem_coefficient_isometry_v") (uses := "def:spectral-coefficient, lem:homogeneous-mixture")
$`W_\rho:L^2(\nu_\alpha)\to L^2(\lambda_\alpha)` is well defined (i), independent of the Borel
representative of $`G` (ii), and
$`\|W_\rho G\|_{L^2(\lambda_\alpha)}^2=C_\rho^{(\alpha)}\|G\|_{L^2(\nu_\alpha)}^2` (iii). If
$`G\in L^1(\nu_\alpha)`, then $`\omega\mapsto G(-\omega a)` is integrable on compact subsets of
$`\mathbb R\setminus\{0\}` for $`\nu_\alpha`-almost every $`a` (iv), and the explicit formula
for $`\gamma_G` holds already for $`G\in L^2(\nu_\alpha)`, with absolute convergence on
almost every ray for every bias. In this notation the Fourier-slice identity reads
$`R_\rho f=W_\rho\,\mathcal G_Qf`.
:::

:::proof "lem:coefficient-isometry"
$`(a,\omega)\mapsto G(-\omega a)` is Borel, and the homogeneous change of variables with
Tonelli gives
$`\frac1{2\pi}\int\int|\widehat\rho(\omega)|^2|G(-\omega a)|^2\,\nu_\alpha(\mathrm da)\,\mathrm d\omega=C_\rho^{(\alpha)}\|G\|^2_{L^2(\nu_\alpha)}`;
the same computation with $`|G|` on a compact set gives local integrability, and the inverse
Fourier transform in $`\omega` for almost every $`a` gives the formula.
:::

:::lemma_ "lem:partial-fourier-l2" (lean := "OperatorRidgelet.Paper.lem_partial_fourier_l2, OperatorRidgelet.Paper.lem_partial_fourier_l2_uniqueness") (uses := "aux:conventions")
For a separable complex Hilbert space $`Y`, partial Fourier transformation in the bias is a
unitary map from $`L^2(\nu\otimes\mathrm dc;Y)` onto
$`L^2(\nu\otimes\mathrm d\omega/(2\pi);Y)`. Each transform admits a jointly strongly
measurable representative agreeing with the one-dimensional Plancherel transform on almost
every ray. Such representatives agree almost everywhere.
:::

:::proof "lem:partial-fourier-l2"
Apply the one-dimensional Fourier unitary to the fibers of the product $`L^2` space. Its
inverse on the fibers proves surjectivity; the product $`L^2` identification supplies joint
measurability. Fiberwise uniqueness and Fubini prove independence of the representative.
:::

:::lemma_ "lem:coefficient-adjoint" (lean := "OperatorRidgelet.Paper.lem_coefficient_adjoint_i, OperatorRidgelet.Paper.lem_coefficient_adjoint_ii, OperatorRidgelet.Paper.lem_coefficient_adjoint_iii") (uses := "lem:partial-fourier-l2, lem:coefficient-isometry")
For an admissible Schwartz filter and a sigma-finite homogeneous direction measure,
the backprojection is $`\Lambda_\rho=W_\rho^*`. It satisfies
$`\Lambda_\rho W_\rho=C_\rho^{(\alpha)}\mathrm{Id}` and
$`\|\Lambda_\rho\gamma\|_2\le\sqrt{C_\rho^{(\alpha)}}\|\gamma\|_2`.
Its ray formula is
$`\Lambda_\rho\gamma(\xi)=(2\pi)^{-1}\int\overline{\widehat\rho(\omega)}\widehat\gamma(-\xi/\omega,\omega)|\omega|^{-\alpha}\,\mathrm d\omega`;
this integral is absolutely convergent for almost every $`\xi` and is independent of the
jointly measurable Fourier representative.
:::

:::proof "lem:coefficient-adjoint"
Plancherel in the bias and the substitution $`\xi=-\omega a` identify the inner product
with the ray formula. Weighted Cauchy–Schwarz and Tonelli give its absolute convergence and
norm bound; polarization of the coefficient isometry gives the left inverse identity.
:::

# The Hilbert space

:::definition "def:spectral-space" (lean := "OperatorRidgelet.spectralCore, OperatorRidgelet.spectralInner, OperatorRidgelet.spectralRange, OperatorRidgelet.gaussFourierLp, OperatorRidgelet.spectralEmbed") (uses := "def:ridgelet-analysis, aux:gaussian-mixture")
$`\mathcal D_\alpha=\{f\in L^2(H,\mu_Q):\mathcal G_Qf\in L^2(H,\nu_\alpha)\}` with
$`\langle f,g\rangle_{\mathcal E_\alpha}=\int_H\mathcal G_Qf\,\overline{\mathcal G_Qg}\,\mathrm d\nu_\alpha`.
The Hilbert space $`\mathcal E_\alpha` is the completion of $`\mathcal D_\alpha` in this norm,
and $`\mathcal K_\alpha=\overline{\mathcal G_Q(\mathcal D_\alpha)}^{L^2(\nu_\alpha)}` is the
closure of the range of $`\mathcal G_Q` on $`\mathcal D_\alpha`. The formalization represents
$`\mathcal E_\alpha` by $`\mathcal K_\alpha` and the unitary $`U_\alpha` by the map
$`U:\mathcal D_\alpha\to\mathcal K_\alpha`, $`f\mapsto\mathcal G_Qf`.
:::

:::lemma_ "lem:spectral-unitary" (lean := "OperatorRidgelet.Paper.lem_spectral_unitary_i, OperatorRidgelet.Paper.lem_spectral_unitary_ii, OperatorRidgelet.Paper.lem_spectral_unitary_iii") (uses := "def:spectral-space, lem:homogeneous-mixture")
The spectral form is positive definite on $`\mathcal D_\alpha` (i), $`\mathcal G_Q` is an
isometry from $`(\mathcal D_\alpha,\langle\cdot,\cdot\rangle_{\mathcal E_\alpha})` into
$`\mathcal K_\alpha` (ii), and its image is dense (iii), so that $`\mathcal G_Q` extends
uniquely to a unitary $`U_\alpha:\mathcal E_\alpha\to\mathcal K_\alpha`.
:::

:::proof "lem:spectral-unitary"
If the norm of $`f\in\mathcal D_\alpha` vanishes, then $`\mathcal G_Qf=0` almost everywhere,
hence everywhere by continuity and full support of $`\nu_\alpha`; the Fourier transform
determines finite complex Borel measures on a separable Hilbert space, so $`f\mu_Q=0`.
:::

:::lemma_ "lem:gaussian-decay" (lean := "OperatorRidgelet.Paper.lem_gaussian_decay_i, OperatorRidgelet.Paper.lem_gaussian_decay_ii") (uses := "aux:centered-gaussian, lem:mixture-integration, def:spectral-space")
For every $`t>0`, $`\alpha>0`, and integer $`m\ge0`,
$`\int_H\|\xi\|^{2m}e^{-t\langle Q\xi,\xi\rangle}\,\nu_\alpha(\mathrm d\xi)<\infty` (i).
Consequently, if $`f\in L^2(\mu_Q)` and
$`|\mathcal G_Qf(\xi)|\le C(1+\|\xi\|)^pe^{-t\langle Q\xi,\xi\rangle/2}`, then
$`f\in\mathcal D_\alpha` for every $`\alpha>0` (ii).
:::

:::proof "lem:gaussian-decay"
On each Gaussian layer, Cauchy–Schwarz separates the polynomial factor, whose moments are
finite, from the Gaussian factor, whose integral is $`\prod_j(1+8st\theta_j)^{-1/2}` with
$`\theta_j>0` the eigenvalues of $`P^{1/2}QP^{1/2}`; retaining $`k>4m+2\alpha` factors makes
the mixture integral finite.
:::

:::proposition "ex:core-elements" (lean := "OperatorRidgelet.Paper.ex_core_elements_i, OperatorRidgelet.Paper.ex_core_elements_ii, OperatorRidgelet.Paper.ex_core_elements_iii, OperatorRidgelet.Paper.ex_core_elements_iv, OperatorRidgelet.Paper.ex_core_elements_v") (uses := "def:spectral-space, lem:gaussian-decay, aux:centered-gaussian, ex:closed-form, ex:operator-layer")
The constant function $`1` has $`\mathcal G_Q1(\xi)=e^{-\langle Q\xi,\xi\rangle/2}` (i), so
$`1\in\mathcal D_\alpha` for every $`\alpha>0` (ii) and $`\mathcal E_\alpha\ne\{0\}` (iii).
The non-cylindrical Gaussian target $`f_W(x)=e^{-\langle Wx,x\rangle/2}` of
{bpref "ex:closed-form"}[] belongs to every $`\mathcal D_\alpha` (iv), and so do the
components of the neural-operator layers with Gaussian activation of
{bpref "ex:operator-layer"}[] (v).
:::

:::proof "ex:core-elements"
The Gaussian characteristic functional gives $`\mathcal G_Q1`, and the decay lemma with
$`m=0`, $`p=0`, $`t=1` gives $`1\in\mathcal D_\alpha`; the other two assertions are proved with
the examples, using only the decay lemma and the Fourier-slice identity.
:::

# Plancherel identity, closed range, and injectivity

The formalization proves the Plancherel theory first for the abstract pair $`(\mu,\nu)`
(Appendix H) and then specializes to the Gaussian pair.

:::theorem "thm:general-weights" (lean := "OperatorRidgelet.Paper.thm_general_weights_plancherel_memLp, OperatorRidgelet.Paper.thm_general_weights_plancherel, OperatorRidgelet.Paper.thm_general_weights_extension, OperatorRidgelet.Paper.thm_general_weights_extension_norm, OperatorRidgelet.Paper.thm_general_weights_extension_closed_range, OperatorRidgelet.Paper.thm_general_weights_extension_coefficient, OperatorRidgelet.Paper.thm_general_weights_injective, OperatorRidgelet.Paper.thm_general_weights_one_mem_iff, OperatorRidgelet.Paper.thm_general_weights_dense, OperatorRidgelet.Paper.thm_general_weights_backprojection, OperatorRidgelet.Paper.thm_general_weights_stability") (uses := "aux:conventions, def:admissible-filter, def:ridgelet-analysis, lem:fourier-slice, lem:coefficient-isometry, def:spectral-space, lem:spectral-unitary")
Let $`\mu` be a Borel probability measure on $`H` and $`\nu` a $`\sigma`-finite Borel measure
with full support and $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for $`\omega\ne0`; define
$`\mathcal G_\mu`, $`\mathcal D_{\mu,\nu}`, and the completion $`\mathcal E_{\mu,\nu}` as in
the Gaussian case. Then the Fourier-slice identity, {bpref "thm:A"}[], {bpref "thm:B"}[], and
{bpref "thm:C"}[] (i)–(iii) remain valid with $`(\mu_Q,\nu_\alpha)` replaced by
$`(\mu,\nu)`: for $`f\in\mathcal D_{\mu,\nu}` the transform lies in $`L^2(\lambda)` and
satisfies the Plancherel identity, $`R_\rho` has a unique bounded extension of norm at most
$`(C^{(\alpha)}_\rho)^{1/2}` (with equality when the core is nonzero), with closed range and
$`R_\rho=W_\rho U`, and
$`R_\rho f=0` implies $`f=0`. Moreover $`1\in\mathcal D_{\mu,\nu}` if and only if
$`\int_H|\widehat\mu(\xi)|^2\nu(\mathrm d\xi)<\infty`. The abstract-weight versions of
{bpref "thm:A"}[] and {bpref "thm:C"}[] are the Lean statements of those theorems themselves.
The backprojection and coefficient stability results also hold. If, in addition, $`\nu` is
finite on bounded sets, the spectral-density construction gives compact-open universality.
Full support alone does not imply this local finiteness assumption. Gaussian decay and
Hermite inversion retain their Gaussian hypotheses.
:::

:::proof "thm:general-weights"
Since $`\mu` is finite, $`f\mu` is a finite complex measure and $`\mathcal G_\mu f` is
continuous; the proofs use only Fubini, the one-dimensional Plancherel and Parseval identities,
and the homogeneity substitution, which holds for $`\nu` by assumption. Completing
$`\mathcal D_{\mu,\nu}` makes $`\mathcal G_\mu` unitary onto the closure of its range, and
full support with Fourier uniqueness gives injectivity; finally $`\mathcal G_\mu1=\widehat\mu`.
:::

:::theorem "thm:B" (lean := "OperatorRidgelet.Paper.thm_B_i_a, OperatorRidgelet.Paper.thm_B_i_b, OperatorRidgelet.Paper.thm_B_ii_a, OperatorRidgelet.Paper.thm_B_ii_b, OperatorRidgelet.Paper.thm_B_ii_c, OperatorRidgelet.Paper.thm_B_ii_d, OperatorRidgelet.Paper.thm_B_iii") (uses := "def:admissible-filter, def:ridgelet-analysis, lem:fourier-slice, lem:homogeneous-mixture, lem:coefficient-isometry, def:spectral-space, lem:spectral-unitary, thm:general-weights")
Let $`\alpha>0`. (i) For $`f,g\in\mathcal D_\alpha` and $`\alpha`-admissible
$`\rho_1,\rho_2`, the transforms $`R_{\rho_1}f` and $`R_{\rho_2}g` belong to
$`L^2(\lambda_\alpha)`, and
$`\langle R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha)}=C_{\rho_1,\rho_2}^{(\alpha)}\langle f,g\rangle_{\mathcal E_\alpha}`.
(ii) An $`\alpha`-admissible $`\rho` determines a unique bounded extension
$`R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)` with
$`\|R_\rho f\|^2=C_\rho^{(\alpha)}\|f\|_{\mathcal E_\alpha}^2`; its range is closed, and
$`R_\rho=W_\rho U_\alpha`. (iii) If $`\rho` is $`\alpha`-admissible and
$`f\in L^1(H,\mu_Q)`, then $`R_\rho f=0` $`\lambda_\alpha`-almost everywhere implies $`f=0`
$`\mu_Q`-almost everywhere.
:::

:::proof "thm:B"
Apply the one-dimensional Plancherel identity in the bias to the Fourier-slice identity and
substitute $`\xi=-\omega a` by homogeneity; admissibility gives square integrability and
Cauchy–Schwarz justifies the cross identity. The norm identity extends $`R_\rho` to the
completion, an isometry up to a nonzero scalar has closed range, and
$`R_\rho=W_\rho U_\alpha` holds on the core and extends by continuity. For (iii), a fixed
frequency with $`\widehat\rho\ne0` and homogeneity give $`\mathcal G_Qf=0` almost everywhere,
and the argument of {bpref "lem:spectral-unitary"}[] finishes.
:::

# The finite-dimensional case and the dilation obstruction

:::definition "aux:finite-dim" (lean := "OperatorRidgelet.FiniteDim.mixtureConst, OperatorRidgelet.FiniteDim.directionMeasure, OperatorRidgelet.FiniteDim.frameConst, OperatorRidgelet.FiniteDim.fourier, OperatorRidgelet.FiniteDim.densityMeasure, OperatorRidgelet.FiniteDim.frameRepresentative, OperatorRidgelet.FiniteDim.fracLaplacian, OperatorRidgelet.strongLawSet") (uses := "aux:centered-gaussian")
On $`H=\mathbb R^m` with $`P=I` and $`0<\alpha<m`, the mixture is
$`\nu_\alpha(\mathrm da)=c_{m,\alpha}\|a\|^{\alpha-m}\,\mathrm da` with
$`c_{m,\alpha}=2^{-\alpha}\pi^{-m/2}\Gamma((m-\alpha)/2)` and $`k_{m,\alpha}=(2\pi)^mc_{m,\alpha}`;
for a Gaussian density $`p` and $`g=fp`, the frame representative is
$`t_f(x)=\int e^{i\langle x,\xi\rangle}\widehat g(\xi)\,\nu_\alpha(\mathrm d\xi)`, and
$`(-\Delta)^s` is the Fourier multiplier $`\|\xi\|^{2s}`. For the dilation obstruction, with
eigenvectors $`e_j` and eigenvalues $`w_j>0` of $`W`, the strong-law sets are
$`E_t=\{x:\lim_n\frac1n\sum_{j\le n}\langle x,e_j\rangle^2/w_j=t\}`.
:::

:::corollary "cor:finite-backprojection" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_i, OperatorRidgelet.Paper.cor_finite_backprojection_ii, OperatorRidgelet.Paper.cor_finite_backprojection_iii, OperatorRidgelet.Paper.cor_finite_backprojection_iv, OperatorRidgelet.Paper.cor_finite_backprojection_v, OperatorRidgelet.Paper.cor_finite_backprojection_vi") (uses := "aux:finite-dim, def:spectral-space, thm:B, thm:C")
Let $`H=\mathbb R^m`, $`0<\alpha<m`, and let $`p` be a nondegenerate Gaussian density. If
$`f\in L^2(p\,\mathrm dx)` with $`g=fp\in\mathcal S(\mathbb R^m)`, then $`f\in\mathcal D_\alpha`
(i) and $`t_f=k_{m,\alpha}(-\Delta)^{-(m-\alpha)/2}g` (ii). For a band-pass $`\rho`, the
synthesis $`S_\rho R_\rho f` is represented against $`p\,\mathrm dx` by
$`C_\rho^{(\alpha)}t_f` (iii), so that, distributionally,
$`f=\frac{p^{-1}}{k_{m,\alpha}C_\rho^{(\alpha)}}(-\Delta)^{(m-\alpha)/2}S_\rho R_\rho f` (iv).
With Lebesgue direction measure and $`\alpha=m`, $`t_f=(2\pi)^mg` (v) and
$`f=(2\pi)^{-m}(C_\rho^{(m)})^{-1}p^{-1}S_\rho R_\rho f` (vi).
:::

:::proof "cor:finite-backprojection"
Here $`\mathcal G_Qf=\widehat g`, the weight $`\|\xi\|^{\alpha-m}` is locally integrable, and
Fourier inversion gives $`\widehat{t_f}=k_{m,\alpha}\|\xi\|^{\alpha-m}\widehat g`; Fubini
identifies $`\int t_f\overline h\,p\,\mathrm dx` with $`\langle f,h\rangle_{\mathcal E_\alpha}`,
which is the frame-operator representation of {bpref "thm:C"}[] (iii).
:::

:::proposition "prop:dilation-obstruction" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_i_a, OperatorRidgelet.Paper.prop_dilation_obstruction_i_b, OperatorRidgelet.Paper.prop_dilation_obstruction_i_c, OperatorRidgelet.Paper.prop_dilation_obstruction_i_d, OperatorRidgelet.Paper.prop_dilation_obstruction_ii") (uses := "aux:finite-dim, aux:centered-gaussian, roadmap:gaussian-strong-law")
Let $`\dim H=\infty` and let $`W` be injective, positive, self-adjoint, and trace class with
eigenvectors $`e_j` and eigenvalues $`w_j>0`. The sets $`E_t`, $`t>0`, are Borel (i a) and
pairwise disjoint (i b), $`\mathcal N(0,tW)(E_t)=1` (i c), and consequently a
$`\sigma`-finite measure dominates $`\mathcal N(0,tW)` for at most countably many $`t` (i d).
Hence, for a bounded Borel $`r` with $`\{r\ne0\}` of positive measure, there is no finite
complex Borel measure $`\Gamma` on $`H\times\mathbb R` whose bias slices satisfy
$`\int_{E\times\mathbb R}e^{i\omega c}\,\Gamma(\mathrm da,\mathrm dc)=r(\omega)(D_{1/\omega})_\#\mathcal N(0,W)(E)`
for almost every $`\omega\ne0` (ii).
:::

:::proof "prop:dilation-obstruction"
The strong law of large numbers for the independent normalized Gaussian coordinates gives
$`\mathcal N(0,tW)(E_t)=1`, a $`\sigma`-finite measure has at most countably many disjoint
sets of positive measure, and a measure $`\Gamma` as in (ii) would give a finite measure
dominating $`\mathcal N(0,W/\omega^2)` for uncountably many $`\omega`.
:::

# Explicit admissible filters

:::definition "aux:explicit-filters" (lean := "OperatorRidgelet.Filters.bump, OperatorRidgelet.Filters.bandPassHat, OperatorRidgelet.Filters.bandPassFun, OperatorRidgelet.Filters.bandPass, OperatorRidgelet.Filters.mexicanHatFun, OperatorRidgelet.Filters.mexicanHat") (uses := "aux:conventions")
With the bump $`\eta(u)=\exp(-1/(1-u^2))` for $`|u|<1` and $`0` otherwise, the band-pass
filter $`\rho_{\mathrm{bp}}` is the real even Schwartz function with
$`\widehat\rho_{\mathrm{bp}}(\omega)=-\eta(2|\omega|-3)`, obtained by Fourier inversion; the
Mexican hat is $`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}`. Both are taken as Schwartz maps by
choice, with junk value $`0` should the explicit function fail to be Schwartz.
:::

:::proposition "ex:bandlimited-filter" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_i, OperatorRidgelet.Paper.ex_bandlimited_filter_ii, OperatorRidgelet.Paper.ex_bandlimited_filter_iii, OperatorRidgelet.Paper.ex_bandlimited_filter_iv, OperatorRidgelet.Paper.ex_bandlimited_filter_v, OperatorRidgelet.Paper.ex_bandlimited_filter_vi, OperatorRidgelet.Paper.ex_bandlimited_filter_vii, OperatorRidgelet.Paper.ex_bandlimited_filter_viii, OperatorRidgelet.Paper.ex_bandlimited_filter_ix, OperatorRidgelet.Paper.ex_bandlimited_filter_x") (uses := "aux:explicit-filters, def:admissible-filter, aux:conventions")
$`\widehat\rho_{\mathrm{bp}}` is smooth (i), nonpositive (ii), nonzero (iii), and supported in
$`\{1\le|\omega|\le2\}` (iv), so $`\rho_{\mathrm{bp}}\in\mathcal S(\mathbb R)` is real (v)
and even (vi) with the prescribed Fourier transform (vii), satisfies the band-pass condition
(viii), and is $`\alpha`-admissible for every $`\alpha>0` (ix); multiplying by
$`(C_{\rho_{\mathrm{bp}}}^{(\alpha)})^{-1/2}` normalizes the admissibility constant to one (x).
The sign makes it admissible for ReLU synthesis in the sense of {bpref "cor:relu-admissible"}[].
:::

:::proof "ex:bandlimited-filter"
The bump and all its derivatives vanish at $`|u|=1`, the support stays away from
$`\omega=0`, Fourier inversion maps $`C_c^\infty` into $`\mathcal S`, even real Fourier data
give an even real inverse, and on the compact support $`|\omega|^{-\alpha}` is bounded above
and below.
:::

:::proposition "ex:mexican-hat" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_i, OperatorRidgelet.Paper.ex_mexican_hat_ii, OperatorRidgelet.Paper.ex_mexican_hat_iii, OperatorRidgelet.Paper.ex_mexican_hat_iv, OperatorRidgelet.Paper.ex_mexican_hat_v, OperatorRidgelet.Paper.ex_mexican_hat_vi") (uses := "aux:explicit-filters, def:admissible-filter, aux:conventions")
$`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}` is a Schwartz function (i) with
$`\widehat\rho_{\mathrm{MH}}(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}` (ii). It is
$`\alpha`-admissible exactly for $`0<\alpha<5` (iii), with
$`C_{\rho_{\mathrm{MH}}}^{(\alpha)}=\Gamma((5-\alpha)/2)` (iv) and
$`C_{\rho_{\mathrm{MH}}}^{(1)}=1` (v). It is not band pass (vi), so {bpref "thm:B"}[] applies
to it but {bpref "thm:A"}[] and {bpref "thm:tempered-reconstruction"}[] do not.
:::

:::proof "ex:mexican-hat"
With $`g(t)=e^{-t^2/2}`, $`\rho_{\mathrm{MH}}=-g''` and the differentiation rule gives the
Fourier transform; then
$`C_{\rho_{\mathrm{MH}}}^{(\alpha)}=\int_{\mathbb R}|\omega|^{4-\alpha}e^{-\omega^2}\mathrm d\omega=\Gamma((5-\alpha)/2)`,
convergent at zero exactly when $`\alpha<5`.
:::
