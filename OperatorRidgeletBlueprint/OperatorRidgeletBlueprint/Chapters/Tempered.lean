import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Tempered
import OperatorRidgelet.Paper.Sobolev

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Tempered synthesis activations and ReLU" =>
%%%
file := "tempered"
%%%

This chapter is Section 5 of the manuscript together with Appendix C. The analysis filter
$`\rho` is a Schwartz function, but the activation that synthesizes a network may be unbounded;
a real $`\beta\in\mathcal S'(\mathbb R)` is paired with the band-pass filter through the
distributional constant
$`C_{\beta,\rho}^{(\alpha)}=\frac1{2\pi}\langle\widehat\beta,\widehat\rho(-\,\cdot\,)|\cdot|^{-\alpha}\rangle`
of {bpref "aux:tempered-activation"}[], which is well defined because $`\widehat\rho`
vanishes near the origin. The weighted Sobolev activation spaces
$`\mathcal A_{s,t}=\langle\cdot\rangle^tH^s(\mathbb R)`, in which this pairing is continuous,
are recalled from Appendix C.

# Regularized synthesis

:::definition "aux:tempered-distributions" (lean := "OperatorRidgelet.IsPolynomialDistribution, OperatorRidgelet.schwartzOfFun, OperatorRidgelet.tanhDistribution, OperatorRidgelet.gaussianCdfDistribution, OperatorRidgelet.gaussianDistribution") (uses := "aux:conventions")
A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` is a polynomial, equivalently
$`\beta=0` in $`\mathcal S'/\mathcal P`, when it acts by integration against some polynomial.
The Schwartz function with prescribed values is obtained by choice when one exists. The
standard activations $`\tanh`, the Gaussian distribution function $`\Phi`, and the Gaussian
$`e^{-u^2/2}` are realized as tempered distributions acting by integration against the
function; ReLU is treated in {bpref "cor:relu-admissible"}[].
:::

:::definition "def:regularized-synthesis" (lean := "OperatorRidgelet.IsRealDistribution, OperatorRidgelet.IsCutoff, OperatorRidgelet.IsApproximateIdentity, OperatorRidgelet.distributionConvolution, OperatorRidgelet.regularizedSpectrum, OperatorRidgelet.regularizedActivation, OperatorRidgelet.regularizedSynthesis, OperatorRidgelet.temperedSynthesis, OperatorRidgelet.Paper.def_regularized_synthesis_i, OperatorRidgelet.Paper.def_regularized_synthesis_ii, OperatorRidgelet.Paper.def_regularized_synthesis_iii, OperatorRidgelet.Paper.def_regularized_synthesis_iv, OperatorRidgelet.Paper.def_regularized_synthesis_v, OperatorRidgelet.Paper.def_regularized_synthesis_vi") (uses := "def:admissible-filter, aux:conventions, aux:tempered-distributions, aux:frame-operator, thm:B")
Let $`\beta\in\mathcal S'(\mathbb R)` be real, that is, fixed by distributional conjugation,
and let $`\rho` be a band-pass filter. Choose an even $`\chi\in C_c^\infty(\mathbb R\setminus\{0\})`
equal to one on a neighbourhood of $`\operatorname{supp}\widehat\rho` (i) and an even,
compactly supported, smooth approximate identity $`(\eta_\varepsilon)_{\varepsilon>0}` (ii),
and define the real Schwartz functions $`\beta_\varepsilon` by
$`\widehat{\beta_\varepsilon}=\chi\,(\widehat\beta*\eta_\varepsilon)\in C_c^\infty(\mathbb R\setminus\{0\})`
(iii–v: membership, existence, and uniqueness of $`\beta_\varepsilon`). For
$`\gamma\in\operatorname{Ran}R_\rho`, the regularized synthesis is
$`S_{\beta_\varepsilon}\gamma=R_{\beta_\varepsilon}'\gamma\in\mathcal E_\alpha'` (vi), and
the synthesis with $`\beta` is $`S_\beta\gamma=\lim_{\varepsilon\downarrow0}S_{\beta_\varepsilon}\gamma`
in $`\mathcal E_\alpha'`, whenever the limit exists.
:::

:::theorem "thm:tempered-reconstruction" (lean := "OperatorRidgelet.Paper.thm_tempered_reconstruction_i, OperatorRidgelet.Paper.thm_tempered_reconstruction_ii, OperatorRidgelet.Paper.thm_tempered_reconstruction_iii, OperatorRidgelet.Paper.thm_tempered_reconstruction_iv, OperatorRidgelet.Paper.thm_tempered_reconstruction_v, OperatorRidgelet.Paper.thm_tempered_reconstruction_vi") (uses := "def:regularized-synthesis, aux:tempered-activation, thm:B, thm:C, thm:A")
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

:::proof "thm:tempered-reconstruction"
Each $`\beta_\varepsilon` is an admissible real filter, so the Plancherel identity gives
$`S_{\beta_\varepsilon}R_\rho f=C_{\beta_\varepsilon,\rho}^{(\alpha)}T_\alpha f`;
distributional convergence of $`\widehat\beta*\eta_\varepsilon` against the fixed test
function $`\widehat\rho(-\omega)|\omega|^{-\alpha}` gives convergence of the constants, and
$`T_\alpha` is an isometry, so the functionals converge in $`\mathcal E_\alpha'`. The
existence of $`\rho` with nonzero constant is the last step of the proof of
{bpref "thm:A"}[].
:::

:::corollary "cor:relu-admissible" (lean := "OperatorRidgelet.reluDistribution, OperatorRidgelet.reluAdmissibilityScale, OperatorRidgelet.reluNormalizedFilter, OperatorRidgelet.Paper.cor_relu_admissible_i, OperatorRidgelet.Paper.cor_relu_admissible_ii, OperatorRidgelet.Paper.cor_relu_admissible_iii, OperatorRidgelet.Paper.cor_relu_admissible_iv, OperatorRidgelet.Paper.cor_relu_admissible_v, OperatorRidgelet.Paper.cor_relu_admissible_vi, OperatorRidgelet.Paper.cor_relu_admissible_vii, OperatorRidgelet.Paper.cor_relu_admissible_viii") (uses := "thm:tempered-reconstruction, thm:A, def:admissible-filter, aux:tempered-activation, def:ray-regular")
Let $`\beta=\operatorname{ReLU}`, $`\operatorname{ReLU}(t)=\max(t,0)`. Then
$`\widehat{\operatorname{ReLU}}=-\operatorname{fp}(\omega^{-2})+i\pi\delta_0'` (i), which
equals $`-\omega^{-2}` away from the origin (ii). If
$`\widehat\rho\in C_c^\infty(\mathbb R\setminus\{0\})` is nonzero, even, and nonpositive, then
$`C_{\operatorname{ReLU},\rho}^{(\alpha)}=-\frac1{2\pi}\int_{\mathbb R}\widehat\rho(\omega)|\omega|^{-\alpha-2}\,\mathrm d\omega`
(iii), which is positive (iv). After rescaling $`\rho` the constant is one (v), and the two
reconstruction formulas of {bpref "thm:tempered-reconstruction"}[] (vi, vii) and
{bpref "thm:A"}[] (iii) (viii) hold with ReLU synthesis for every $`\alpha>0`.
:::

:::proof "cor:relu-admissible"
From $`\operatorname{ReLU}(t)=(|t|+t)/2`, the identities $`\widehat{|t|}=-2\operatorname{fp}(\omega^{-2})`
and $`\widehat t=2\pi i\delta_0'` give the Fourier transform; the test function is supported
away from zero, so the $`\delta_0'` term vanishes and the finite part is ordinary
multiplication by $`\omega^{-2}`, and evenness and the sign of $`\widehat\rho` give the
constant.
:::

# Weighted Sobolev activation spaces and standard activations

Write $`\langle u\rangle=(1+u^2)^{1/2}` and let $`B^q` be the Bessel operator on the frequency
variable. For $`s\in\mathbb R` and $`t\ge0`, the weighted Sobolev activation space is
$`\mathcal A_{s,t}=\langle\cdot\rangle^tH^s(\mathbb R)\subset\mathcal S'(\mathbb R)` with
$`\|\beta\|_{\mathcal A_{s,t}}=\|\langle\omega\rangle^sB^{-t}\widehat\beta\|_{L^2}`, and the
dual test norm is $`\|r\|_{\mathcal H^\sharp_{s,t}}=\|\langle\omega\rangle^{-s}B^tr\|_{L^2}`
for $`r\in\mathcal S(\mathbb R)`.

:::lemma_ "lem:weighted-duality" (lean := "OperatorRidgelet.activationFourierCoordinate, OperatorRidgelet.activationCoordinate, OperatorRidgelet.activationNorm, OperatorRidgelet.testFilterCoordinate, OperatorRidgelet.testFilterNorm, OperatorRidgelet.Paper.lem_weighted_duality_i, OperatorRidgelet.Paper.lem_weighted_duality_ii, OperatorRidgelet.Paper.lem_weighted_duality_iii, OperatorRidgelet.Paper.lem_weighted_duality_iv, OperatorRidgelet.Paper.lem_weighted_duality_v") (uses := "aux:conventions, aux:tempered-distributions")
The map $`\beta\mapsto\langle\omega\rangle^sB^{-t}\widehat\beta` is an isometric isomorphism
$`\mathcal A_{s,t}\to L^2(\mathbb R)`: the coordinate is represented by an $`L^2` function
(i), the map is injective (ii) and onto (iii). Moreover
$`|\frac1{2\pi}\langle\widehat\beta,r\rangle|\le\frac1{2\pi}\|\beta\|_{\mathcal A_{s,t}}\|r\|_{\mathcal H^\sharp_{s,t}}`
(iv), so the pairing extends to the completion of the test filters in
$`\mathcal H^\sharp_{s,t}` (v).
:::

:::proof "lem:weighted-duality"
$`\beta=\langle\cdot\rangle^t\mathcal F^{-1}[\langle\omega\rangle^{-s}g]` is a preimage of
$`g\in L^2`; the multiplier $`\langle u\rangle^t` is real and even, so $`B^t` is symmetric
for the bilinear pairing, the identity
$`\langle\widehat\beta,r\rangle=\int(\langle\omega\rangle^sB^{-t}\widehat\beta)(\langle\omega\rangle^{-s}B^tr)\,\mathrm d\omega`
extends by density, and Cauchy–Schwarz proves the bound.
:::

:::lemma_ "lem:standard-activation-class" (lean := "OperatorRidgelet.MemActivationSpaceFun, OperatorRidgelet.gaussianCdf, OperatorRidgelet.gaussianFun, OperatorRidgelet.weightedDistribution, OperatorRidgelet.Paper.lem_standard_activation_class_relu_mem, OperatorRidgelet.Paper.lem_standard_activation_class_relu_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_relu_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_mem, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_mem, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_mem, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_exists_filter") (uses := "lem:weighted-duality, aux:tempered-distributions, thm:A")
ReLU, $`\tanh`, the Gaussian distribution function
$`\Phi(u)=\int_{-\infty}^u(2\pi)^{-1/2}e^{-v^2/2}\,\mathrm dv`, and $`e^{-u^2/2}` belong to
$`\mathcal A_{0,2}=\langle\cdot\rangle^2L^2(\mathbb R)`, are globally Lipschitz, and are not
polynomials (twelve claims). For every non-polynomial real $`\beta\in\mathcal S'` there is a
real band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}=1`.
:::

:::proof "lem:standard-activation-class"
Membership in $`\mathcal A_{0,2}` means $`\langle u\rangle^{-2}\beta\in L^2`; three of the
functions are bounded and ReLU satisfies $`\int_0^\infty u^2(1+u^2)^{-2}\mathrm du<\infty`.
Their derivatives are bounded wherever defined, the bounded functions are nonconstant and ReLU
is not smooth at zero, and the last statement is the final part of the proof of
{bpref "thm:A"}[] followed by rescaling $`\rho`.
:::

:::proposition "ex:standard-activations" (lean := "OperatorRidgelet.Paper.lem_standard_activation_class_relu_mem, OperatorRidgelet.Paper.lem_standard_activation_class_relu_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_relu_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_mem, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_tanh_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_mem, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_mem, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_lipschitz, OperatorRidgelet.Paper.lem_standard_activation_class_gaussian_not_polynomial, OperatorRidgelet.Paper.ex_standard_activations_relu, OperatorRidgelet.Paper.ex_standard_activations_tanh, OperatorRidgelet.Paper.ex_standard_activations_gaussianCdf, OperatorRidgelet.Paper.ex_standard_activations_gaussian") (uses := "lem:standard-activation-class, thm:tempered-reconstruction, thm:A, thm:E")
ReLU, $`\tanh`, the Gaussian distribution function, and the Gaussian $`e^{-u^2/2}` are
globally Lipschitz, are not polynomials, and belong to $`\mathcal A_{0,2}`. Each of them is
therefore covered by {bpref "thm:tempered-reconstruction"}[], by {bpref "thm:A"}[] (iii), and
by the finite-width bounds of {bpref "thm:E"}[]; the Lean instance of this coverage is that for
every $`\alpha>0` there is a band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}\ne0` for each
of the four activations.
:::

:::proof "ex:standard-activations"
The three properties are {bpref "lem:standard-activation-class"}[]; a globally Lipschitz
function has polynomial growth, so {bpref "thm:A"}[] (iii) and {bpref "thm:E"}[] apply.
:::

# Weak Sobolev regularity along rays

:::lemma_ "lem:sobolev-tools" (lean := "OperatorRidgelet.bracket, OperatorRidgelet.MemRaySobolev, OperatorRidgelet.raySobolevNorm, OperatorRidgelet.rayProfile, OperatorRidgelet.sobolevMomentConst, OperatorRidgelet.Paper.lem_sobolev_tools_i, OperatorRidgelet.Paper.lem_sobolev_tools_ii, OperatorRidgelet.Paper.lem_sobolev_tools_iii, OperatorRidgelet.Paper.lem_sobolev_tools_iv") (uses := "aux:conventions")
Write $`H^s_\omega(\mathbb R;Y)` for the profiles $`h` whose inverse Fourier transform
$`\gamma=\check h` satisfies $`\|h\|_{H^s_\omega}^2=2\pi\int\langle
t\rangle^{2s}\|\gamma(t)\|^2\,\mathrm dt<\infty`. For $`s>1/2` and $`0\le r<s-1/2`,
$`\int\langle t\rangle^r\|\gamma(t)\|\,\mathrm dt\le A_{s,r}\|h\|_{H^s_\omega}` with
$`A_{s,r}=(2\pi)^{-1/2}(\int(1+t^2)^{-(s-r)}\mathrm dt)^{1/2}`. Reflection $`Rh(\omega)=h(-\omega)`
is an isometry, $`\|M_uh\|_{H^s_\omega}\le(1+|u|)^s\|h\|_{H^s_\omega}` for the modulation
$`M_uh(\omega)=e^{iu\omega}h(\omega)`, and $`(u,h)\mapsto M_uh` is jointly continuous.
:::

:::proof "lem:sobolev-tools"
The weighted $`L^1` bound is Cauchy--Schwarz applied to $`\langle t\rangle^{-(s-r)}` and
$`\langle t\rangle^{s}\|\gamma(t)\|`, the scalar factor being integrable exactly when
$`s-r>1/2`. Reflection and modulation correspond to $`\gamma(-\cdot)` and $`\gamma(\cdot+u)` on
the coefficient side, and $`\langle t-u\rangle\le(1+|u|)\langle t\rangle` gives the modulation
bound. Joint continuity reduces, by that bound and the triangle inequality, to the strong
continuity of translation, which follows from the strong continuity of translation in $`L^2`
and dominated convergence for the multiplier
$`(\langle t\rangle/\langle t+u\rangle)^s`.
:::

:::lemma_ "lem:sobolev-pairing" (lean := "OperatorRidgelet.sobolevPairing, OperatorRidgelet.sobolevPairingConst, OperatorRidgelet.Paper.lem_sobolev_pairing_i, OperatorRidgelet.Paper.lem_sobolev_pairing_ii, OperatorRidgelet.Paper.lem_sobolev_pairing_iii") (uses := "lem:sobolev-tools")
Let $`\sigma` be continuous with $`|\sigma(t)|\le C_\sigma(1+|t|)^p`, $`p\ge0`, and
$`s>p+1/2`, and put $`b_{\sigma,s}=\|\langle\cdot\rangle^{-s}\sigma\|_2`, which is finite. The
pairing $`L_\sigma^Y(h)=\int\sigma(t)\check h(-t)\,\mathrm dt` converges absolutely and
satisfies $`\|L_\sigma^Y(h)\|\le(2\pi)^{-1/2}b_{\sigma,s}\|h\|_{H^s_\omega}`, so it is the
bounded extension of $`(2\pi)^{-1}\langle\widehat\sigma,\cdot\rangle` to $`H^s_\omega`.
Moreover $`\int\sigma(u-b)\gamma(b)\,\mathrm db=L_\sigma^Y(M_uh)`.
:::

:::proof "lem:sobolev-pairing"
$`1+|t|\le\sqrt2\langle t\rangle` turns the growth bound into
$`\langle t\rangle^{-s}|\sigma(t)|\le C_\sigma2^{p/2}\langle t\rangle^{p-s}`, whose square is
integrable for $`s-p>1/2`. Weighted Cauchy--Schwarz against
{bpref "lem:sobolev-tools"}[] gives absolute convergence and the bound, the reflection isometry
turning $`\|\gamma(-\cdot)\|` into $`\|h\|_{H^s_\omega}`. The translation formula is the change
of variables $`b=u-t`.
:::

:::theorem "thm:weak-sobolev-synthesis" (lean := "OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_i, OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_ii, OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_iii, OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_iv, OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_v") (uses := "lem:sobolev-tools, lem:sobolev-pairing, def:admissible-filter, aux:conventions")
Let $`\nu` be homogeneous of degree $`\alpha>0`, $`\rho\in\mathcal S(\mathbb R)` with
$`0<C^{(\alpha)}_\rho<\infty`, $`\sigma` continuous with $`|\sigma(t)|\le
C_\sigma(1+|t|)^p` and $`s>p+1/2`, and $`g:H\to Y` strongly measurable. Suppose the rays
$`h_a(\omega)=\widehat\rho(-\omega)g(\omega a)` lie in $`H^s_\omega(\mathbb R;Y)` with a jointly
measurable coefficient and $`\mathfrak B_s(\rho,g)=\int(1+\|a\|)^s\|h_a\|_{H^s_\omega}\,\mathrm
d\nu<\infty`, and that $`q_{\alpha,\rho}(\omega)=\widehat\rho(-\omega)|\omega|^{-\alpha}` lies in
$`H^s_\omega(\mathbb R)`. Then for $`0\le r<s-1/2`
$`\int(1+\|a\|+|b|)^r\|\gamma_g\|\le2^{r/2}A_{s,r}\mathfrak B_s(\rho,g)`, the coefficient measure
is finite, and the ordinary absolutely convergent synthesis satisfies
$`S_\sigma[\Gamma_g](x)=C^{(\alpha)}_{\sigma,\rho}f_g(x)` with
$`C^{(\alpha)}_{\sigma,\rho}=(2\pi)^{-1}\langle\widehat\sigma,q_{\alpha,\rho}\rangle`, uniformly
absolutely on bounded input sets and continuously in $`x`.
:::

:::proof "thm:weak-sobolev-synthesis"
The moments are the weighted $`L^1` estimate of {bpref "lem:sobolev-tools"}[] on each ray,
$`1+\|a\|+|b|\le\sqrt2(1+\|a\|)\langle b\rangle`, and Tonelli; the case $`r=0` gives the finite
variation, and the growth bound of $`\sigma` with $`r=p` gives the absolute convergence and the
majorant. For the identity, the bias translation formula of {bpref "lem:sobolev-pairing"}[] and
Fubini turn the synthesis into $`\int\sigma(t)\Psi(t)\,\mathrm dt` with
$`\Psi(t)=\int\gamma_g(a,\langle a,x\rangle-t)\,\mathrm d\nu`. Fubini again computes the profile
of the integrable $`\Psi`, which homogeneity identifies with
$`\widehat\rho(\omega)|\omega|^{-\alpha}f_g(x)` off the origin, hence everywhere by continuity;
the $`L^1` uniqueness of the profile then identifies $`\Psi` with
$`\check q_{\alpha,\rho}(-\cdot)f_g(x)`, and the pairing gives the constant. Continuity is
dominated convergence with the majorant.
:::

# Non-band-pass filters for Sobolev synthesis

:::proposition "prop:nonbandpass-sobolev" (lean := "OperatorRidgelet.gaussDerivFilter, OperatorRidgelet.gaussTarget, OperatorRidgelet.gaussRayCoefficient, OperatorRidgelet.gaussSobolevRay, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_i, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_ii, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_iii, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_iv, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_v, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_vi, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_vii, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_viii, OperatorRidgelet.Paper.prop_nonbandpass_sobolev_ix") (uses := "thm:weak-sobolev-synthesis, lem:sobolev-tools, def:admissible-filter, aux:conventions")
Let $`\nu` be homogeneous of degree $`\alpha>0` and finite on the unit ball, fix $`s>1/2` and an
integer $`k\ge1` with $`2k>\alpha+2s-1/2`, and let
$`\widehat\rho_k(\omega)=\omega^{2k}e^{-\omega^2}`, $`g(\xi)=e^{-\|\xi\|^2}v`. Then $`\rho_k` is
a real Schwartz filter (i) that is not band pass (ii) but is $`\alpha`-admissible for
$`\alpha<4k+1` (iii). The homogeneous moments $`\int(1+\|a\|^2)^{-d/2}\mathrm d\nu` are finite
for $`d>\alpha` (iv); the coefficient of the rays is jointly measurable (v), each ray lies in
$`H^s_\omega` with profile $`\widehat\rho_k(-\omega)g(\omega a)` (vi), and
$`\mathfrak B_s(\rho_k,g)<\infty` (vii). The Sobolev test $`q_{\alpha,\rho_k}` lies in
$`H^s_\omega` (viii). Hence {bpref "thm:weak-sobolev-synthesis"}[] applies to this filter for
every continuous activation of growth order $`p<s-1/2` (ix).
:::

:::proof "prop:nonbandpass-sobolev"
The symbol is a polynomial times a Gaussian, hence Schwartz, and real and even, so its inverse
angular transform is a real Schwartz function. It vanishes only at the origin, which is
therefore in the closed support, so the filter is not band pass, while
$`|\widehat\rho_k|^2|\omega|^{-\alpha}=|\omega|^{4k-\alpha}e^{-2\omega^2}` is integrable exactly
for $`4k-\alpha>-1`. Homogeneity scales balls, $`\nu(B_R)=R^\alpha\nu(B_1)`, and the dyadic
annuli give a geometric series, which is the moment bound. Writing
$`A=(1+\|a\|^2)^{1/2}`, the ray with profile $`\omega^{2k}e^{-A^2\omega^2}v` has coefficient
$`A^{-2k-1}\rho_k(b/A)v`, a dilate of a Schwartz function, so it lies in every $`H^s_\omega`,
with $`\|h_a\|_{H^s_\omega}\le\|v\|\,\|h_0\|_{H^s_\omega}A^{s-2k-1/2}`;
$`1+\|a\|\le\sqrt2A` and the moment bound give $`\mathfrak B_s<\infty` exactly in the stated
range. For the Sobolev test, the Gamma integral
$`|\omega|^{-\alpha}=\Gamma(\alpha/2)^{-1}\int_0^\infty u^{\alpha/2-1}e^{-u\omega^2}\mathrm du`
writes $`q_{\alpha,\rho_k}` as a superposition of the same symbols at the scales
$`(1+u)^{1/2}`; Fubini gives its profile, and Cauchy--Schwarz against the finite weight
$`u^{\alpha/2-1}(1+u)^{(s-2k-1/2)/2}` together with Tonelli reduces its Sobolev norm to the
norms of the dilated filters.
:::
