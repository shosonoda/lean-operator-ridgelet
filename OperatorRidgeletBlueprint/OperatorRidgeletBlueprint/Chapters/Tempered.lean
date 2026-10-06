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

The synthesis activation may be a tempered distribution, including ReLU. Weighted Sobolev spaces make the Fourier pairing continuous; we define them and prove their duality before using regularized synthesis. The later inverse Fourier estimates give an absolutely convergent network integral under Sobolev conditions, with an explicit example of filters that are not band pass.

# Weighted Sobolev activation spaces

:::definition "aux:tempered-distributions" (lean := "OperatorRidgelet.IsPolynomialDistribution, OperatorRidgelet.schwartzOfFun, OperatorRidgelet.tanhDistribution, OperatorRidgelet.gaussianCdfDistribution, OperatorRidgelet.gaussianDistribution") (uses := "aux:conventions")
This is the common distributional setup of Section 5. Polynomiality enters Lemma 5.2
and Theorem 5.4, the realizations of standard activations enter Lemma 5.2, and
the choice of a Schwartz representative enters Definition 5.3.

A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` is a polynomial, equivalently
$`\beta=0` in $`\mathcal S'/\mathcal P`, when it acts by integration against some polynomial.
The Schwartz function with prescribed values is obtained by choice when one exists. The
standard activations $`\tanh`, the Gaussian distribution function $`\Phi`, and the Gaussian
$`e^{-u^2/2}` are realized as tempered distributions acting by integration against the
function; ReLU is treated in {bpref "cor:5.5"}[].
:::

Write $`\langle u\rangle=(1+u^2)^{1/2}` and $`B^qv=F_{\mathbb R}[\langle\cdot\rangle^qF_{\mathbb R}^{-1}v]`. For $`s\in\mathbb R`, $`t\ge0`, define $`\mathcal A_{s,t}=\langle\cdot\rangle^tH^s(\mathbb R)` with norm $`\|\beta\|_{\mathcal A_{s,t}}=\|\langle\omega\rangle^sB^{-t}\beta^\sharp\|_2`, and the test norm $`\|r\|_{\mathcal T^\sharp_{s,t}}=\|\langle\omega\rangle^{-s}B^tr\|_2`. Membership controls distributional pairings; a continuous pointwise representative remains a separate assumption.

:::lemma_ "lem:5.1" (lean := "OperatorRidgelet.activationFourierCoordinate, OperatorRidgelet.activationCoordinate, OperatorRidgelet.activationNorm, OperatorRidgelet.testFilterCoordinate, OperatorRidgelet.testFilterNorm, OperatorRidgelet.Paper.lem_5_1_i, OperatorRidgelet.Paper.lem_5_1_ii, OperatorRidgelet.Paper.lem_5_1_iii, OperatorRidgelet.Paper.lem_5_1_iv, OperatorRidgelet.Paper.lem_5_1_v") (uses := "aux:conventions, aux:tempered-distributions")
The map $`\beta\mapsto\langle\omega\rangle^sB^{-t}\beta^\sharp` is an isometric isomorphism
$`\mathcal A_{s,t}\to L^2(\mathbb R)`: the coordinate is represented by an $`L^2` function
(i), the map is injective (ii) and onto (iii). Moreover
$`|\frac1{2\pi}\langle\beta^\sharp,r\rangle|\le\frac1{2\pi}\|\beta\|_{\mathcal A_{s,t}}\|r\|_{\mathcal T^\sharp_{s,t}}`
(iv), so the pairing extends to the completion of the test filters in
$`\mathcal T^\sharp_{s,t}` (v).
:::

:::proof "lem:5.1"
$`\beta=\langle\cdot\rangle^tF_{\mathbb R}^{-1}[\langle\omega\rangle^{-s}g]` is a preimage of
$`g\in L^2`; the multiplier $`\langle u\rangle^t` is real and even, so $`B^t` is symmetric
for the bilinear pairing, the identity
$`\langle\beta^\sharp,r\rangle=\int(\langle\omega\rangle^sB^{-t}\beta^\sharp)(\langle\omega\rangle^{-s}B^tr)\,\mathrm d\omega`
extends by density, and Cauchy–Schwarz proves the bound.
:::

:::lemma_ "lem:5.2" (lean := "OperatorRidgelet.MemActivationSpaceFun, OperatorRidgelet.gaussianCdf, OperatorRidgelet.gaussianFun, OperatorRidgelet.weightedDistribution, OperatorRidgelet.Paper.lem_5_2_relu_mem, OperatorRidgelet.Paper.lem_5_2_relu_lipschitz, OperatorRidgelet.Paper.lem_5_2_relu_not_polynomial, OperatorRidgelet.Paper.lem_5_2_tanh_mem, OperatorRidgelet.Paper.lem_5_2_tanh_lipschitz, OperatorRidgelet.Paper.lem_5_2_tanh_not_polynomial, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_mem, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_5_2_gaussian_mem, OperatorRidgelet.Paper.lem_5_2_gaussian_lipschitz, OperatorRidgelet.Paper.lem_5_2_gaussian_not_polynomial, OperatorRidgelet.Paper.lem_5_2_exists_filter") (uses := "aux:tempered-distributions")
ReLU, $`\tanh`, the Gaussian distribution function
$`\Phi(u)=\int_{-\infty}^u(2\pi)^{-1/2}e^{-v^2/2}\,\mathrm dv`, and $`e^{-u^2/2}` belong to
$`\mathcal A_{0,2}=\langle\cdot\rangle^2L^2(\mathbb R)`, are globally Lipschitz, and are not
polynomials (twelve claims). For every non-polynomial real $`\beta\in\mathcal S'` there is a
real band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}=1`.
:::

:::proof "lem:5.2" (uses := "lem:5.1, thm:4.5")
Membership in $`\mathcal A_{0,2}` means $`\langle u\rangle^{-2}\beta\in L^2`; three of the
functions are bounded and ReLU satisfies $`\int_0^\infty u^2(1+u^2)^{-2}\mathrm du<\infty`.
Their derivatives are bounded wherever defined, the bounded functions are nonconstant and ReLU
is not smooth at zero, and the last statement is the final part of the proof of
{bpref "thm:4.5"}[] followed by rescaling $`\rho`.
:::

# Reconstruction with tempered activations

:::definition "def:5.3" (lean := "OperatorRidgelet.IsRealDistribution, OperatorRidgelet.IsCutoff, OperatorRidgelet.IsApproximateIdentity, OperatorRidgelet.distributionConvolution, OperatorRidgelet.regularizedSpectrum, OperatorRidgelet.regularizedActivation, OperatorRidgelet.regularizedSynthesis, OperatorRidgelet.temperedSynthesis, OperatorRidgelet.Paper.def_5_3_i, OperatorRidgelet.Paper.def_5_3_ii, OperatorRidgelet.Paper.def_5_3_iii, OperatorRidgelet.Paper.def_5_3_iv, OperatorRidgelet.Paper.def_5_3_v, OperatorRidgelet.Paper.def_5_3_vi") (uses := "def:3.3, aux:conventions, aux:tempered-distributions, aux:frame-operator, thm:3.14")
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

:::theorem "thm:5.4" (lean := "OperatorRidgelet.Paper.thm_5_4_i, OperatorRidgelet.Paper.thm_5_4_ii, OperatorRidgelet.Paper.thm_5_4_iii, OperatorRidgelet.Paper.thm_5_4_iv, OperatorRidgelet.Paper.thm_5_4_v, OperatorRidgelet.Paper.thm_5_4_vi") (uses := "def:5.3, aux:tempered-activation")
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

:::proof "thm:5.4" (uses := "thm:3.14, thm:4.8, thm:4.5")
Each $`\beta_\varepsilon` is a real Schwartz function whose Fourier transform has compact support away from zero. It is admissible whenever it is nonzero. Plancherel gives the following identity in that case; the zero case is immediate:
$`S_{\beta_\varepsilon}R_\rho f=C_{\beta_\varepsilon,\rho}^{(\alpha)}T_\alpha f`;
distributional convergence of $`\beta^\sharp*\eta_\varepsilon` against the fixed test
function $`\rho^\sharp(-\omega)|\omega|^{-\alpha}` gives convergence of the constants, and
$`T_\alpha` is an isometry, so the functionals converge in $`\mathcal E_\alpha'`. The
existence of $`\rho` with nonzero constant is the last step of the proof of
{bpref "thm:4.5"}[].
:::

:::corollary "cor:5.5" (lean := "OperatorRidgelet.reluDistribution, OperatorRidgelet.reluAdmissibilityScale, OperatorRidgelet.reluNormalizedFilter, OperatorRidgelet.Paper.cor_5_5_i, OperatorRidgelet.Paper.cor_5_5_ii, OperatorRidgelet.Paper.cor_5_5_iii, OperatorRidgelet.Paper.cor_5_5_iv, OperatorRidgelet.Paper.cor_5_5_v, OperatorRidgelet.Paper.cor_5_5_vi, OperatorRidgelet.Paper.cor_5_5_vii, OperatorRidgelet.Paper.cor_5_5_viii") (uses := "thm:5.4, thm:4.5, def:3.3, aux:tempered-activation, def:4.2")
Let $`\beta=\operatorname{ReLU}`, $`\operatorname{ReLU}(t)=\max(t,0)`. Then
$`\operatorname{ReLU}^\sharp=-\operatorname{fp}(\omega^{-2})+i\pi\delta_0'` (i), which
equals $`-\omega^{-2}` away from the origin (ii). If
$`\rho^\sharp\in C_c^\infty(\mathbb R\setminus\{0\})` is nonzero, even, and nonpositive, then
$`C_{\operatorname{ReLU},\rho}^{(\alpha)}=-\frac1{2\pi}\int_{\mathbb R}\rho^\sharp(\omega)|\omega|^{-\alpha-2}\,\mathrm d\omega`
(iii), which is positive (iv). After rescaling $`\rho` the constant is one (v), and the two
reconstruction formulas of {bpref "thm:5.4"}[] (vi, vii) and
{bpref "thm:4.5"}[] (iii) (viii) hold with ReLU synthesis for every $`\alpha>0`.
:::

:::proof "cor:5.5"
From $`\operatorname{ReLU}(t)=(|t|+t)/2`, the identities $`(|t|)^\sharp=-2\operatorname{fp}(\omega^{-2})`
and $`t^\sharp=2\pi i\delta_0'` give the Fourier transform; the test function is supported
away from zero, so the $`\delta_0'` term vanishes and the finite part is ordinary
multiplication by $`\omega^{-2}`, and evenness and the sign of $`\rho^\sharp` give the
constant.
:::

:::example_ "ex:5.6" (lean := "OperatorRidgelet.Paper.lem_5_2_relu_mem, OperatorRidgelet.Paper.lem_5_2_relu_lipschitz, OperatorRidgelet.Paper.lem_5_2_relu_not_polynomial, OperatorRidgelet.Paper.lem_5_2_tanh_mem, OperatorRidgelet.Paper.lem_5_2_tanh_lipschitz, OperatorRidgelet.Paper.lem_5_2_tanh_not_polynomial, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_mem, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_5_2_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_5_2_gaussian_mem, OperatorRidgelet.Paper.lem_5_2_gaussian_lipschitz, OperatorRidgelet.Paper.lem_5_2_gaussian_not_polynomial, OperatorRidgelet.Paper.ex_5_6_relu, OperatorRidgelet.Paper.ex_5_6_tanh, OperatorRidgelet.Paper.ex_5_6_gaussianCdf, OperatorRidgelet.Paper.ex_5_6_gaussian") (uses := "thm:5.4, thm:4.5, thm:6.6")
ReLU, $`\tanh`, the Gaussian distribution function, and the Gaussian $`e^{-u^2/2}` are
globally Lipschitz, are not polynomials, and belong to $`\mathcal A_{0,2}`. Each of them is
therefore covered by {bpref "thm:5.4"}[], by {bpref "thm:4.5"}[] (iii), and
by the finite-width bounds of {bpref "thm:6.6"}[]; the Lean instance of this coverage is that for
every $`\alpha>0` there is a band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}\ne0` for each
of the four activations.
:::

:::proof "ex:5.6" (uses := "lem:5.2")
The three properties are {bpref "lem:5.2"}[]; a globally Lipschitz
function has polynomial growth, so {bpref "thm:4.5"}[] (iii) applies. The activation assumptions of the finite-width results below are therefore satisfied.
:::

*Remark 5.7 (Identity in the dual space versus integral network).*

The frame identity for a tempered activation holds in $`\mathcal E_\alpha'`. By itself it does not
produce a finite coefficient measure on $`H\times\mathbb R`. For a spectral density
regular along rays, {bpref "thm:4.5"}[] gives an absolutely convergent integral network;
{bpref "thm:6.6"}[] supplies finite total variation and moments. The ReLU examples use
this stronger conclusion.

# Inverse Fourier estimates and dual pairing

For Hilbert-valued profiles, $`H^s_\omega` is the Bessel-potential space in the frequency variable. In the Banach-valued hypotheses below, the same norm notation means the displayed weighted $`L^2` norm of the specified inverse transform. These hypotheses are stated directly; a Fourier isometry is used only for Hilbert-valued functions.

:::lemma_ "lem:5.8" (lean := "OperatorRidgelet.bracket, OperatorRidgelet.MemRaySobolev, OperatorRidgelet.raySobolevNorm, OperatorRidgelet.rayProfile, OperatorRidgelet.sobolevMomentConst, OperatorRidgelet.Paper.lem_5_8_i, OperatorRidgelet.Paper.lem_5_8_ii, OperatorRidgelet.Paper.lem_5_8_iii, OperatorRidgelet.Paper.lem_5_8_iv") (uses := "aux:conventions")
Use $`\|h\|_{H^s_\omega}` for the norm of a profile $`h` whose inverse Fourier transform
$`\gamma=\check h` satisfies $`\|h\|_{H^s_\omega}^2=2\pi\int\langle
t\rangle^{2s}\|\gamma(t)\|^2\,\mathrm dt<\infty`. For $`s>1/2` and $`0\le r<s-1/2`,
$`\int\langle t\rangle^r\|\gamma(t)\|\,\mathrm dt\le A_{s,r}\|h\|_{H^s_\omega}` with
$`A_{s,r}=(2\pi)^{-1/2}(\int(1+t^2)^{-(s-r)}\mathrm dt)^{1/2}`. Reflection $`Rh(\omega)=h(-\omega)`
is an isometry, $`\|M_uh\|_{H^s_\omega}\le(1+|u|)^s\|h\|_{H^s_\omega}` for the modulation
$`M_uh(\omega)=e^{iu\omega}h(\omega)`, and $`(u,h)\mapsto M_uh` is jointly continuous.
:::

:::proof "lem:5.8"
The weighted $`L^1` bound is Cauchy--Schwarz applied to $`\langle t\rangle^{-(s-r)}` and
$`\langle t\rangle^{s}\|\gamma(t)\|`, the scalar factor being integrable exactly when
$`s-r>1/2`. Reflection and modulation correspond to $`\gamma(-\cdot)` and $`\gamma(\cdot+u)` on
the coefficient side, and $`\langle t-u\rangle\le(1+|u|)\langle t\rangle` gives the modulation
bound. Joint continuity reduces, by that bound and the triangle inequality, to the strong
continuity of translation, which follows from the strong continuity of translation in $`L^2`
and dominated convergence for the multiplier
$`(\langle t\rangle/\langle t+u\rangle)^s`.
:::

The weighted $`L^1` estimate and reflection identity are used in the representation proof below. The modulation bound and joint continuity describe the alternative route through an $`H^s_\omega`-valued Bochner integral.

:::lemma_ "lem:5.9" (lean := "OperatorRidgelet.sobolevPairing, OperatorRidgelet.sobolevPairingConst, OperatorRidgelet.Paper.lem_5_9_i, OperatorRidgelet.Paper.lem_5_9_ii, OperatorRidgelet.Paper.lem_5_9_iii")
Let $`\sigma` be continuous with $`|\sigma(t)|\le C_\sigma(1+|t|)^p`, $`p\ge0`, and
$`s>p+1/2`, and put $`b_{\sigma,s}=\|\langle\cdot\rangle^{-s}\sigma\|_2`, which is finite. The
pairing $`L_\sigma^Y(h)=\int\sigma(t)\check h(-t)\,\mathrm dt` converges absolutely and
satisfies $`\|L_\sigma^Y(h)\|\le(2\pi)^{-1/2}b_{\sigma,s}\|h\|_{H^s_\omega}`, so it is the
bounded extension of $`(2\pi)^{-1}\langle\sigma^\sharp,\cdot\rangle` to $`H^s_\omega`.
Moreover $`\int\sigma(u-b)\gamma(b)\,\mathrm db=L_\sigma^Y(M_uh)`.
:::

:::proof "lem:5.9" (uses := "lem:5.8")
$`1+|t|\le\sqrt2\langle t\rangle` turns the growth bound into
$`\langle t\rangle^{-s}|\sigma(t)|\le C_\sigma2^{p/2}\langle t\rangle^{p-s}`, whose square is
integrable for $`s-p>1/2`. Weighted Cauchy--Schwarz against
{bpref "lem:5.8"}[] gives absolute convergence and the bound, the reflection isometry
turning $`\|\gamma(-\cdot)\|` into $`\|h\|_{H^s_\omega}`. The translation formula is the change
of variables $`b=u-t`.
:::

# Integral representation under Sobolev conditions

For the density $`g`, write $`f_g(x)=\int_H e^{i\langle x,\xi\rangle}g(\xi)\,\nu(\mathrm d\xi)` whenever $`g\in L^1(\nu;Y)`, and $`\Gamma_g=\gamma_g(\nu\otimes\mathrm db)`. This is the same spectral synthesis denoted $`g_G` above when the density is written $`G`.

:::theorem "thm:5.10" (lean := "OperatorRidgelet.Paper.thm_5_10_i, OperatorRidgelet.Paper.thm_5_10_ii, OperatorRidgelet.Paper.thm_5_10_iii, OperatorRidgelet.Paper.thm_5_10_iv, OperatorRidgelet.Paper.thm_5_10_v") (uses := "def:3.3, aux:conventions")
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

:::proof "thm:5.10" (uses := "lem:5.8, lem:5.9")
First choose $`\omega_0\ne0` with $`\rho^\sharp(-\omega_0)\ne0`.
The weighted inverse Fourier estimate with $`r=0` gives
$`\|h_a(\omega_0)\|\le A_{s,0}\|h_a\|_{H^s_\omega}`. Integrating this inequality
and using homogeneity yields
$`\|g\|_{L^1(\nu;Y)}\le |\omega_0|^\alpha |\rho^\sharp(-\omega_0)|^{-1}
 A_{s,0}\mathfrak B_s(\rho,g)<\infty`. Thus $`f_g` is defined, bounded, and continuous
by the earlier spectral-target lemma.

The moments are the weighted $`L^1` estimate of {bpref "lem:5.8"}[] applied to
$`b\mapsto\gamma_g(a,b)`,
$`1+\|a\|+|b|\le\sqrt2(1+\|a\|)\langle b\rangle`, and Tonelli; the case $`r=0` gives the finite
total variation of the coefficient measure, and the growth bound of $`\sigma` with $`r=p`
gives the absolute convergence and the
majorant. For the identity, Fubini in the two parameters turns the synthesis into
$`\int\sigma(t)\Psi(t)\,\mathrm dt` with
$`\Psi(t)=\int\gamma_g(a,\langle a,x\rangle-t)\,\mathrm d\nu`. Fubini again computes the profile
of the integrable $`\Psi`, which homogeneity identifies with
$`\rho^\sharp(\omega)|\omega|^{-\alpha}f_g(x)` off the origin, hence everywhere by continuity;
the $`L^1` uniqueness of the profile then identifies $`\Psi` with
$`\check q_{\alpha,\rho}(-\cdot)f_g(x)`, and the pairing of {bpref "lem:5.9"}[] gives
the constant. Continuity is dominated convergence with the majorant. The final clause of the
manuscript statement, that $`\gamma_g` lies in $`L^2(\nu\otimes\mathrm db;Y)` with
$`\|\gamma_g\|^2=(\!(\rho,\rho)\!)_\alpha\|g\|^2_{L^2(\nu;Y)}` when $`Y` is a separable complex
Hilbert space, $`(\!(\rho,\rho)\!)_\alpha<\infty` and $`g\in L^2(\nu;Y)`, is not part of the
Lean statement.
:::

The displayed statement includes the manuscript product-space $`L^2` conclusion. The associated Lean statements carry that clause in a weaker form; their verification does not assert the full clause as written here.

*Remark 5.11 (What the synthesis identity uses).*

The absolutely convergent integral representation uses the inner product and Borel structure
of the input space,
homogeneity of the direction measure, and completeness of the output norm. The output
Hilbert structure is needed only for the $`L^2` coefficient conclusion. Positivity of the
admissibility constant is not required. The ray hypotheses already imply
$`G\in L^1(\nu;Y)` by evaluating the weighted inverse-transform estimate at a nonzero
frequency where $`\rho^\sharp` does not vanish and then using homogeneity.

A second parameter moment needs $`s>5/2`. With a globally Lipschitz activation,
{bpref "thm:6.5"}[] then applies; reconstruction of $`f_G` also requires
division by a nonzero synthesis pairing. The example below verifies concrete filters without band-pass support.

*Examples of filters for the reconstruction formula.*

The following explicit filters meet the Sobolev criterion without band-pass support.
Their coefficient estimates and constants are proved immediately below.

# Example of filters for the reconstruction formula

:::proposition "prop:5.12" (lean := "OperatorRidgelet.gaussDerivFilter, OperatorRidgelet.gaussTarget, OperatorRidgelet.gaussRayCoefficient, OperatorRidgelet.gaussSobolevRay, OperatorRidgelet.Paper.prop_5_12_i, OperatorRidgelet.Paper.prop_5_12_ii, OperatorRidgelet.Paper.prop_5_12_iii, OperatorRidgelet.Paper.prop_5_12_iv, OperatorRidgelet.Paper.prop_5_12_v, OperatorRidgelet.Paper.prop_5_12_vi, OperatorRidgelet.Paper.prop_5_12_vii, OperatorRidgelet.Paper.prop_5_12_viii, OperatorRidgelet.Paper.prop_5_12_ix") (uses := "thm:5.10, def:3.3, aux:conventions")
Under the input-space and sigma-finite Borel measure hypotheses of {bpref "thm:5.10"}[],
let $`\nu` be homogeneous of degree $`\alpha>0` and finite on the unit ball. Fix $`s>1/2` and an
integer $`k\ge1` with $`2k>\alpha+2s-1/2`, and let
$`\rho_k^\sharp(\omega)=\omega^{2k}e^{-\omega^2}`, $`g(\xi)=e^{-\|\xi\|^2}v`. Then $`\rho_k` is
a real Schwartz filter (i) that is not band pass (ii) but is $`\alpha`-admissible for
$`\alpha<4k+1` (iii). The homogeneous moments $`\int(1+\|a\|^2)^{-d/2}\mathrm d\nu` are finite
for $`d>\alpha` (iv); the coefficient $`\gamma_g` is jointly measurable (v), each function
$`h_a(\omega)=\rho_k^\sharp(-\omega)g(\omega a)` lies in $`H^s_\omega` (vi), and
$`\mathfrak B_s(\rho_k,g)<\infty` (vii). The Sobolev test $`q_{\alpha,\rho_k}` lies in
$`H^s_\omega` (viii). Hence {bpref "thm:5.10"}[] applies to this filter for
every continuous activation of growth order $`p<s-1/2` (ix).

Put $`\delta=2k-\alpha`. For $`\sigma(t)=e^{-t^2/2}`, the reconstruction constant is
$`(\!(\sigma,\rho_k)\!)_\alpha=\Gamma((\delta+1)/2)(3/2)^{-(\delta+1)/2}/\sqrt{2\pi}>0`.
If $`s>3/2`, ReLU also satisfies the hypotheses and
$`(\!(\operatorname{ReLU},\rho_k)\!)_\alpha=-(2\pi)^{-1}\Gamma((\delta-1)/2)\ne0`.
The unit-ball finiteness hypothesis holds for the homogeneous Gaussian mixtures on the
infinite-dimensional Hilbert space used in the main construction.
:::

:::proof "prop:5.12" (uses := "lem:5.8")
The Fourier transform $`\rho_k^\sharp` is a polynomial times a Gaussian, hence Schwartz,
and real and even, so its inverse
Fourier transform is a real Schwartz function. It vanishes only at the origin, which is
therefore in the closed support, so the filter is not band pass, while
$`|\rho_k^\sharp|^2|\omega|^{-\alpha}=|\omega|^{4k-\alpha}e^{-2\omega^2}` is integrable exactly
for $`4k-\alpha>-1`. Homogeneity scales balls, $`\nu(B_R)=R^\alpha\nu(B_1)`, and the dyadic
annuli give a geometric series, which is the moment bound. Write
$`h_0(\omega)=\omega^{2k}e^{-\omega^2}` and $`A=(1+\|a\|^2)^{1/2}`.
The function $`h_a(\omega)=\omega^{2k}e^{-A^2\omega^2}v` has inverse transform
$`A^{-2k-1}\rho_k(b/A)v`, a dilate of a Schwartz function, so it lies in every $`H^s_\omega`,
with $`\|h_a\|_{H^s_\omega}\le\|v\|\,\|h_0\|_{H^s_\omega}A^{s-2k-1/2}`;
$`1+\|a\|\le\sqrt2A` and the moment bound give $`\mathfrak B_s<\infty` exactly in the stated
range. For the Sobolev test, the Gamma integral
$`|\omega|^{-\alpha}=\Gamma(\alpha/2)^{-1}\int_0^\infty u^{\alpha/2-1}e^{-u\omega^2}\mathrm du`
writes $`q_{\alpha,\rho_k}` as a superposition of the rescaled functions
$`A^{-2k}h_0(A\,\cdot)` with $`A=(1+u)^{1/2}`; Fubini gives its inverse transform,
and Cauchy--Schwarz against the finite weight
$`u^{\alpha/2-1}(1+u)^{(s-2k-1/2)/2}` together with Tonelli reduces its Sobolev norm to the
norms of the dilated filters.

For the Gaussian activation, substitute
$`\sigma^\sharp(\omega)=\sqrt{2\pi}e^{-\omega^2/2}` in the pairing and evaluate
$`\int_{\mathbb R}|\omega|^\delta e^{-3\omega^2/2}\,\mathrm d\omega`
by the Gamma integral. For ReLU, its Fourier transform away from zero is
$`-\omega^{-2}`. When $`s>3/2`, the order condition gives $`\delta>5/2`, so
the origin-supported terms vanish against the Sobolev test and the remaining integral is
$`-(2\pi)^{-1}\int_{\mathbb R}|\omega|^{\delta-2}e^{-\omega^2}\,\mathrm d\omega`.
This is the stated negative, nonzero Gamma constant.
:::

The two displayed closed-form synthesis constants are part of the manuscript statement. The associated Lean statements retain their Sobolev-pairing formulations and do not assert those two closed-form evaluations.
