import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Tempered

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
