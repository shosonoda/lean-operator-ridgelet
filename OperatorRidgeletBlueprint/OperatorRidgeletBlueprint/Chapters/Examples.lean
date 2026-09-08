import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Examples

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Examples with genuinely infinite-dimensional inputs" =>
%%%
file := "examples"
%%%

This chapter is Section 7 of the manuscript together with Appendix E. A function $`f` on $`H`
is cylindrical if $`f=\widetilde f\circ L` for a finite-rank linear map $`L`; all examples are
non-cylindrical, so finite width is never obtained by truncating the input. We write
$`\phi_v` for the centred one-dimensional Gaussian density of variance $`v>0`, with
$`\phi_0=\delta_0`, and $`\Phi(u)=e^{-u^2/2}` for the Gaussian activation.

# Preliminaries

:::definition "aux:cylindrical" (lean := "OperatorRidgelet.IsCylindrical, OperatorRidgelet.HasInfiniteRank, OperatorRidgelet.FactorsThrough, OperatorRidgelet.not_factorsThrough_of_fibre_separation, OperatorRidgelet.not_factorsThrough_linear_of_kernel_separation")
A function $`f` on $`H` is cylindrical if $`f=\widetilde f\circ L` for a linear map
$`L:H\to\mathbb R^m`, and a linear map has infinite rank when its range is not finite
dimensional. The elementary obstruction: a target $`F` cannot factor through an observation
$`P` if $`P(x)=P(y)` but $`F(x)\ne F(y)`; in particular, if $`F` separates $`0` from a vector
in the kernel of a linear $`P`, then $`F` is not cylindrical through $`P`.
:::

:::definition "aux:trace-class-operators" (lean := "OperatorRidgelet.traceAlong, OperatorRidgelet.HasSummableTrace, OperatorRidgelet.traceOf, OperatorRidgelet.IsPositiveTraceClass, OperatorRidgelet.IsPositiveSqrt, OperatorRidgelet.HasEigenbasis, OperatorRidgelet.fredholmDetAlong, OperatorRidgelet.fredholmDet, OperatorRidgelet.resolventForm") (uses := "aux:centered-gaussian, roadmap:trace-and-determinant")
Mathlib has neither trace-class operators nor Fredholm determinants. The trace
$`\operatorname{tr}P=\sum_i\langle Pe_i,e_i\rangle` is taken along a Hilbert basis for which
the sum converges; a positive trace-class operator is positive, self-adjoint, with summable
trace; square roots $`Q^{1/2}` are data $`S` with $`S` positive self-adjoint and $`S^2=Q`;
the Fredholm determinant $`\det(I+M)=\prod_i(1+m_i)` is computed along an orthonormal
eigenbasis of $`M`; and $`(I+M)^{-1}` enters through the quadratic form
$`\langle S(I+M)^{-1}Sx,x\rangle`.
:::

:::definition "aux:gaussian-target" (lean := "OperatorRidgelet.gaussianFun, OperatorRidgelet.gaussianActDeriv2, OperatorRidgelet.gaussianSmooth, OperatorRidgelet.gaussianTarget, OperatorRidgelet.gaussianKappa, OperatorRidgelet.gaussianTargetResolvent, OperatorRidgelet.mixtureLayerCovariance, OperatorRidgelet.MemSpectralCore, OperatorRidgelet.MemSpectralCoreVec, OperatorRidgelet.toLpOrZero, OperatorRidgelet.gaussFourier_congr_ae, OperatorRidgelet.toLp_mem_spectralCore_iff, OperatorRidgelet.memSpectralCore_iff") (uses := "aux:trace-class-operators, def:spectral-space, aux:gaussian-mixture")
The Gaussian activation $`\Phi(u)=\phi(u)=e^{-u^2/2}` with $`\phi''(b)=(b^2-1)e^{-b^2/2}`,
the convolution $`(\rho*\phi_v)(c)` with the centred Gaussian of variance $`v\ge0`, the
Gaussian target $`f_W(x)=e^{-\langle Wx,x\rangle/2}`, and, for $`M=Q^{1/2}WQ^{1/2}`,
$`\kappa_W(\xi)=\langle Q^{1/2}(I+M)^{-1}Q^{1/2}\xi,\xi\rangle`,
$`S_W=Q^{1/2}(I+M)^{-1}Q^{1/2}`, and
$`\Sigma_s=2sP^{1/2}(I+2sP^{1/2}S_WP^{1/2})^{-1}P^{1/2}`. Membership $`f\in\mathcal D_\alpha`
of a function (rather than of an $`L^2` class) means $`f\in L^2(\mu)` and
$`\mathcal G_\mu f\in L^2(\nu)`, related to the submodule $`\mathcal D_\alpha` by the stated
lemmas.
:::

:::lemma_ "lem:gaussian-quadratic" (lean := "OperatorRidgelet.Paper.lem_gaussian_quadratic_i, OperatorRidgelet.Paper.lem_gaussian_quadratic_ii") (uses := "aux:trace-class-operators, aux:centered-gaussian")
Let $`\Sigma` be a positive self-adjoint trace-class operator, $`S` a bounded positive
self-adjoint operator, and $`x\in H`. Then $`M=\Sigma^{1/2}S\Sigma^{1/2}` is trace class (i),
and
$`\int_He^{i\langle x,\xi\rangle-\langle S\xi,\xi\rangle/2}\,\mathcal N(0,\Sigma)(\mathrm d\xi)=\det(I+M)^{-1/2}\exp\bigl(-\tfrac12\langle\Sigma^{1/2}(I+M)^{-1}\Sigma^{1/2}x,x\rangle\bigr)`
(ii).
:::

:::proof "lem:gaussian-quadratic"
In an orthonormal eigenbasis $`(u_j)` of $`M` with eigenvalues $`m_j`, the Gaussian series
$`\xi=\sum_j\eta_j\Sigma^{1/2}u_j` has law $`\mathcal N(0,\Sigma)`,
$`\langle S\xi,\xi\rangle=\sum_jm_j\eta_j^2`, and the expectation factorizes into
one-dimensional Gaussian integrals $`(1+m_j)^{-1/2}e^{-x_j^2/(2(1+m_j))}`.
:::

:::definition "aux:relu-identities" (lean := "LeanRidgelet.relu, OperatorRidgelet.relu_sub_relu_neg, OperatorRidgelet.spectralReLUNetwork, OperatorRidgelet.spectralReLUNetwork_eq")
$`\operatorname{ReLU}(x)=\max(x,0)` and its odd part is the identity,
$`\operatorname{ReLU}(x)-\operatorname{ReLU}(-x)=x`. For a finite spectral index set, the
paired-ReLU network $`\sum_i\lambda_i[\operatorname{ReLU}(\langle e_i,x\rangle)-\operatorname{ReLU}(-\langle e_i,x\rangle)]e_i`
therefore equals the spectral truncation $`\sum_i\lambda_i\langle e_i,x\rangle e_i` exactly.
:::

:::lemma_ "lem:gaussian-hinge" (lean := "OperatorRidgelet.Paper.lem_gaussian_hinge_i_a, OperatorRidgelet.Paper.lem_gaussian_hinge_i_b, OperatorRidgelet.Paper.lem_gaussian_hinge_ii") (uses := "aux:gaussian-target, aux:relu-identities")
For $`\phi(u)=e^{-u^2/2}`, the integral $`\int_{\mathbb R}(u-b)_+\phi''(b)\,\mathrm db`
converges absolutely for each $`u` (i a) and equals $`\phi(u)` (i b), and
$`\int_{\mathbb R}(1+|b|^k)|\phi''(b)|\,\mathrm db<\infty` for every $`k\ge0` (ii).
:::

:::proof "lem:gaussian-hinge"
$`\phi''(b)=(b^2-1)e^{-b^2/2}` has all polynomially weighted absolute integrals finite, and
integrating by parts on $`(-L,u)` gives
$`\int_{-L}^u(u-b)\phi''(b)\mathrm db=\phi(u)-\phi(-L)-(u+L)\phi'(-L)\to\phi(u)`.
:::

# A Gaussian target with a closed-form transform

:::proposition "ex:closed-form" (lean := "OperatorRidgelet.Paper.ex_closed_form_i_a, OperatorRidgelet.Paper.ex_closed_form_i_b, OperatorRidgelet.Paper.ex_closed_form_i_c, OperatorRidgelet.Paper.ex_closed_form_i_d, OperatorRidgelet.Paper.ex_closed_form_ii_a, OperatorRidgelet.Paper.ex_closed_form_ii_b, OperatorRidgelet.Paper.ex_closed_form_ii_c, OperatorRidgelet.Paper.ex_closed_form_iii_a, OperatorRidgelet.Paper.ex_closed_form_iii_b, OperatorRidgelet.Paper.ex_closed_form_iii_c, OperatorRidgelet.Paper.ex_closed_form_iii_d") (uses := "aux:gaussian-target, aux:cylindrical, lem:gaussian-quadratic, lem:fourier-slice, lem:gaussian-decay, lem:mixture-integration, thm:C, lem:ray-regular-examples, thm:E")
Let $`W` be bounded, positive, injective, self-adjoint with $`M=Q^{1/2}WQ^{1/2}` trace class,
$`f_W(x)=e^{-\langle Wx,x\rangle/2}`, $`D=\det(I+M)`, and
$`\kappa_W(\xi)=\langle Q^{1/2}(I+M)^{-1}Q^{1/2}\xi,\xi\rangle`. For every $`\alpha>0` and
band-pass $`\rho`: (i) $`\mathcal G_Qf_W(\xi)=D^{-1/2}e^{-\kappa_W(\xi)/2}` and
$`R_\rho f_W(a,c)=D^{-1/2}(\rho*\phi_{\kappa_W(a)})(c)`, so $`f_W\in\mathcal D_\alpha`, and
$`f_W` is not cylindrical when $`W` has infinite rank. (ii) $`G=\mathcal G_Qf_W` is regular
along rays and $`T_\alpha f_W` is represented by
$`g_G(x)=D^{-1/2}\int_0^\infty\det(I+2sP^{1/2}S_WP^{1/2})^{-1/2}\exp(-\tfrac12\langle\Sigma_sx,x\rangle)\,s^{\alpha/2-1}\,\mathrm ds`.
(iii) For every real, globally Lipschitz, non-polynomial $`\beta`, the coefficient
$`R_\rho f_W=\gamma_G` has finite variation and second moment,
$`S_\beta[R_\rho f_W\lambda_\alpha]=C_{\beta,\rho}^{(\alpha)}g_G`, and its sampled network
converges at the rate $`N^{-1/2}` in $`C(K)`.
:::

:::proof "ex:closed-form"
{bpref "lem:gaussian-quadratic"}[] with $`\Sigma=Q`, $`S=W` gives $`\mathcal G_Qf_W`, Fourier
inversion in the bias gives the convolution, $`(I+M)^{-1}\ge(1+\|M\|)^{-1}I` gives the decay
needed by {bpref "lem:gaussian-decay"}[], and $`f_W(x)<1=f_W(0)` for $`x\ne0` in the kernel
of a finite-rank map. Part (ii) is {bpref "thm:C"}[] (iii) with the Gaussian integral applied
on each layer of $`\nu_\alpha`; part (iii) is {bpref "lem:ray-regular-examples"}[] (a) with
$`S_W\ge(1+\|M\|)^{-1}Q` followed by {bpref "thm:E"}[].
:::

# Gaussian-parameter networks on the sequence space

Let $`H=\ell^2(\mathbb N)` with standard basis $`(e_j)` and $`Qe_j=q_je_j`, $`q_j>0`,
$`\sum_jq_j<\infty`; in Lean, $`H` is abstract with a Hilbert basis on which $`Q` is
diagonal.

:::definition "aux:gaussian-parameter-networks" (lean := "OperatorRidgelet.gaussianParameterReLU, OperatorRidgelet.gaussianParameterGauss, OperatorRidgelet.hingeCoefficientMeasure") (uses := "def:integral-network, aux:gaussian-target, aux:centered-gaussian")
The integral networks $`F_Q(x)=\int_H\operatorname{ReLU}(\langle a,x\rangle)\,\mathcal N(0,Q)(\mathrm da)`
and $`\Phi_Q(x)=\int_H\Phi(\langle a,x\rangle)\,\mathcal N(0,Q)(\mathrm da)`, and the ReLU
coefficient measure of a Gaussian-activation network with coefficient density $`\gamma`: the
pushforward of $`\phi''(b)\gamma(a,c)\,\lambda(\mathrm da,\mathrm dc)\,\mathrm db` under
$`(a,c,b)\mapsto(a,c-b)`.
:::

:::proposition "ex:gaussian-parameter" (lean := "OperatorRidgelet.Paper.ex_gaussian_parameter_i, OperatorRidgelet.Paper.ex_gaussian_parameter_ii, OperatorRidgelet.Paper.ex_gaussian_parameter_iii, OperatorRidgelet.Paper.ex_gaussian_parameter_iv, OperatorRidgelet.Paper.ex_gaussian_parameter_v, OperatorRidgelet.Paper.ex_gaussian_parameter_vi_a, OperatorRidgelet.Paper.ex_gaussian_parameter_vi_b, OperatorRidgelet.Paper.ex_gaussian_parameter_vi_c") (uses := "aux:gaussian-parameter-networks, aux:cylindrical, aux:centered-gaussian, lem:gaussian-hinge")
$`F_Q(x)=\sqrt{\langle Qx,x\rangle/2\pi}` (i) and
$`\Phi_Q(x)=(1+\langle Qx,x\rangle)^{-1/2}` (ii), which also equals
$`\int_{H\times\mathbb R}\operatorname{ReLU}(\langle a,x\rangle-b)\,\phi''(b)\,\mathcal N(0,Q)(\mathrm da)\,\mathrm db`
(iii). Neither $`F_Q` (iv) nor $`\Phi_Q` (v) is cylindrical. A Gaussian-activation network
with finite coefficient measure is also a ReLU network with the hinge coefficient measure
(vi a), which is finite (vi b) with all parameter moments finite (vi c).
:::

:::proof "ex:gaussian-parameter"
For fixed $`x`, $`\langle a,x\rangle` is centred Gaussian with variance
$`v=\langle Qx,x\rangle`, and $`\mathbb EZ_+=\sqrt{v/2\pi}`, $`\mathbb Ee^{-Z^2/2}=(1+v)^{-1/2}`
for $`Z\sim\mathcal N(0,v)`; the hinge representation of {bpref "lem:gaussian-hinge"}[] with
Fubini gives (iii) and (vi), and a nonzero vector in the kernel of a finite-rank map would give
the same value as $`x=0`, contradicting injectivity of $`Q`.
:::

:::corollary "cor:relu-discretization" (lean := "OperatorRidgelet.Paper.cor_relu_discretization") (uses := "ex:gaussian-parameter, thm:lipschitz-barron, aux:trace-class-operators, aux:relu-identities")
Let $`a_1,\dots,a_N` be independent with law $`\mathcal N(0,Q)` and
$`F_{Q,N}(x)=\frac1N\sum_{j=1}^N\operatorname{ReLU}(\langle a_j,x\rangle)`. Then for every
compact $`K\subset H`, $`\mathbb E\|F_{Q,N}-F_Q\|_{C(K)}\le8R_K\sqrt{\operatorname{tr}Q}/\sqrt N`.
:::

:::proof "cor:relu-discretization"
Apply {bpref "thm:lipschitz-barron"}[] with $`V=1`, $`c=0`, $`\beta(0)=0`,
$`\operatorname{Lip}(\beta)=1`, and $`M_2^2=\mathbb E\|a\|^2=\operatorname{tr}Q`.
:::

# Neural-operator layers

Let $`(\Omega,m)` be a finite measure space, $`y\mapsto a_y\in H` Borel and bounded with
$`\|A\|_\infty=\sup_y\|a_y\|`, and $`y\mapsto b_y\in Y` Borel with
$`\int_\Omega\|b_y\|_Ym(\mathrm dy)<\infty`. With $`(Ax)(y)=\langle a_y,x\rangle` and
$`Bu=\int_\Omega b_yu(y)\,m(\mathrm dy)`, the layer with a continuous real activation
$`\beta` of polynomial growth is
$`\mathcal F(x)=B\,\beta(Ax)=\int_\Omega b_y\,\beta(\langle a_y,x\rangle)\,m(\mathrm dy)`;
for $`\varphi\in Y` the scalar observable is $`F_\varphi(x)=\langle\mathcal F(x),\varphi\rangle_Y`
and $`w_\varphi(y)=\langle b_y,\varphi\rangle_Y`.

:::definition "aux:operator-layer" (lean := "OperatorRidgelet.HasPolynomialGrowth, OperatorRidgelet.IsLayerData, OperatorRidgelet.layerSupNorm, OperatorRidgelet.operatorLayer, OperatorRidgelet.layerWeight, OperatorRidgelet.layerObservable, OperatorRidgelet.layerA, OperatorRidgelet.layerCovariance, OperatorRidgelet.layerMeasure, OperatorRidgelet.layerHingeMeasure") (uses := "def:integral-network, aux:gaussian-target, aux:centered-gaussian")
The standing hypotheses on $`(a,b)`, the norm $`\|A\|_\infty`, the layer $`\mathcal F`, the
observable $`F_\varphi`, the weight $`w_\varphi`, the operator $`A:H\to L^2(m)`, the
covariances $`S_y=Q-(1+\sigma_y^2)^{-1}(Qa_y)\otimes(Qa_y)` with
$`\sigma_y^2=\langle Qa_y,a_y\rangle`, the $`Y`-valued coefficient measure
$`\Gamma=\iota_\#(b_y\,m(\mathrm dy))` with $`\iota(y)=(a_y,0)`, and the coefficient measure
of the ReLU form, the pushforward of $`\phi''(b)\,b_y\,m(\mathrm dy)\,\mathrm db` under
$`(y,b)\mapsto(a_y,-b)`.
:::

:::proposition "ex:operator-layer" (lean := "OperatorRidgelet.Paper.ex_operator_layer_i_a, OperatorRidgelet.Paper.ex_operator_layer_i_b, OperatorRidgelet.Paper.ex_operator_layer_i_c, OperatorRidgelet.Paper.ex_operator_layer_i_d, OperatorRidgelet.Paper.ex_operator_layer_i_e, OperatorRidgelet.Paper.ex_operator_layer_ii_a, OperatorRidgelet.Paper.ex_operator_layer_ii_b, OperatorRidgelet.Paper.ex_operator_layer_ii_c, OperatorRidgelet.Paper.ex_operator_layer_ii_d, OperatorRidgelet.Paper.ex_operator_layer_ii_e, OperatorRidgelet.Paper.ex_operator_layer_ii_f, OperatorRidgelet.Paper.ex_operator_layer_ii_g, OperatorRidgelet.Paper.ex_operator_layer_ii_h, OperatorRidgelet.Paper.ex_operator_layer_ii_i, OperatorRidgelet.Paper.ex_operator_layer_ii_j, OperatorRidgelet.Paper.ex_operator_layer_ii_k, OperatorRidgelet.Paper.ex_operator_layer_ii_l, OperatorRidgelet.Paper.ex_operator_layer_ii_m, OperatorRidgelet.Paper.ex_operator_layer_ii_n, OperatorRidgelet.Paper.ex_operator_layer_ii_o, OperatorRidgelet.Paper.ex_operator_layer_ii_p, OperatorRidgelet.Paper.ex_operator_layer_iii_a, OperatorRidgelet.Paper.ex_operator_layer_iii_b, OperatorRidgelet.Paper.ex_operator_layer_iii_c, OperatorRidgelet.Paper.ex_operator_layer_iii_d, OperatorRidgelet.Paper.ex_operator_layer_iv") (uses := "aux:operator-layer, aux:cylindrical, aux:gaussian-target, def:integral-network, cor:vector-rates, thm:lipschitz-barron, lem:fourier-slice, lem:gaussian-decay, lem:ray-regular-examples, thm:C, thm:E, thm:vector-valued, lem:gaussian-hinge")
(i) $`\mathcal F=S_\beta[\Gamma]` with $`\Gamma=\iota_\#(b_y\,m(\mathrm dy))`, whose total
variation is at most $`\int\|b_y\|m(\mathrm dy)` and whose second parameter moment is at most
$`\|A\|_\infty^2`; hence width-$`N` networks approximate $`\mathcal F` at the rate
$`N^{-1/2}` in $`L^2(\zeta;Y)`, and for globally Lipschitz $`\beta`,
$`\mathbb E\|F_{\varphi,N}-F_\varphi\|_{C(K)}\le\frac{8\|w_\varphi\|_{L^1(m)}}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_K\|A\|_\infty)`.
(ii) For $`\beta=\Phi`, $`F_\varphi\in\mathcal D_\alpha` for every $`\alpha>0`,
$`\mathcal G_QF_\varphi(\xi)=\int_\Omega w_\varphi(y)(1+\sigma_y^2)^{-1/2}e^{-\langle S_y\xi,\xi\rangle/2}\,m(\mathrm dy)`,
$`R_\rho F_\varphi(a,c)=\int_\Omega w_\varphi(y)(1+\sigma_y^2)^{-1/2}(\rho*\phi_{\langle S_ya,a\rangle})(c)\,m(\mathrm dy)`,
and $`S_y\ge(1+\|Q\|\|A\|_\infty^2)^{-1}Q`; consequently $`\mathcal G_QF_\varphi` is regular
along rays, the reconstruction formulas of {bpref "thm:C"}[] hold for $`F_\varphi`, and
$`R_\rho F_\varphi` synthesizes, with any real Lipschitz non-polynomial $`\beta'`, the target
$`C_{\beta',\rho}^{(\alpha)}T_\alpha F_\varphi` with the finite-width rate of
{bpref "thm:E"}[]; the same holds for $`\mathcal F` as a $`Y`-valued target. (iii) The
Gaussian-activation layer is also the ReLU network
$`\mathcal F(x)=\int_{\Omega\times\mathbb R}b_y\,\phi''(b)\operatorname{ReLU}(\langle a_y,x\rangle-b)\,m(\mathrm dy)\,\mathrm db`
with finite coefficient measure and finite moments. (iv) If $`A` has infinite rank,
$`\beta=\Phi`, and $`w_\varphi>0` $`m`-almost everywhere, then $`F_\varphi` is not
cylindrical.
:::

:::proof "ex:operator-layer"
Part (i) is the change of variables for the pushforward measure and
$`\|\iota(y)\|^2\le\|A\|_\infty^2`. For (ii), the pair
$`(\langle a_y,x\rangle,\langle x,\xi\rangle)` is centred Gaussian under $`\mu_Q` and
$`\mathbb E[e^{-Z^2/2}e^{-iW}]=(1+\sigma^2)^{-1/2}\exp(-\tau^2/2+r^2/(2(1+\sigma^2)))`;
Cauchy–Schwarz gives the lower bound on $`S_y`, {bpref "lem:ray-regular-examples"}[] (a) and
(c) give regularity along rays, and {bpref "thm:C"}[], {bpref "thm:E"}[], and
{bpref "thm:vector-valued"}[] give the rest. Part (iii) is Fubini with
{bpref "lem:gaussian-hinge"}[]; for (iv), a vector $`x\in\ker L\setminus\ker A` gives
$`F_\varphi(tx)=F_\varphi(0)` for all $`t`, while dominated convergence gives
$`F_\varphi(tx)\to\int w_\varphi\mathbf 1_{\{Ax=0\}}\mathrm dm<F_\varphi(0)`.
:::

:::definition "aux:torus" (lean := "OperatorRidgelet.Torus, OperatorRidgelet.torusHaar, OperatorRidgelet.TorusL2, OperatorRidgelet.TorusL2C, OperatorRidgelet.torusTranslate, OperatorRidgelet.torusTranslateC, OperatorRidgelet.convDirection, OperatorRidgelet.convOutput, OperatorRidgelet.torusOne, OperatorRidgelet.torusCharacter, OperatorRidgelet.torusFourierCoeff, OperatorRidgelet.torusFreqNormSq, OperatorRidgelet.besselOperator") (uses := "aux:operator-layer")
The torus $`\mathbb T^d=(\mathbb R/2\pi\mathbb Z)^d` with normalized Haar measure,
$`H=L^2(\mathbb T^d;\mathbb R)` and $`Y=L^2(\mathbb T^d)`, the translations
$`(\tau_zx)(t)=x(t-z)`, the convolution-layer data $`a_y=k(y-\cdot)` and
$`b_y=\psi(\cdot-y)`, the constant function $`1`, the characters
$`e_n(t)=e^{i\langle n,t\rangle}` and Fourier coefficients $`\widehat f(n)`, and the Bessel
operator $`(I-\Delta)^{-s}`, multiplying the $`n`-th Fourier coefficient by $`(1+|n|^2)^{-s}`.
:::

:::proposition "ex:convolution" (lean := "OperatorRidgelet.Paper.ex_convolution_i, OperatorRidgelet.Paper.ex_convolution_ii, OperatorRidgelet.Paper.ex_convolution_iii, OperatorRidgelet.Paper.ex_convolution_iv, OperatorRidgelet.Paper.ex_convolution_v, OperatorRidgelet.Paper.ex_convolution_vi, OperatorRidgelet.Paper.ex_convolution_vii, OperatorRidgelet.Paper.ex_convolution_viii, OperatorRidgelet.Paper.ex_convolution_ix, OperatorRidgelet.Paper.ex_convolution_x, OperatorRidgelet.Paper.ex_convolution_xi, OperatorRidgelet.Paper.ex_convolution_xii, OperatorRidgelet.Paper.ex_convolution_xiii") (uses := "aux:torus, aux:operator-layer, aux:cylindrical, aux:centered-gaussian, def:ridgelet-analysis, ex:operator-layer")
Let $`k,\psi\in L^2(\mathbb T^d;\mathbb R)`, $`a_y=k(y-\cdot)`, and $`b_y=\psi(\cdot-y)`.
Then $`\langle a_y,x\rangle=(k*x)(y)` (i), the layer is $`\mathcal F(x)=\psi*\beta(k*x)`
(ii), $`\|A\|_\infty=\|k\|_2` (iii), $`\int\|b_y\|\mathrm dy=\|\psi\|_2` (iv), the standing
hypotheses hold (v), and $`\mathcal F` commutes with all translations (vi) and with every
isometry of $`\mathbb T^d` fixing $`k` and $`\psi` (vii). If $`\widehat k(n)\ne0` for
infinitely many $`n`, then $`A` has infinite rank (viii); with $`\varphi\equiv1`,
$`F_1(x)=\widehat\psi(0)\int_{\mathbb T^d}\beta((k*x)(y))\mathrm dy` (ix), which is not
cylindrical when moreover $`\widehat\psi(0)\ne0` (x). The operator $`(I-\Delta)^{-s}` with
$`s>d/2` is an injective trace-class covariance (xi) and translation invariant (xii), and for
$`Q=P=(I-\Delta)^{-s}` the transform is equivariant:
$`R_\rho[f\circ\tau_z](a,c)=R_\rho f(\tau_za,c)` (xiii).
:::

:::proof "ex:convolution"
With normalized Haar measure $`\|a_y\|=\|k\|_2` and $`\|b_y\|=\|\psi\|_2`, convolutions
commute with translations and with isometries fixing their kernels, $`\beta` acts pointwise,
$`A` is diagonal in the Fourier basis with entries $`\widehat k(n)`, $`w_1=\widehat\psi(0)`
is a nonzero constant so {bpref "ex:operator-layer"}[] (iv) applies, and $`(I-\Delta)^{-s}`
has eigenvalues $`(1+|n|^2)^{-s}`, summable for $`s>d/2`.
:::

:::definition "aux:dirichlet" (lean := "OperatorRidgelet.UnitOpenInterval, OperatorRidgelet.UnitL2, OperatorRidgelet.UnitL2C, OperatorRidgelet.dirichletKernel, OperatorRidgelet.dirichletKernelFn, OperatorRidgelet.dirichletDirection, OperatorRidgelet.dirichletOutput, OperatorRidgelet.dirichletSolution, OperatorRidgelet.integralOperator, OperatorRidgelet.dirichletOperator, OperatorRidgelet.dirichletEigenvalue, OperatorRidgelet.dirichletEigenfunction, OperatorRidgelet.dirichletReLUTruncation") (uses := "aux:operator-layer, aux:relu-identities")
The interval $`\Omega=(0,1)` with Lebesgue measure, $`H=Y=L^2(0,1)`, the Green kernel
$`g(y,t)=\sinh(\min(y,t))\sinh(1-\max(y,t))/\sinh1`, the layer data $`a_y=b_y=g(y,\cdot)`,
the Dirichlet solution operator $`\mathsf G=(I-\partial_t^2)^{-1}` as the integral operator
with kernel $`g`, its eigenvalues $`\lambda_n=(1+\pi^2n^2)^{-1}` and eigenfunctions
$`e_n(t)=\sqrt2\sin(n\pi t)`, and the $`2N`-neuron ReLU truncation
$`\mathsf G_Nx=\sum_{n=1}^N\lambda_n[\operatorname{ReLU}(\langle e_n,x\rangle)-\operatorname{ReLU}(-\langle e_n,x\rangle)]e_n`.
:::

:::proposition "ex:dirichlet" (lean := "OperatorRidgelet.Paper.ex_dirichlet_i, OperatorRidgelet.Paper.ex_dirichlet_ii, OperatorRidgelet.Paper.ex_dirichlet_iii, OperatorRidgelet.Paper.ex_dirichlet_iv, OperatorRidgelet.Paper.ex_dirichlet_v, OperatorRidgelet.Paper.ex_dirichlet_vi, OperatorRidgelet.Paper.ex_dirichlet_vii, OperatorRidgelet.Paper.ex_dirichlet_viii, OperatorRidgelet.Paper.ex_dirichlet_ix, OperatorRidgelet.Paper.ex_dirichlet_x, OperatorRidgelet.Paper.ex_dirichlet_xi") (uses := "aux:dirichlet, aux:operator-layer, aux:relu-identities, aux:trace-class-operators, ex:operator-layer")
$`(\mathsf Gx)(y)=\int_0^1g(y,t)x(t)\,\mathrm dt` (i) and $`u=\mathsf Gx` solves
$`-u''+u=x`, $`u(0)=u(1)=0` (ii); $`\mathsf Ge_n=\lambda_ne_n` (iii), so $`\mathsf G` is an
injective trace-class covariance (iv) of infinite rank (v), and
$`\|A\|_\infty\le\sup_y\|g(y,\cdot)\|_2<\infty` (vi). With $`a_y=b_y=g(y,\cdot)` the
neural-operator layer example applies (vii) and the layer is
$`\mathcal F(x)=\mathsf G\,\beta(\mathsf Gx)` (viii), one Picard step for the semilinear
equation $`-u''+u=\beta(u)+x`. The linear operator is an exact ReLU network,
$`\mathsf Gx=\sum_n\lambda_ne_n[\operatorname{ReLU}(\langle e_n,x\rangle)-\operatorname{ReLU}(-\langle e_n,x\rangle)]`
(ix), whose $`2N`-neuron truncation has error at most $`\lambda_{N+1}\|x\|` (x) with
$`\lambda_{N+1}\le\pi^{-2}(N+1)^{-2}` (xi).
:::

:::proof "ex:dirichlet"
Direct differentiation shows that $`g(y,\cdot)` solves the boundary value problem with a
unit jump of the derivative at $`t=y`, the eigenpairs are checked by
$`-e_n''+e_n=(1+\pi^2n^2)e_n`, the kernel is continuous and bounded so
{bpref "ex:operator-layer"}[] applies, the ReLU expansion is the spectral theorem with
$`u=\operatorname{ReLU}(u)-\operatorname{ReLU}(-u)`, and orthogonality gives
$`\|\mathsf Gx-\mathsf G_Nx\|^2=\sum_{n>N}\lambda_n^2\langle e_n,x\rangle^2\le\lambda_{N+1}^2\|x\|^2`.
:::
