import Architect
import OperatorRidgelet.Paper.Examples

/-!
# LeanArchitect metadata for Section 7 (genuinely infinite-dimensional examples) and Appendix E

`attribute [blueprint ...]` commands for the declarations of `OperatorRidgelet.Paper.Examples` and
the definitions it uses.  Labels are the manuscript labels with the part appended; auxiliary
definitions carry `examples:` labels.  Statements whose proof is still `sorry` carry
`(notReady := true)`.
-/

/-! ## Definitions -/

attribute [blueprint "examples:is-cylindrical"
  (statement := /-- A function $f$ on $H$ is cylindrical if $f=\tilde f\circ L$ for a
    finite-rank linear map $L:H\to\mathbb R^m$. -/)
  (hasProof := false)] OperatorRidgelet.IsCylindrical

attribute [blueprint "examples:has-infinite-rank"
  (statement := /-- A linear map has infinite rank when its range is not finite dimensional. -/)
  (hasProof := false)] OperatorRidgelet.HasInfiniteRank

attribute [blueprint "examples:is-positive-sqrt"
  (statement := /-- $S$ is the positive square root of $Q$: $S$ is positive self-adjoint and
    $S^2=Q$. -/)
  (hasProof := false)] OperatorRidgelet.IsPositiveSqrt

attribute [blueprint "examples:has-eigenbasis"
  (statement := /-- $(e_i)$ is an orthonormal eigenbasis of $M$ with eigenvalues $(w_i)$:
    $Me_i=w_ie_i$. -/)
  (hasProof := false)] OperatorRidgelet.HasEigenbasis

attribute [blueprint "examples:fredholm-det-along"
  (statement := /-- The product $\prod_i(1+\langle Me_i,e_i\rangle)$ along a Hilbert basis. -/)
  (hasProof := false)] OperatorRidgelet.fredholmDetAlong

attribute [blueprint "examples:fredholm-det"
  (statement := /-- The Fredholm determinant $\det(I+M)=\prod_i(1+m_i)$ over the eigenvalues of
    $M$, computed along an orthonormal eigenbasis. -/)
  (hasProof := false)] OperatorRidgelet.fredholmDet

attribute [blueprint "examples:resolvent-form"
  (statement := /-- The quadratic form $\langle S(I+M)^{-1}Sx,x\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.resolventForm

attribute [blueprint "examples:gaussian-act-deriv2"
  (statement := /-- $\varphi''(b)=(b^2-1)e^{-b^2/2}$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianActDeriv2

attribute [blueprint "examples:gaussian-smooth"
  (statement := /-- The convolution $(\rho*\phi_v)(c)=\int_{\mathbb R}\rho(c-t)\,\mathcal
    N(0,v)(\mathrm dt)$ with the centred Gaussian of variance $v\ge0$
    ($\phi_0=\delta_0$). -/)
  (hasProof := false)] OperatorRidgelet.gaussianSmooth

attribute [blueprint "examples:gaussian-target"
  (statement := /-- The Gaussian target $f_W(x)=e^{-\langle Wx,x\rangle/2}$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianTarget

attribute [blueprint "examples:gaussian-kappa"
  (statement := /-- $\kappa_W(\xi)=\langle Q^{1/2}(I+M)^{-1}Q^{1/2}\xi,\xi\rangle$ with
    $M=Q^{1/2}WQ^{1/2}$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianKappa

attribute [blueprint "examples:gaussian-target-resolvent"
  (statement := /-- $S_W=Q^{1/2}(I+M)^{-1}Q^{1/2}$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianTargetResolvent

attribute [blueprint "examples:mixture-layer-covariance"
  (statement := /-- $\Sigma_s=2sP^{1/2}(I+2sP^{1/2}S_WP^{1/2})^{-1}P^{1/2}$. -/)
  (hasProof := false)] OperatorRidgelet.mixtureLayerCovariance

attribute [blueprint "examples:mem-spectral-core"
  (statement := /-- $f\in\mathcal D_\alpha$ for a function $f$: $f\in L^2(\mu)$ and $\mathcal
    G_\mu f\in L^2(\nu)$. -/)
  (hasProof := false)] OperatorRidgelet.MemSpectralCore

attribute [blueprint "examples:mem-spectral-core-vec"
  (statement := /-- $f\in\mathcal D_\alpha(Y)$ for a $Y$-valued function $f$. -/)
  (hasProof := false)] OperatorRidgelet.MemSpectralCoreVec

attribute [blueprint "examples:to-lp-or-zero"
  (statement := /-- The element of $L^p(\mu)$ represented by $f$, and $0$ when $f\notin
    L^p(\mu)$. -/)
  (hasProof := false)] OperatorRidgelet.toLpOrZero

attribute [blueprint "examples:gaussian-parameter-relu"
  (statement := /-- $F_Q(x)=\int_H\operatorname{ReLU}(\langle a,x\rangle)\,\mathcal
    N(0,Q)(\mathrm da)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianParameterReLU

attribute [blueprint "examples:gaussian-parameter-gauss"
  (statement := /-- $\Phi_Q(x)=\int_H\Phi(\langle a,x\rangle)\,\mathcal N(0,Q)(\mathrm da)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianParameterGauss

attribute [blueprint "examples:hinge-coefficient-measure"
  (statement := /-- The ReLU coefficient measure of a Gaussian-activation network with
    coefficient density $\gamma$: the pushforward of
    $\varphi''(b)\gamma(a,c)\,\lambda(\mathrm da,\mathrm dc)\,\mathrm db$ under
    $(a,c,b)\mapsto(a,c-b)$. -/)
  (hasProof := false)] OperatorRidgelet.hingeCoefficientMeasure

attribute [blueprint "examples:is-layer-data"
  (statement := /-- The standing hypotheses of the neural-operator layer: $y\mapsto a_y$ is
    Borel and bounded, $y\mapsto b_y$ is Borel with $\int\|b_y\|\,m(\mathrm
    dy)<\infty$. -/)
  (hasProof := false)] OperatorRidgelet.IsLayerData

attribute [blueprint "examples:layer-sup-norm"
  (statement := /-- $\|A\|_\infty=\sup_y\|a_y\|$. -/)
  (hasProof := false)] OperatorRidgelet.layerSupNorm

attribute [blueprint "examples:operator-layer"
  (statement := /-- The neural-operator layer $\mathcal F(x)=B\beta(Ax)=\int_\Omega
    b_y\beta(\langle a_y,x\rangle)\,m(\mathrm dy)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorLayer

attribute [blueprint "examples:layer-weight"
  (statement := /-- $w_\varphi(y)=\langle b_y,\varphi\rangle_Y$. -/)
  (hasProof := false)] OperatorRidgelet.layerWeight

attribute [blueprint "examples:layer-observable"
  (statement := /-- The scalar observable $F_\varphi(x)=\langle\mathcal F(x),\varphi\rangle_Y$. -/)
  (hasProof := false)] OperatorRidgelet.layerObservable

attribute [blueprint "examples:layer-a"
  (statement := /-- The operator $A:H\to L^2(m)$, $(Ax)(y)=\langle a_y,x\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.layerA

attribute [blueprint "examples:layer-covariance"
  (statement := /-- $S_y=Q-(1+\sigma_y^2)^{-1}(Qa_y)\otimes(Qa_y)$, $\sigma_y^2=\langle
    Qa_y,a_y\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.layerCovariance

attribute [blueprint "examples:layer-measure"
  (statement := /-- The $Y$-valued coefficient measure $\Gamma=\iota_\#(b_y\,m(\mathrm dy))$,
    $\iota(y)=(a_y,0)$. -/)
  (hasProof := false)] OperatorRidgelet.layerMeasure

attribute [blueprint "examples:layer-hinge-measure"
  (statement := /-- The coefficient measure of the ReLU form of the Gaussian-activation layer:
    the pushforward of $\varphi''(b)\,b_y\,m(\mathrm dy)\,\mathrm db$ under
    $(y,b)\mapsto(a_y,-b)$. -/)
  (hasProof := false)] OperatorRidgelet.layerHingeMeasure

attribute [blueprint "examples:torus"
  (statement := /-- The torus $\mathbb T^d=(\mathbb R/2\pi\mathbb Z)^d$. -/)
  (hasProof := false)] OperatorRidgelet.Torus

attribute [blueprint "examples:torus-haar"
  (statement := /-- The normalized Haar measure on $\mathbb T^d$. -/)
  (hasProof := false)] OperatorRidgelet.torusHaar

attribute [blueprint "examples:torus-l2"
  (statement := /-- $L^2(\mathbb T^d;\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.TorusL2

attribute [blueprint "examples:torus-l2c"
  (statement := /-- $L^2(\mathbb T^d)$. -/)
  (hasProof := false)] OperatorRidgelet.TorusL2C

attribute [blueprint "examples:torus-translate"
  (statement := /-- The translation $(\tau_zx)(t)=x(t-z)$ on $L^2(\mathbb T^d;\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.torusTranslate

attribute [blueprint "examples:torus-translate-c"
  (statement := /-- The translation $(\tau_zu)(t)=u(t-z)$ on $L^2(\mathbb T^d)$. -/)
  (hasProof := false)] OperatorRidgelet.torusTranslateC

attribute [blueprint "examples:conv-direction"
  (statement := /-- The direction $a_y=k(y-\cdot)$ of the convolution layer. -/)
  (hasProof := false)] OperatorRidgelet.convDirection

attribute [blueprint "examples:conv-output"
  (statement := /-- The output $b_y=\psi(\cdot-y)$ of the convolution layer. -/)
  (hasProof := false)] OperatorRidgelet.convOutput

attribute [blueprint "examples:torus-one"
  (statement := /-- The constant function $1$ in $L^2(\mathbb T^d)$. -/)
  (hasProof := false)] OperatorRidgelet.torusOne

attribute [blueprint "examples:torus-character"
  (statement := /-- The character $e_n(t)=e^{i\langle n,t\rangle}$ of $\mathbb T^d$,
    $n\in\mathbb Z^d$. -/)
  (hasProof := false)] OperatorRidgelet.torusCharacter

attribute [blueprint "examples:torus-fourier-coeff"
  (statement := /-- The Fourier coefficient $\widehat f(n)=\int_{\mathbb T^d}f(t)e^{-i\langle
    n,t\rangle}\,\mathrm dt$. -/)
  (hasProof := false)] OperatorRidgelet.torusFourierCoeff

attribute [blueprint "examples:torus-freq-norm-sq"
  (statement := /-- $|n|^2=\sum_jn_j^2$ for $n\in\mathbb Z^d$. -/)
  (hasProof := false)] OperatorRidgelet.torusFreqNormSq

attribute [blueprint "examples:bessel-operator"
  (statement := /-- The Bessel operator $(I-\Delta)^{-s}$ on $L^2(\mathbb T^d;\mathbb R)$,
    multiplying the $n$-th Fourier coefficient by $(1+|n|^2)^{-s}$. -/)
  (hasProof := false)] OperatorRidgelet.besselOperator

attribute [blueprint "examples:unit-open-interval"
  (statement := /-- The open interval $(0,1)$ with Lebesgue measure. -/)
  (hasProof := false)] OperatorRidgelet.UnitOpenInterval

attribute [blueprint "examples:unit-l2"
  (statement := /-- $L^2(0,1)$, real valued. -/)
  (hasProof := false)] OperatorRidgelet.UnitL2

attribute [blueprint "examples:unit-l2c"
  (statement := /-- $L^2(0,1)$, complex valued. -/)
  (hasProof := false)] OperatorRidgelet.UnitL2C

attribute [blueprint "examples:dirichlet-kernel"
  (statement := /-- The Green kernel $g(y,t)=\sinh(\min(y,t))\sinh(1-\max(y,t))/\sinh1$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletKernel

attribute [blueprint "examples:dirichlet-kernel-fn"
  (statement := /-- $g(y,\cdot)$ as an element of $L^2(0,1)$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletKernelFn

attribute [blueprint "examples:dirichlet-direction"
  (statement := /-- The direction $a_y=g(y,\cdot)$ of the Dirichlet layer. -/)
  (hasProof := false)] OperatorRidgelet.dirichletDirection

attribute [blueprint "examples:dirichlet-output"
  (statement := /-- The output $b_y=g(y,\cdot)$ of the Dirichlet layer. -/)
  (hasProof := false)] OperatorRidgelet.dirichletOutput

attribute [blueprint "examples:dirichlet-solution"
  (statement := /-- $u(y)=\int_0^1g(y,t)x(t)\,\mathrm dt$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletSolution

attribute [blueprint "examples:integral-operator"
  (statement := /-- The integral operator on $L^2(m)$ with kernel $k$. -/)
  (hasProof := false)] OperatorRidgelet.integralOperator

attribute [blueprint "examples:dirichlet-operator"
  (statement := /-- The Dirichlet solution operator $\mathsf G=(I-\partial_t^2)^{-1}$ on
    $L^2(0,1)$, the integral operator with kernel $g$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletOperator

attribute [blueprint "examples:dirichlet-eigenvalue"
  (statement := /-- $\lambda_n=(1+\pi^2n^2)^{-1}$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletEigenvalue

attribute [blueprint "examples:dirichlet-eigenfunction"
  (statement := /-- $e_n(t)=\sqrt2\sin(n\pi t)$ in $L^2(0,1)$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletEigenfunction

attribute [blueprint "examples:dirichlet-relu-truncation"
  (statement := /-- The $2N$-neuron ReLU truncation $\mathsf
    G_Nx=\sum_{n=1}^N\lambda_n[\operatorname{ReLU}(\langle
    e_n,x\rangle)-\operatorname{ReLU}(-\langle e_n,x\rangle)]e_n$. -/)
  (hasProof := false)] OperatorRidgelet.dirichletReLUTruncation

/-! ## Auxiliary lemmas -/

attribute [blueprint "examples:gauss-fourier-congr-ae"
  (statement := /-- $\mathcal G_\mu f=\mathcal G_\mu g$ when $f=g$ $\mu$-almost everywhere. -/)]
  OperatorRidgelet.gaussFourier_congr_ae

attribute [blueprint "examples:to-lp-mem-spectral-core-iff"
  (statement := /-- For $f\in L^2(\mu)$, the class of $f$ lies in $\mathcal D$ if and only if
    $\mathcal G_\mu f\in L^2(\nu)$. -/)]
  OperatorRidgelet.toLp_mem_spectralCore_iff

attribute [blueprint "examples:mem-spectral-core-iff"
  (statement := /-- $f\in\mathcal D_\alpha$ as a function if and only if $f\in L^2(\mu)$ and its
    class lies in the submodule $\mathcal D$. -/)]
  OperatorRidgelet.memSpectralCore_iff

/-! ## Statements -/

attribute [blueprint "lem:gaussian-quadratic-i"
  (statement := /-- $M=\Sigma^{1/2}S\Sigma^{1/2}$ is trace class. -/)]
  OperatorRidgelet.Paper.lem_gaussian_quadratic_i

attribute [blueprint "lem:gaussian-quadratic-ii"
  (statement := /-- $\int_He^{i\langle x,\xi\rangle-\langle S\xi,\xi\rangle/2}\,\mathcal
    N(0,\Sigma)(\mathrm
    d\xi)=\det(I+M)^{-1/2}\exp(-\tfrac12\langle\Sigma^{1/2}(I+M)^{-1}\Sigma^{1/2}x,x\rangle)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_gaussian_quadratic_ii

attribute [blueprint "lem:gaussian-hinge-i-a"
  (statement := /-- $\int_{\mathbb R}(u-b)_+\varphi''(b)\,\mathrm db$ converges absolutely for
    each $u$. -/)]
  OperatorRidgelet.Paper.lem_gaussian_hinge_i_a

attribute [blueprint "lem:gaussian-hinge-i-b"
  (statement := /-- $\varphi(u)=\int_{\mathbb R}(u-b)_+\varphi''(b)\,\mathrm db$. -/)]
  OperatorRidgelet.Paper.lem_gaussian_hinge_i_b

attribute [blueprint "lem:gaussian-hinge-ii"
  (statement := /-- $\int_{\mathbb R}(1+|b|^k)|\varphi''(b)|\,\mathrm db<\infty$ for every
    $k\ge0$. -/)]
  OperatorRidgelet.Paper.lem_gaussian_hinge_ii

attribute [blueprint "ex:closed-form-i-a"
  (statement := /-- $\mathcal G_Qf_W(\xi)=D^{-1/2}e^{-\kappa_W(\xi)/2}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_i_a

attribute [blueprint "ex:closed-form-i-b"
  (statement := /-- $R_\rho f_W(a,c)=D^{-1/2}(\rho*\phi_{\kappa_W(a)})(c)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_i_b

attribute [blueprint "ex:closed-form-i-c"
  (statement := /-- $f_W\in\mathcal D_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_i_c

attribute [blueprint "ex:closed-form-i-d"
  (statement := /-- $f_W$ is not cylindrical when $W$ has infinite rank. -/)]
  OperatorRidgelet.Paper.ex_closed_form_i_d

attribute [blueprint "ex:closed-form-ii-a"
  (statement := /-- $G=\mathcal G_Qf_W$ is regular along rays. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_ii_a

attribute [blueprint "ex:closed-form-ii-b"
  (statement := /-- $T_\alpha f_W$ is represented by $g_G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_ii_b

attribute [blueprint "ex:closed-form-ii-c"
  (statement := /-- $g_G(x)=D^{-1/2}\int_0^\infty\det(I+2sP^{1/2}S_WP^{1/2})^{-1/2}
    \exp(-\tfrac12\langle\Sigma_sx,x\rangle)\,s^{\alpha/2-1}\,\mathrm ds$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_ii_c

attribute [blueprint "ex:closed-form-iii-a"
  (statement := /-- $R_\rho f_W=\gamma_G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_iii_a

attribute [blueprint "ex:closed-form-iii-b"
  (statement := /-- $R_\rho f_W$ has finite variation and second moment. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_iii_b

attribute [blueprint "ex:closed-form-iii-c"
  (statement := /-- For real, globally Lipschitz, non-polynomial $\beta$, $S_\beta[R_\rho
    f_W\lambda_\alpha]=C^{(\alpha)}_{\beta,\rho}g_G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_iii_c

attribute [blueprint "ex:closed-form-iii-d"
  (statement := /-- The sampled network of $R_\rho f_W\lambda_\alpha$ converges at the rate
    $N^{-1/2}$ in $C(K)$ as in the spectral Barron bound. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_closed_form_iii_d

attribute [blueprint "ex:core-elements-iv"
  (statement := /-- $f_W\in\mathcal D_\alpha$ for every $\alpha>0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_core_elements_iv

attribute [blueprint "ex:core-elements-v"
  (statement := /-- The components $F_\varphi$ of the Gaussian-activation operator layers belong
    to $\mathcal D_\alpha$ for every $\alpha>0$. -/)]
  OperatorRidgelet.Paper.ex_core_elements_v

attribute [blueprint "ex:gaussian-parameter-i"
  (statement := /-- $F_Q(x)=\sqrt{\langle Qx,x\rangle/2\pi}$. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_i

attribute [blueprint "ex:gaussian-parameter-ii"
  (statement := /-- $\Phi_Q(x)=(1+\langle Qx,x\rangle)^{-1/2}$. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_ii

attribute [blueprint "ex:gaussian-parameter-iii"
  (statement := /-- $\Phi_Q(x)=\int_{H\times\mathbb R}\operatorname{ReLU}(\langle
    a,x\rangle-b)\varphi''(b)\,\mathcal N(0,Q)(\mathrm da)\,\mathrm db$. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_iii

attribute [blueprint "ex:gaussian-parameter-iv"
  (statement := /-- $F_Q$ is not cylindrical. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_iv

attribute [blueprint "ex:gaussian-parameter-v"
  (statement := /-- $\Phi_Q$ is not cylindrical. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_v

attribute [blueprint "ex:gaussian-parameter-vi-a"
  (statement := /-- A Gaussian-activation network with finite coefficient measure is the ReLU
    network with the hinge coefficient measure. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_gaussian_parameter_vi_a

attribute [blueprint "ex:gaussian-parameter-vi-b"
  (statement := /-- The hinge coefficient measure is finite. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_vi_b

attribute [blueprint "ex:gaussian-parameter-vi-c"
  (statement := /-- The hinge coefficient measure has all parameter moments finite. -/)]
  OperatorRidgelet.Paper.ex_gaussian_parameter_vi_c

attribute [blueprint "cor:relu-discretization"
  (statement := /-- $\mathbb E\|F_{Q,N}-F_Q\|_{C(K)}\le8R_K\sqrt{\operatorname{tr}Q}/\sqrt N$
    for every compact $K$. -/)]
  OperatorRidgelet.Paper.cor_relu_discretization

attribute [blueprint "ex:operator-layer-i-a"
  (statement := /-- $\mathcal F=S_\beta[\Gamma]$ with $\Gamma=\iota_\#(b_y\,m(\mathrm dy))$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_i_a

attribute [blueprint "ex:operator-layer-i-b"
  (statement := /-- $\|\Gamma\|_{\mathrm{TV}}\le\int\|b_y\|\,m(\mathrm dy)$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_i_b

attribute [blueprint "ex:operator-layer-i-c"
  (statement := /-- The second parameter moment of $\Gamma$ is at most $\|A\|_\infty^2$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_i_c

attribute [blueprint "ex:operator-layer-i-d"
  (statement := /-- Width-$N$ networks approximate $\mathcal F$ at the rate $N^{-1/2}$ in
    $L^2(\zeta;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_i_d

attribute [blueprint "ex:operator-layer-i-e"
  (statement := /-- $\mathbb
    E\|F_{\varphi,N}-F_\varphi\|_{C(K)}\le\frac{8\|w_\varphi\|_{L^1(m)}}{\sqrt
    N}(|\beta(0)|+\operatorname{Lip}(\beta)R_K\|A\|_\infty)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_i_e

attribute [blueprint "ex:operator-layer-ii-a"
  (statement := /-- $F_\varphi\in\mathcal D_\alpha$ for every $\alpha>0$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_a

attribute [blueprint "ex:operator-layer-ii-b"
  (statement := /-- $\mathcal G_QF_\varphi(\xi)=\int_\Omega
    w_\varphi(y)(1+\sigma_y^2)^{-1/2}e^{-\langle S_y\xi,\xi\rangle/2}\,m(\mathrm
    dy)$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_b

attribute [blueprint "ex:operator-layer-ii-c"
  (statement := /-- $R_\rho F_\varphi(a,c)=\int_\Omega
    w_\varphi(y)(1+\sigma_y^2)^{-1/2}(\rho*\phi_{\langle
    S_ya,a\rangle})(c)\,m(\mathrm dy)$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_c

attribute [blueprint "ex:operator-layer-ii-d"
  (statement := /-- $S_y\ge(1+\|Q\|\|A\|_\infty^2)^{-1}Q$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_d

attribute [blueprint "ex:operator-layer-ii-e"
  (statement := /-- $\mathcal G_QF_\varphi$ is regular along rays. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_e

attribute [blueprint "ex:operator-layer-ii-f"
  (statement := /-- The reconstruction formulas hold for $F_\varphi$: $T_\alpha F_\varphi$ is
    represented by $g_{\mathcal G_QF_\varphi}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_f

attribute [blueprint "ex:operator-layer-ii-g"
  (statement := /-- $R_\rho F_\varphi=\gamma_{\mathcal G_QF_\varphi}$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_g

attribute [blueprint "ex:operator-layer-ii-h"
  (statement := /-- $R_\rho F_\varphi$ has finite variation and moments. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_h

attribute [blueprint "ex:operator-layer-ii-i"
  (statement := /-- $R_\rho F_\varphi$ synthesizes, with any real Lipschitz non-polynomial
    $\beta'$, the target $C^{(\alpha)}_{\beta',\rho}T_\alpha F_\varphi$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_i

attribute [blueprint "ex:operator-layer-ii-j"
  (statement := /-- The sampled network of $R_\rho F_\varphi\lambda_\alpha$ converges at the
    finite-width rate of the spectral Barron bound. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_j

attribute [blueprint "ex:operator-layer-ii-k"
  (statement := /-- $\mathcal F\in\mathcal D_\alpha(Y)$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_k

attribute [blueprint "ex:operator-layer-ii-l"
  (statement := /-- $\mathcal G_Q\mathcal F(\xi)=\int_\Omega(1+\sigma_y^2)^{-1/2}e^{-\langle
    S_y\xi,\xi\rangle/2}b_y\,m(\mathrm dy)$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_ii_l

attribute [blueprint "ex:operator-layer-ii-m"
  (statement := /-- $\mathcal G_Q\mathcal F$ is regular along rays. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_m

attribute [blueprint "ex:operator-layer-ii-n"
  (statement := /-- $R_\rho\mathcal F=\gamma_{\mathcal G_Q\mathcal F}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_n

attribute [blueprint "ex:operator-layer-ii-o"
  (statement := /-- $R_\rho\mathcal F$ has finite variation and moments. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_o

attribute [blueprint "ex:operator-layer-ii-p"
  (statement := /-- $R_\rho\mathcal F$ synthesizes, with any real Lipschitz non-polynomial
    $\beta'$, the $Y$-valued target $C^{(\alpha)}_{\beta',\rho}g_{\mathcal
    G_Q\mathcal F}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_ii_p

attribute [blueprint "ex:operator-layer-iii-a"
  (statement := /-- $\mathcal F(x)=\int_{\Omega\times\mathbb
    R}b_y\varphi''(b)\operatorname{ReLU}(\langle a_y,x\rangle-b)\,m(\mathrm
    dy)\,\mathrm db$. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_iii_a

attribute [blueprint "ex:operator-layer-iii-b"
  (statement := /-- The Gaussian-activation layer is the ReLU network with the hinge coefficient
    measure. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_operator_layer_iii_b

attribute [blueprint "ex:operator-layer-iii-c"
  (statement := /-- The hinge coefficient measure of the layer is finite. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_iii_c

attribute [blueprint "ex:operator-layer-iii-d"
  (statement := /-- The hinge coefficient measure of the layer has all moments finite. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_iii_d

attribute [blueprint "ex:operator-layer-iv"
  (statement := /-- If $A$ has infinite rank, $\beta=\Phi$, and $w_\varphi>0$ $m$-a.e., then
    $F_\varphi$ is not cylindrical. -/)]
  OperatorRidgelet.Paper.ex_operator_layer_iv

attribute [blueprint "ex:convolution-i"
  (statement := /-- $\langle a_y,x\rangle=(k*x)(y)$. -/)]
  OperatorRidgelet.Paper.ex_convolution_i

attribute [blueprint "ex:convolution-ii"
  (statement := /-- $\mathcal F(x)=\psi*\beta(k*x)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_ii

attribute [blueprint "ex:convolution-iii"
  (statement := /-- $\|A\|_\infty=\|k\|_2$. -/)]
  OperatorRidgelet.Paper.ex_convolution_iii

attribute [blueprint "ex:convolution-iv"
  (statement := /-- $\int\|b_y\|\,\mathrm dy=\|\psi\|_2$. -/)]
  OperatorRidgelet.Paper.ex_convolution_iv

attribute [blueprint "ex:convolution-v"
  (statement := /-- The convolution layer satisfies the standing hypotheses of the
    neural-operator layer. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_v

attribute [blueprint "ex:convolution-vi"
  (statement := /-- $\mathcal F$ commutes with all translations of $\mathbb T^d$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_vi

attribute [blueprint "ex:convolution-vii"
  (statement := /-- $\mathcal F$ commutes with every isometric automorphism of $\mathbb T^d$
    that fixes $k$ and $\psi$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_vii

attribute [blueprint "ex:convolution-viii"
  (statement := /-- If $\widehat k(n)\ne0$ for infinitely many $n$, then $A$ has infinite rank. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_viii

attribute [blueprint "ex:convolution-ix"
  (statement := /-- $F_1(x)=\widehat\psi(0)\int_{\mathbb T^d}\beta((k*x)(y))\,\mathrm dy$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_ix

attribute [blueprint "ex:convolution-x"
  (statement := /-- If $\widehat k(n)\ne0$ for infinitely many $n$ and $\widehat\psi(0)\ne0$,
    then $F_1$ is not cylindrical. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_x

attribute [blueprint "ex:convolution-xi"
  (statement := /-- $(I-\Delta)^{-s}$ is injective, positive, self-adjoint, and trace class for
    $s>d/2$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_xi

attribute [blueprint "ex:convolution-xii"
  (statement := /-- $(I-\Delta)^{-s}$ is translation invariant. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_xii

attribute [blueprint "ex:convolution-xiii"
  (statement := /-- $R_\rho[f\circ\tau_z](a,c)=R_\rho f(\tau_za,c)$ for every translation
    $\tau_z$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_convolution_xiii

attribute [blueprint "ex:dirichlet-i"
  (statement := /-- $(\mathsf Gx)(y)=\int_0^1g(y,t)x(t)\,\mathrm dt$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_i

attribute [blueprint "ex:dirichlet-ii"
  (statement := /-- $u=\mathsf Gx$ solves $-u''+u=x$, $u(0)=u(1)=0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_ii

attribute [blueprint "ex:dirichlet-iii"
  (statement := /-- $\mathsf Ge_n=\lambda_ne_n$ with $\lambda_n=(1+\pi^2n^2)^{-1}$,
    $e_n(t)=\sqrt2\sin(n\pi t)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_iii

attribute [blueprint "ex:dirichlet-iv"
  (statement := /-- $\mathsf G$ is injective, positive, self-adjoint, and trace class. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_iv

attribute [blueprint "ex:dirichlet-v"
  (statement := /-- $\mathsf G$ has infinite rank. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_v

attribute [blueprint "ex:dirichlet-vi"
  (statement := /-- $\|A\|_\infty\le\sup_y\|g(y,\cdot)\|_2<\infty$. -/)]
  OperatorRidgelet.Paper.ex_dirichlet_vi

attribute [blueprint "ex:dirichlet-vii"
  (statement := /-- With $a_y=b_y=g(y,\cdot)$ the neural-operator layer example applies. -/)]
  OperatorRidgelet.Paper.ex_dirichlet_vii

attribute [blueprint "ex:dirichlet-viii"
  (statement := /-- The layer is $\mathcal F(x)=\mathsf G\beta(\mathsf Gx)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_viii

attribute [blueprint "ex:dirichlet-ix"
  (statement := /-- $\mathsf Gx=\sum_n\lambda_ne_n[\operatorname{ReLU}(\langle
    e_n,x\rangle)-\operatorname{ReLU}(-\langle e_n,x\rangle)]$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_ix

attribute [blueprint "ex:dirichlet-x"
  (statement := /-- The $2N$-neuron truncation has error at most $\lambda_{N+1}\|x\|$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_dirichlet_x

attribute [blueprint "ex:dirichlet-xi"
  (statement := /-- $\lambda_{N+1}\le\pi^{-2}(N+1)^{-2}=O(N^{-2})$. -/)]
  OperatorRidgelet.Paper.ex_dirichlet_xi
