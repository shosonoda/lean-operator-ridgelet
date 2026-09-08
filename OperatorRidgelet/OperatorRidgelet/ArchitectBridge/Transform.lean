import Architect
import OperatorRidgelet.Paper.Transform
import OperatorRidgelet.Transform.Infra

/-!
# LeanArchitect metadata for Section 3 (the ridgelet transform) and Appendices A, G, H, I

`attribute [blueprint ...]` commands for the declarations of `OperatorRidgelet.Paper.Transform`
and the definitions it uses.  Labels are the manuscript labels with the part appended; auxiliary
definitions carry `transform:`, `finite-dim:`, and `filters:` labels, and the missing Gaussian
infrastructure carries the label `infra:gaussian-layers-exist`.
-/

/-! ## Definitions -/

attribute [blueprint "transform:character"
  (statement := /-- The analysis character is $x\mapsto e^{-i\langle x,\xi\rangle}$. -/)
  (hasProof := false)] OperatorRidgelet.character

attribute [blueprint "transform:gauss-fourier"
  (statement := /-- The weighted Fourier transform is $\mathcal G_\mu
    f(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu(\mathrm dx)$; for
    $\mu=\mu_Q$ it is $\mathcal G_Q$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourier

attribute [blueprint "transform:line-fourier"
  (statement := /-- The one-dimensional Fourier transform $\widehat h(\omega)=\int_{\mathbb
    R}h(t)e^{-it\omega}\,\mathrm dt$ of a complex function. -/)
  (hasProof := false)] OperatorRidgelet.lineFourier

attribute [blueprint "transform:filter-fourier"
  (statement := /-- The Fourier transform $\widehat\rho(\omega)=\int_{\mathbb
    R}\rho(t)e^{-it\omega}\,\mathrm dt$ of a real filter. -/)
  (hasProof := false)] OperatorRidgelet.filterFourier

attribute [blueprint "transform:homogeneous"
  (statement := /-- A measure $\nu$ on $H$ is homogeneous of degree $\alpha$ when
    $(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu$ for every $\omega\ne0$. -/)
  (hasProof := false)] OperatorRidgelet.IsHomogeneous

attribute [blueprint "transform:trace-class-covariance"
  (statement := /-- An operator is an injective, positive, self-adjoint, trace-class covariance;
    the trace is taken along a Hilbert basis. -/)
  (hasProof := false)] OperatorRidgelet.IsTraceClassCovariance

attribute [blueprint "transform:centered-gaussian"
  (statement := /-- $\mu=\mathcal N(0,Q)$: a Borel probability measure with $\int_He^{i\langle
    x,\xi\rangle}\mu(\mathrm dx)=e^{-\langle Q\xi,\xi\rangle/2}$. -/)
  (hasProof := false)] OperatorRidgelet.IsCenteredGaussian

attribute [blueprint "transform:gaussian-layers"
  (statement := /-- A family $N_s=\mathcal N(0,2sP)$, $s>0$, of Gaussian layers with
    characteristic functionals $e^{-s\langle P\xi,\xi\rangle}$. -/)
  (hasProof := false)] OperatorRidgelet.IsCenteredGaussianLayers

attribute [blueprint "transform:mixture-weight"
  (statement := /-- The weight $s^{\alpha/2-1}\,\mathrm ds$ on a set of scales. -/)
  (hasProof := false)] OperatorRidgelet.mixtureWeight

attribute [blueprint "transform:gaussian-mixture-on"
  (statement := /-- The truncated mixture $\int_S\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds$
    over a set $S$ of scales, as a Giry-monad bind. -/)
  (hasProof := false)] OperatorRidgelet.gaussianMixtureOn

attribute [blueprint "transform:gaussian-mixture"
  (statement := /-- The homogeneous Gaussian mixture $\nu_\alpha=\int_0^\infty\mathcal
    N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianMixture

attribute [blueprint "transform:strong-law-set"
  (statement := /-- The set $E_t=\{x:\lim_n\frac1n\sum_{j\le n}\langle x,e_j\rangle^2/w_j=t\}$
    of the dilation obstruction. -/)
  (hasProof := false)] OperatorRidgelet.strongLawSet

attribute [blueprint "def:admissible-filter-cross"
  (statement := /-- $C^{(\alpha)}_{\rho_1,\rho_2}=\frac1{2\pi}\int_{\mathbb
    R}\widehat\rho_1(\omega)\overline{\widehat\rho_2(\omega)}|\omega|^{-\alpha}\,\mathrm
    d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.crossAdmissibilityConst

attribute [blueprint "def:admissible-filter-const"
  (statement := /-- $C^{(\alpha)}_\rho=\frac1{2\pi}\int_{\mathbb
    R}|\widehat\rho(\omega)|^2|\omega|^{-\alpha}\,\mathrm d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.admissibilityConst

attribute [blueprint "def:admissible-filter"
  (statement := /-- A real $\rho\in\mathcal S(\mathbb R)$ is $\alpha$-admissible if
    $0<C^{(\alpha)}_\rho<\infty$. -/)
  (hasProof := false)] OperatorRidgelet.IsAdmissible

attribute [blueprint "def:admissible-filter-bandpass"
  (statement := /-- $\rho$ is a band-pass filter if moreover $\widehat\rho\in C_c^\infty(\mathbb
    R\setminus\{0\})$ (and $\rho\ne0$). -/)
  (hasProof := false)] OperatorRidgelet.IsBandPass

attribute [blueprint "def:ridgelet-analysis"
  (statement := /-- The weighted ridgelet transform $R_\rho f(a,c)=\int_Hf(x)\rho(\langle
    a,x\rangle+c)\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.ridgelet

attribute [blueprint "def:ridgelet-analysis-parameter-measure"
  (statement := /-- The parameter measure $\lambda=\nu\otimes\mathrm dc$ on $H\times\mathbb R$. -/)
  (hasProof := false)] OperatorRidgelet.parameterMeasure

attribute [blueprint "transform:bias-fourier"
  (statement := /-- The partial Fourier transform in the bias,
    $\widehat\gamma(a,\omega)=\int_{\mathbb R}\gamma(a,c)e^{-i\omega c}\,\mathrm
    dc$. -/)
  (hasProof := false)] OperatorRidgelet.biasFourier

attribute [blueprint "def:spectral-coefficient-formula"
  (statement := /-- The explicit coefficient $\gamma_G(a,c)=\frac1{2\pi}\int_{\mathbb
    R}\widehat\rho(\omega)G(-\omega a)e^{i\omega c}\,\mathrm d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.coefficientFormula

attribute [blueprint "def:spectral-coefficient-bias-fourier"
  (statement := /-- $\gamma$ has partial Fourier transform $\Phi$ in the bias: Parseval's
    identity against Schwartz test functions holds for $\nu$-almost every
    direction. -/)
  (hasProof := false)] OperatorRidgelet.HasBiasFourier

attribute [blueprint "def:spectral-coefficient"
  (statement := /-- The coefficient $W_\rho G\in L^2(\lambda)$, the element whose partial
    Fourier transform in the bias is $\widehat\rho(\omega)G(-\omega a)$. -/)
  (hasProof := false)] OperatorRidgelet.spectralCoefficient

attribute [blueprint "def:spectral-space"
  (statement := /-- $\mathcal D=\{f\in L^2(\mu):\mathcal G_\mu f\in L^2(\nu)\}$. -/)
  (hasProof := false)] OperatorRidgelet.spectralCore

attribute [blueprint "def:spectral-space-inner"
  (statement := /-- $\langle f,g\rangle_{\mathcal E}=\int_H\mathcal G_\mu f\,\overline{\mathcal
    G_\mu g}\,\mathrm d\nu$. -/)
  (hasProof := false)] OperatorRidgelet.spectralInner

attribute [blueprint "def:spectral-space-fourier-lp"
  (statement := /-- $\mathcal G_\mu f$ as an element of $L^2(\nu)$ for $f\in\mathcal D$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierLp

attribute [blueprint "def:spectral-space-range"
  (statement := /-- $\mathcal K=\overline{\mathcal G_\mu(\mathcal D)}^{L^2(\nu)}$, which
    represents $\mathcal E_\alpha$. -/)
  (hasProof := false)] OperatorRidgelet.spectralRange

attribute [blueprint "def:spectral-space-embed"
  (statement := /-- The map $U:\mathcal D\to\mathcal K$, $f\mapsto\mathcal G_\mu f$. -/)
  (hasProof := false)] OperatorRidgelet.spectralEmbed

attribute [blueprint "finite-dim:mixture-const"
  (statement := /-- $c_{m,\alpha}=2^{-\alpha}\pi^{-m/2}\Gamma((m-\alpha)/2)$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.mixtureConst

attribute [blueprint "finite-dim:direction-measure"
  (statement := /-- $\nu_\alpha(\mathrm da)=c_{m,\alpha}\|a\|^{\alpha-m}\,\mathrm da$ on
    $\mathbb R^m$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.directionMeasure

attribute [blueprint "finite-dim:frame-const"
  (statement := /-- $k_{m,\alpha}=(2\pi)^mc_{m,\alpha}$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.frameConst

attribute [blueprint "finite-dim:fourier"
  (statement := /-- The Fourier transform $\widehat g(\xi)=\int g(x)e^{-i\langle
    x,\xi\rangle}\,\mathrm dx$ on $\mathbb R^m$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.fourier

attribute [blueprint "finite-dim:density-measure"
  (statement := /-- The pivot measure $p\,\mathrm dx$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.densityMeasure

attribute [blueprint "finite-dim:frame-representative"
  (statement := /-- $t_f(x)=\int e^{i\langle x,\xi\rangle}\widehat g(\xi)\,\nu(\mathrm d\xi)$
    with $g=fp$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.frameRepresentative

attribute [blueprint "finite-dim:frac-laplacian"
  (statement := /-- $(-\Delta)^sg$ as the Fourier multiplier $\|\xi\|^{2s}$. -/)
  (hasProof := false)] OperatorRidgelet.FiniteDim.fracLaplacian

attribute [blueprint "filters:bump"
  (statement := /-- $\eta(u)=\exp(-1/(1-u^2))$ for $|u|<1$ and $0$ otherwise. -/)
  (hasProof := false)] OperatorRidgelet.Filters.bump

attribute [blueprint "filters:band-pass-hat"
  (statement := /-- $\widehat\rho_{\mathrm{bp}}(\omega)=-\eta(2|\omega|-3)$. -/)
  (hasProof := false)] OperatorRidgelet.Filters.bandPassHat

attribute [blueprint "filters:band-pass-fun"
  (statement := /-- The inverse Fourier transform
    $\rho_{\mathrm{bp}}(t)=\frac1{2\pi}\int\widehat\rho_{\mathrm{bp}}(\omega)e^{it\omega}\,\mathrm
    d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.Filters.bandPassFun

attribute [blueprint "filters:band-pass"
  (statement := /-- The band-pass filter $\rho_{\mathrm{bp}}\in\mathcal S(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.Filters.bandPass

attribute [blueprint "filters:mexican-hat-fun"
  (statement := /-- $\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}$. -/)
  (hasProof := false)] OperatorRidgelet.Filters.mexicanHatFun

attribute [blueprint "filters:mexican-hat"
  (statement := /-- The Mexican hat $\rho_{\mathrm{MH}}\in\mathcal S(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.Filters.mexicanHat

/-! ## Infrastructure -/

attribute [blueprint "infra:gaussian-layers-exist"
  (statement := /-- For an injective, positive, self-adjoint, trace-class $P$ there is a family
    of Gaussian layers $\mathcal N(0,2sP)$, $s>0$ (the Gaussian series of
    Appendix A). -/)
  (notReady := true)] OperatorRidgelet.exists_isCenteredGaussianLayers

/-! ## Paper statements -/

attribute [blueprint "lem:homogeneous-mixture-i"
  (statement := /-- If $\dim H=\infty$ and $\alpha>0$, then $\nu_\alpha$ is sigma-finite. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_i

attribute [blueprint "lem:homogeneous-mixture-ii"
  (statement := /-- $\nu_\alpha$ is finite on bounded Borel sets. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_ii

attribute [blueprint "lem:homogeneous-mixture-iii"
  (statement := /-- $\nu_\alpha(H)=\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_iii

attribute [blueprint "lem:homogeneous-mixture-iv"
  (statement := /-- $\nu_\alpha$ has full support. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_iv

attribute [blueprint "lem:homogeneous-mixture-v"
  (statement := /-- $(D_\omega)_\#\nu_\alpha=|\omega|^{-\alpha}\nu_\alpha$ for $\omega\ne0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_v

attribute [blueprint "lem:homogeneous-mixture-vi"
  (statement := /-- $\int_HF(\omega a)\,\nu_\alpha(\mathrm
    da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu_\alpha$ for nonnegative Borel
    $F$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_homogeneous_mixture_vi

attribute [blueprint "def:admissible-filter-every-alpha"
  (statement := /-- A band-pass filter is $\alpha$-admissible for every $\alpha>0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.def_admissible_filter

attribute [blueprint "lem:fourier-slice-i"
  (statement := /-- $R_\rho f$ is bounded on $H\times\mathbb R$. -/)]
  OperatorRidgelet.Paper.lem_fourier_slice_i

attribute [blueprint "lem:fourier-slice-ii"
  (statement := /-- $R_\rho f$ is jointly continuous on $H\times\mathbb R$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_fourier_slice_ii

attribute [blueprint "lem:fourier-slice-iii"
  (statement := /-- $\|R_\rho f(a,\cdot)\|_{L^1(\mathbb
    R)}\le\|f\|_{L^1(\mu)}\|\rho\|_{L^1(\mathbb R)}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_fourier_slice_iii

attribute [blueprint "lem:fourier-slice-iv"
  (statement := /-- $\|R_\rho f(a,\cdot)\|_{L^2(\mathbb
    R)}^2\le\|f\|_{L^2(\mu)}^2\|\rho\|_{L^2(\mathbb R)}^2$ if $f\in L^2(\mu)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_fourier_slice_iv

attribute [blueprint "lem:fourier-slice-v"
  (statement := /-- $\widehat{R_\rho f}(a,\omega)=\widehat\rho(\omega)\,\mathcal G_\mu f(-\omega
    a)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_fourier_slice_v

attribute [blueprint "def:spectral-coefficient-l1"
  (statement := /-- If $G\in L^1(\nu)\cap L^2(\nu)$, then $W_\rho G=\gamma_G$ almost everywhere. -/)
  (notReady := true)] OperatorRidgelet.Paper.def_spectral_coefficient

attribute [blueprint "lem:coefficient-isometry-i"
  (statement := /-- $W_\rho G$ is well defined: exactly one element of $L^2(\lambda)$ has
    partial bias Fourier transform $\widehat\rho(\omega)G(-\omega a)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_coefficient_isometry_i

attribute [blueprint "lem:coefficient-isometry-ii"
  (statement := /-- $W_\rho G$ is independent of the Borel representative of $G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_coefficient_isometry_ii

attribute [blueprint "lem:coefficient-isometry-iii"
  (statement := /-- $\|W_\rho G\|_{L^2(\lambda)}^2=C^{(\alpha)}_\rho\|G\|_{L^2(\nu)}^2$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_coefficient_isometry_iii

attribute [blueprint "lem:coefficient-isometry-iv"
  (statement := /-- If $G\in L^1(\nu)$, then $\omega\mapsto G(-\omega a)$ is integrable on
    compact subsets of $\mathbb R\setminus\{0\}$ for $\nu$-almost every $a$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_coefficient_isometry_iv

attribute [blueprint "lem:spectral-unitary-i"
  (statement := /-- The spectral form is positive definite on $\mathcal D$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_spectral_unitary_i

attribute [blueprint "lem:spectral-unitary-ii"
  (statement := /-- $\mathcal G_\mu$ is an isometry from $(\mathcal
    D,\langle\cdot,\cdot\rangle_{\mathcal E})$ into $\mathcal K$. -/)]
  OperatorRidgelet.Paper.lem_spectral_unitary_ii

attribute [blueprint "lem:spectral-unitary-iii"
  (statement := /-- $\mathcal G_\mu(\mathcal D)$ is dense in $\mathcal K$, so $\mathcal G_\mu$
    extends uniquely to a unitary $U_\alpha:\mathcal E_\alpha\to\mathcal
    K_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_spectral_unitary_iii

attribute [blueprint "lem:gaussian-decay-i"
  (statement := /-- $\int_H\|\xi\|^{2m}e^{-t\langle Q\xi,\xi\rangle}\,\nu_\alpha(\mathrm
    d\xi)<\infty$ for $t>0$, $\alpha>0$, $m\ge0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_gaussian_decay_i

attribute [blueprint "lem:gaussian-decay-ii"
  (statement := /-- If $f\in L^2(\mu_Q)$ and $|\mathcal G_Qf(\xi)|\le C(1+\|\xi\|)^pe^{-t\langle
    Q\xi,\xi\rangle/2}$, then $f\in\mathcal D_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_gaussian_decay_ii

attribute [blueprint "ex:core-elements-i"
  (statement := /-- $\mathcal G_Q1(\xi)=e^{-\langle Q\xi,\xi\rangle/2}$. -/)]
  OperatorRidgelet.Paper.ex_core_elements_i

attribute [blueprint "ex:core-elements-ii"
  (statement := /-- $1\in\mathcal D_\alpha$ for every $\alpha>0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_core_elements_ii

attribute [blueprint "ex:core-elements-iii"
  (statement := /-- $\mathcal E_\alpha\ne\{0\}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_core_elements_iii

attribute [blueprint "thm:B-i-a"
  (statement := /-- For $f\in\mathcal D_\alpha$ and $\alpha$-admissible $\rho$, $R_\rho f\in
    L^2(\lambda_\alpha)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_i_a

attribute [blueprint "thm:B-i-b"
  (statement := /-- $\langle
    R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle
    f,g\rangle_{\mathcal E_\alpha}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_i_b

attribute [blueprint "thm:B-ii-a"
  (statement := /-- An $\alpha$-admissible $\rho$ determines a unique bounded extension
    $R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_ii_a

attribute [blueprint "thm:B-ii-b"
  (statement := /-- $\|R_\rho f\|^2=C^{(\alpha)}_\rho\|f\|_{\mathcal E_\alpha}^2$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_ii_b

attribute [blueprint "thm:B-ii-c"
  (statement := /-- The range of $R_\rho$ is closed. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_ii_c

attribute [blueprint "thm:B-ii-d"
  (statement := /-- $R_\rho=W_\rho U_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_ii_d

attribute [blueprint "thm:B-iii"
  (statement := /-- If $\rho$ is $\alpha$-admissible and $f\in L^2(\mu_Q)$, then $R_\rho f=0$
    $\lambda_\alpha$-a.e. implies $f=0$ $\mu_Q$-a.e. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_B_iii

attribute [blueprint "lem:mixture-integration-i"
  (statement := /-- $s\mapsto\mathcal N(0,2sP)(E)$ is Borel measurable on $(0,\infty)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_integration_i

attribute [blueprint "lem:mixture-integration-ii"
  (statement := /-- $\nu_\alpha(E)=\int_0^\infty\mathcal N(0,2sP)(E)\,s^{\alpha/2-1}\,\mathrm
    ds$ defines a countably additive Borel measure. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_integration_ii

attribute [blueprint "lem:mixture-integration-iii"
  (statement := /-- $\int_HF\,\mathrm d\nu_\alpha=\int_0^\infty\int_HF\,\mathrm d\mathcal
    N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds$ for nonnegative Borel $F$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_integration_iii

attribute [blueprint "lem:mixture-integration-iv"
  (statement := /-- The integration formula holds for complex $F$ with $\int_H|F|\,\mathrm
    d\nu_\alpha<\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_integration_iv

attribute [blueprint "lem:mixture-character-i"
  (statement := /-- $q=\langle Pz,z\rangle>0$ for $z\ne0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_character_i

attribute [blueprint "lem:mixture-character-ii"
  (statement := /-- $\lim_{\varepsilon\downarrow0,M\uparrow\infty}\int_He^{i\langle
    z,\xi\rangle}\,\nu_\alpha^{\varepsilon,M}(\mathrm
    d\xi)=\Gamma(\alpha/2)q^{-\alpha/2}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_character_ii

attribute [blueprint "lem:mixture-character-iii"
  (statement := /-- $\int_0^\infty e^{-sq}s^{\alpha/2-1}\,\mathrm
    ds=\Gamma(\alpha/2)q^{-\alpha/2}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_character_iii

attribute [blueprint "lem:mixture-character-iv"
  (statement := /-- $\int_H|e^{i\langle z,\xi\rangle}|\,\nu_\alpha(\mathrm d\xi)=\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_mixture_character_iv

attribute [blueprint "cor:finite-backprojection-i"
  (statement := /-- If $f\in L^2(p\,\mathrm dx)$ with $g=fp\in\mathcal S(\mathbb R^m)$, then
    $f\in\mathcal D_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_i

attribute [blueprint "cor:finite-backprojection-ii"
  (statement := /-- $t_f=\int e^{i\langle x,\xi\rangle}\widehat g(\xi)\,\nu_\alpha(\mathrm
    d\xi)=k_{m,\alpha}(-\Delta)^{-(m-\alpha)/2}g$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_ii

attribute [blueprint "cor:finite-backprojection-iii"
  (statement := /-- For band-pass $\rho$, $S_\rho R_\rho f$ is represented against $p\,\mathrm
    dx$ by $C^{(\alpha)}_\rho t_f$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_iii

attribute [blueprint "cor:finite-backprojection-iv"
  (statement := /-- Distributionally,
    $f=\frac{p^{-1}}{k_{m,\alpha}C^{(\alpha)}_\rho}(-\Delta)^{(m-\alpha)/2}S_\rho
    R_\rho f$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_iv

attribute [blueprint "cor:finite-backprojection-v"
  (statement := /-- With Lebesgue direction measure and $\alpha=m$, $t_f=(2\pi)^mg$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_v

attribute [blueprint "cor:finite-backprojection-vi"
  (statement := /-- With Lebesgue direction measure and $\alpha=m$,
    $f=(2\pi)^{-m}(C^{(m)}_\rho)^{-1}p^{-1}S_\rho R_\rho f$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_finite_backprojection_vi

attribute [blueprint "prop:dilation-obstruction-i-a"
  (statement := /-- The sets $E_t$ are Borel. -/)
  (notReady := true)] OperatorRidgelet.Paper.prop_dilation_obstruction_i_a

attribute [blueprint "prop:dilation-obstruction-i-b"
  (statement := /-- The sets $E_t$ are pairwise disjoint. -/)]
  OperatorRidgelet.Paper.prop_dilation_obstruction_i_b

attribute [blueprint "prop:dilation-obstruction-i-c"
  (statement := /-- $\mathcal N(0,tW)(E_t)=1$ for $t>0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.prop_dilation_obstruction_i_c

attribute [blueprint "prop:dilation-obstruction-i-d"
  (statement := /-- A sigma-finite measure dominates $\mathcal N(0,tW)$ for at most countably
    many $t$. -/)
  (notReady := true)] OperatorRidgelet.Paper.prop_dilation_obstruction_i_d

attribute [blueprint "prop:dilation-obstruction-ii"
  (statement := /-- No finite complex Borel measure on $H\times\mathbb R$ has bias slices
    $r(\omega)(D_{1/\omega})_\#\mathcal N(0,W)$ for almost every $\omega\ne0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.prop_dilation_obstruction_ii

attribute [blueprint "thm:general-weights-plancherel-memLp"
  (statement := /-- For the abstract pair $(\mu,\nu)$, $R_\rho f\in L^2(\lambda)$ for
    $f\in\mathcal D_{\mu,\nu}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_plancherel_memLp

attribute [blueprint "thm:general-weights-plancherel"
  (statement := /-- For the abstract pair, $\langle
    R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle
    f,g\rangle_{\mathcal E_{\mu,\nu}}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_plancherel

attribute [blueprint "thm:general-weights-extension"
  (statement := /-- For the abstract pair, $R_\rho$ has a unique bounded extension $\mathcal
    E_{\mu,\nu}\to L^2(\lambda)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_extension

attribute [blueprint "thm:general-weights-extension-norm"
  (statement := /-- For the abstract pair, $\|R_\rho f\|^2=C^{(\alpha)}_\rho\|f\|_{\mathcal
    E_{\mu,\nu}}^2$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_extension_norm

attribute [blueprint "thm:general-weights-extension-closed-range"
  (statement := /-- For the abstract pair, the range of $R_\rho$ is closed. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_extension_closed_range

attribute [blueprint "thm:general-weights-extension-coefficient"
  (statement := /-- For the abstract pair, $R_\rho=W_\rho U$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_extension_coefficient

attribute [blueprint "thm:general-weights-injective"
  (statement := /-- For the abstract pair, $R_\rho f=0$ $\lambda$-a.e. implies $f=0$ $\mu$-a.e. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_injective

attribute [blueprint "thm:general-weights-one-mem-iff"
  (statement := /-- $1\in\mathcal D_{\mu,\nu}$ if and only if
    $\int_H|\widehat\mu(\xi)|^2\,\nu(\mathrm d\xi)<\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_weights_one_mem_iff

attribute [blueprint "ex:bandlimited-filter-i"
  (statement := /-- $\widehat\rho_{\mathrm{bp}}$ is smooth. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_i

attribute [blueprint "ex:bandlimited-filter-ii"
  (statement := /-- $\widehat\rho_{\mathrm{bp}}$ is nonpositive. -/)]
  OperatorRidgelet.Paper.ex_bandlimited_filter_ii

attribute [blueprint "ex:bandlimited-filter-iii"
  (statement := /-- $\widehat\rho_{\mathrm{bp}}$ is nonzero. -/)]
  OperatorRidgelet.Paper.ex_bandlimited_filter_iii

attribute [blueprint "ex:bandlimited-filter-iv"
  (statement := /-- $\widehat\rho_{\mathrm{bp}}$ is supported in $\{1\le|\omega|\le2\}$. -/)]
  OperatorRidgelet.Paper.ex_bandlimited_filter_iv

attribute [blueprint "ex:bandlimited-filter-v"
  (statement := /-- $\rho_{\mathrm{bp}}$ is a real Schwartz function, the inverse Fourier
    transform of $\widehat\rho_{\mathrm{bp}}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_v

attribute [blueprint "ex:bandlimited-filter-vi"
  (statement := /-- $\rho_{\mathrm{bp}}$ is even. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_vi

attribute [blueprint "ex:bandlimited-filter-vii"
  (statement := /-- The Fourier transform of $\rho_{\mathrm{bp}}$ is the prescribed
    $\widehat\rho_{\mathrm{bp}}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_vii

attribute [blueprint "ex:bandlimited-filter-viii"
  (statement := /-- $\rho_{\mathrm{bp}}$ satisfies the band-pass condition. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_viii

attribute [blueprint "ex:bandlimited-filter-ix"
  (statement := /-- $\rho_{\mathrm{bp}}$ is $\alpha$-admissible for every $\alpha>0$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_ix

attribute [blueprint "ex:bandlimited-filter-x"
  (statement := /-- Multiplying by $(C^{(\alpha)}_{\rho_{\mathrm{bp}}})^{-1/2}$ normalizes the
    admissibility constant to one. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_bandlimited_filter_x

attribute [blueprint "ex:mexican-hat-i"
  (statement := /-- $\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}$ is a Schwartz function. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_i

attribute [blueprint "ex:mexican-hat-ii"
  (statement := /-- $\widehat\rho_{\mathrm{MH}}(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_ii

attribute [blueprint "ex:mexican-hat-iii"
  (statement := /-- $\rho_{\mathrm{MH}}$ is $\alpha$-admissible exactly for $0<\alpha<5$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_iii

attribute [blueprint "ex:mexican-hat-iv"
  (statement := /-- $C^{(\alpha)}_{\rho_{\mathrm{MH}}}=\Gamma((5-\alpha)/2)$ for $0<\alpha<5$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_iv

attribute [blueprint "ex:mexican-hat-v"
  (statement := /-- $C^{(1)}_{\rho_{\mathrm{MH}}}=1$. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_v

attribute [blueprint "ex:mexican-hat-vi"
  (statement := /-- $\rho_{\mathrm{MH}}$ is not band pass. -/)
  (notReady := true)] OperatorRidgelet.Paper.ex_mexican_hat_vi
