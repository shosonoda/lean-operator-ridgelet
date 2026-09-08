import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Transform
import OperatorRidgelet.Transform.Infra

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Gaussian-weighted ridgelet transform" =>
%%%
file := "gaussian-weighted-transform"
%%%

This chapter lists the definitions and the statements of Section 3 of the manuscript (the
Gaussian-weighted ridgelet transform, the Fourier-slice identity, the coefficient operator, the
Hilbert space $`\mathcal E_\alpha`, and the Plancherel theorem) together with Appendix A (the
Gaussian mixture), Appendix G (the finite-dimensional case and the dilation obstruction),
Appendix H (abstract weights), and Appendix I (explicit filters). Node labels are the manuscript
labels with the part appended.

The core theory is stated for an abstract pair $`(\mu,\nu)`: $`\mu` a Borel probability measure
on the input space and $`\nu` a $`\sigma`-finite measure with full support that is homogeneous
of degree $`\alpha`. The Gaussian case is the instance $`\mu=\mathcal N(0,Q)`,
$`\nu=\nu_\alpha`. The Hilbert space $`\mathcal E_\alpha` is represented by the closed subspace
$`\mathcal K_\alpha=\overline{\mathcal G_Q(\mathcal D_\alpha)}\subseteq L^2(\nu_\alpha)`, to
which it is unitarily equivalent by Lemma `lem:spectral-unitary`.

# Gaussian measures and the homogeneous mixture

:::definition "transform:centered-gaussian" (lean := "OperatorRidgelet.IsCenteredGaussian")
$`\mu=\mathcal N(0,Q)` is the Borel probability measure with characteristic functional
$`\int_He^{i\langle x,\xi\rangle}\mu(\mathrm dx)=e^{-\langle Q\xi,\xi\rangle/2}`.
:::

:::definition "transform:trace-class-covariance" (lean := "OperatorRidgelet.IsTraceClassCovariance")
An injective, positive, self-adjoint, trace-class operator; the trace is taken along a Hilbert
basis.
:::

:::definition "transform:gaussian-layers" (lean := "OperatorRidgelet.IsCenteredGaussianLayers") (uses := "transform:centered-gaussian")
A family $`N_s=\mathcal N(0,2sP)`, $`s>0`, of Gaussian layers.
:::

:::theorem "infra:gaussian-layers-exist" (lean := "OperatorRidgelet.exists_isCenteredGaussianLayers") (uses := "transform:gaussian-layers, transform:trace-class-covariance")
For an injective, positive, self-adjoint, trace-class $`P` the Gaussian layers exist (the
Gaussian series of Appendix A). Mathlib has no constructor of a Gaussian measure with a
prescribed trace-class covariance in infinite dimension; this is the missing infrastructure.
:::

:::definition "transform:gaussian-mixture" (lean := "OperatorRidgelet.gaussianMixture") (uses := "transform:gaussian-layers")
The homogeneous Gaussian mixture
$`\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`, as the Giry-monad
bind of the weight against the layers.
:::

:::definition "transform:homogeneous" (lean := "OperatorRidgelet.IsHomogeneous")
A measure is homogeneous of degree $`\alpha` when $`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for
every $`\omega\ne0`.
:::

:::theorem "lem:mixture-integration-i" (lean := "OperatorRidgelet.Paper.lem_mixture_integration_i") (uses := "transform:gaussian-layers")
For every Borel set $`E`, the map $`s\mapsto\mathcal N(0,2sP)(E)` is Borel measurable.
:::

:::theorem "lem:mixture-integration-ii" (lean := "OperatorRidgelet.Paper.lem_mixture_integration_ii") (uses := "transform:gaussian-mixture, lem:mixture-integration-i")
$`\nu_\alpha(E)=\int_0^\infty\mathcal N(0,2sP)(E)\,s^{\alpha/2-1}\,\mathrm ds` on Borel sets.
:::

:::theorem "lem:mixture-integration-iii" (lean := "OperatorRidgelet.Paper.lem_mixture_integration_iii") (uses := "lem:mixture-integration-ii")
$`\int_HF\,\mathrm d\nu_\alpha=\int_0^\infty\int_HF\,\mathrm d\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`
for nonnegative Borel $`F`.
:::

:::theorem "lem:mixture-integration-iv" (lean := "OperatorRidgelet.Paper.lem_mixture_integration_iv") (uses := "lem:mixture-integration-iii")
The integration formula holds for complex $`F` with $`\int_H|F|\,\mathrm d\nu_\alpha<\infty`.
:::

:::theorem "lem:homogeneous-mixture-i" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_i") (uses := "transform:gaussian-mixture, lem:mixture-integration-ii")
If $`\dim H=\infty` and $`\alpha>0`, then $`\nu_\alpha` is $`\sigma`-finite.
:::

:::theorem "lem:homogeneous-mixture-ii" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_ii") (uses := "transform:gaussian-mixture, lem:mixture-integration-ii")
$`\nu_\alpha` is finite on bounded Borel sets.
:::

:::theorem "lem:homogeneous-mixture-iii" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_iii") (uses := "transform:gaussian-mixture, lem:mixture-integration-ii")
$`\nu_\alpha(H)=\infty`.
:::

:::theorem "lem:homogeneous-mixture-iv" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_iv") (uses := "transform:gaussian-mixture, lem:mixture-integration-ii")
$`\nu_\alpha` has full support.
:::

:::theorem "lem:homogeneous-mixture-v" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_v") (uses := "transform:gaussian-mixture, transform:homogeneous, lem:mixture-integration-ii")
$`(D_\omega)_\#\nu_\alpha=|\omega|^{-\alpha}\nu_\alpha` for $`\omega\ne0`.
:::

:::theorem "lem:homogeneous-mixture-vi" (lean := "OperatorRidgelet.Paper.lem_homogeneous_mixture_vi") (uses := "lem:homogeneous-mixture-v, lem:mixture-integration-iii")
$`\int_HF(\omega a)\,\nu_\alpha(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu_\alpha` for
nonnegative Borel $`F`.
:::

:::theorem "lem:mixture-character-i" (lean := "OperatorRidgelet.Paper.lem_mixture_character_i") (uses := "transform:trace-class-covariance")
$`q=\langle Pz,z\rangle>0` for $`z\ne0`.
:::

:::theorem "lem:mixture-character-ii" (lean := "OperatorRidgelet.Paper.lem_mixture_character_ii") (uses := "transform:gaussian-mixture, lem:mixture-character-i, lem:mixture-character-iii")
The characteristic functionals of the truncated mixtures converge to
$`\Gamma(\alpha/2)q^{-\alpha/2}` as $`\varepsilon\downarrow0` and $`M\uparrow\infty`.
:::

:::theorem "lem:mixture-character-iii" (lean := "OperatorRidgelet.Paper.lem_mixture_character_iii") (uses := "lem:mixture-character-i")
$`\int_0^\infty e^{-sq}s^{\alpha/2-1}\,\mathrm ds=\Gamma(\alpha/2)q^{-\alpha/2}`.
:::

:::theorem "lem:mixture-character-iv" (lean := "OperatorRidgelet.Paper.lem_mixture_character_iv") (uses := "lem:homogeneous-mixture-iii")
$`\int_H|e^{i\langle z,\xi\rangle}|\,\nu_\alpha(\mathrm d\xi)=\infty`.
:::

# Admissible filters and the transform

:::definition "transform:filter-fourier" (lean := "OperatorRidgelet.filterFourier")
$`\widehat\rho(\omega)=\int_{\mathbb R}\rho(t)e^{-it\omega}\,\mathrm dt`.
:::

:::definition "def:admissible-filter-const" (lean := "OperatorRidgelet.admissibilityConst") (uses := "transform:filter-fourier")
$`C^{(\alpha)}_\rho=\frac1{2\pi}\int_{\mathbb R}|\widehat\rho(\omega)|^2|\omega|^{-\alpha}\,\mathrm d\omega`.
:::

:::definition "def:admissible-filter-cross" (lean := "OperatorRidgelet.crossAdmissibilityConst") (uses := "transform:filter-fourier")
$`C^{(\alpha)}_{\rho_1,\rho_2}=\frac1{2\pi}\int_{\mathbb R}\widehat\rho_1(\omega)\overline{\widehat\rho_2(\omega)}|\omega|^{-\alpha}\,\mathrm d\omega`.
:::

:::definition "def:admissible-filter" (lean := "OperatorRidgelet.IsAdmissible") (uses := "def:admissible-filter-const")
A real $`\rho\in\mathcal S(\mathbb R)` is $`\alpha`-admissible if $`0<C^{(\alpha)}_\rho<\infty`.
:::

:::definition "def:admissible-filter-bandpass" (lean := "OperatorRidgelet.IsBandPass") (uses := "transform:filter-fourier")
$`\rho` is a band-pass filter if moreover $`\widehat\rho\in C_c^\infty(\mathbb R\setminus\{0\})`.
:::

:::theorem "def:admissible-filter-every-alpha" (lean := "OperatorRidgelet.Paper.def_admissible_filter") (uses := "def:admissible-filter, def:admissible-filter-bandpass")
A band-pass filter is $`\alpha`-admissible for every $`\alpha>0`.
:::

:::definition "def:ridgelet-analysis" (lean := "OperatorRidgelet.ridgelet")
$`R_\rho f(a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu(\mathrm dx)`.
:::

:::definition "def:ridgelet-analysis-parameter-measure" (lean := "OperatorRidgelet.parameterMeasure")
$`\lambda=\nu\otimes\mathrm dc`.
:::

:::definition "transform:gauss-fourier" (lean := "OperatorRidgelet.gaussFourier")
$`\mathcal G_\mu f(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu(\mathrm dx)`.
:::

:::definition "transform:bias-fourier" (lean := "OperatorRidgelet.biasFourier")
$`\widehat\gamma(a,\omega)=\int_{\mathbb R}\gamma(a,c)e^{-i\omega c}\,\mathrm dc`.
:::

:::theorem "lem:fourier-slice-i" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_i") (uses := "def:ridgelet-analysis")
$`R_\rho f` is bounded.
:::

:::theorem "lem:fourier-slice-ii" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_ii") (uses := "def:ridgelet-analysis")
$`R_\rho f` is jointly continuous.
:::

:::theorem "lem:fourier-slice-iii" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_iii") (uses := "def:ridgelet-analysis")
$`\|R_\rho f(a,\cdot)\|_{L^1}\le\|f\|_{L^1(\mu)}\|\rho\|_{L^1}`.
:::

:::theorem "lem:fourier-slice-iv" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_iv") (uses := "def:ridgelet-analysis")
$`\|R_\rho f(a,\cdot)\|_{L^2}^2\le\|f\|_{L^2(\mu)}^2\|\rho\|_{L^2}^2` if $`f\in L^2(\mu)`.
:::

:::theorem "lem:fourier-slice-v" (lean := "OperatorRidgelet.Paper.lem_fourier_slice_v") (uses := "def:ridgelet-analysis, transform:gauss-fourier, transform:bias-fourier, transform:filter-fourier, lem:fourier-slice-iii")
$`\widehat{R_\rho f}(a,\omega)=\widehat\rho(\omega)\,\mathcal G_\mu f(-\omega a)`.
:::

# The coefficient operator

:::definition "def:spectral-coefficient-bias-fourier" (lean := "OperatorRidgelet.HasBiasFourier")
$`\gamma` has partial Fourier transform $`\Phi` in the bias, in the sense of Parseval's identity
against Schwartz test functions for $`\nu`-almost every direction.
:::

:::definition "def:spectral-coefficient" (lean := "OperatorRidgelet.spectralCoefficient") (uses := "def:spectral-coefficient-bias-fourier, def:ridgelet-analysis-parameter-measure")
$`W_\rho G\in L^2(\lambda)` is the element whose partial Fourier transform in the bias is
$`\widehat\rho(\omega)G(-\omega a)`.
:::

:::definition "def:spectral-coefficient-formula" (lean := "OperatorRidgelet.coefficientFormula") (uses := "transform:filter-fourier")
$`\gamma_G(a,c)=\frac1{2\pi}\int_{\mathbb R}\widehat\rho(\omega)G(-\omega a)e^{i\omega c}\,\mathrm d\omega`.
:::

:::theorem "def:spectral-coefficient-l1" (lean := "OperatorRidgelet.Paper.def_spectral_coefficient") (uses := "def:spectral-coefficient, def:spectral-coefficient-formula, lem:coefficient-isometry-iv")
If $`G\in L^1(\nu)\cap L^2(\nu)`, then $`W_\rho G=\gamma_G` almost everywhere.
:::

:::theorem "lem:coefficient-isometry-i" (lean := "OperatorRidgelet.Paper.lem_coefficient_isometry_i") (uses := "def:spectral-coefficient, transform:homogeneous")
$`W_\rho G` is well defined.
:::

:::theorem "lem:coefficient-isometry-ii" (lean := "OperatorRidgelet.Paper.lem_coefficient_isometry_ii") (uses := "lem:coefficient-isometry-i")
$`W_\rho G` is independent of the Borel representative of $`G`.
:::

:::theorem "lem:coefficient-isometry-iii" (lean := "OperatorRidgelet.Paper.lem_coefficient_isometry_iii") (uses := "lem:coefficient-isometry-i, def:admissible-filter-const")
$`\|W_\rho G\|_{L^2(\lambda)}^2=C^{(\alpha)}_\rho\|G\|_{L^2(\nu)}^2`.
:::

:::theorem "lem:coefficient-isometry-iv" (lean := "OperatorRidgelet.Paper.lem_coefficient_isometry_iv") (uses := "transform:homogeneous")
If $`G\in L^1(\nu)`, then $`\omega\mapsto G(-\omega a)` is locally integrable on
$`\mathbb R\setminus\{0\}` for $`\nu`-almost every $`a`.
:::

# The Hilbert space

:::definition "def:spectral-space" (lean := "OperatorRidgelet.spectralCore") (uses := "transform:gauss-fourier")
$`\mathcal D=\{f\in L^2(\mu):\mathcal G_\mu f\in L^2(\nu)\}`.
:::

:::definition "def:spectral-space-inner" (lean := "OperatorRidgelet.spectralInner") (uses := "transform:gauss-fourier")
$`\langle f,g\rangle_{\mathcal E}=\int_H\mathcal G_\mu f\,\overline{\mathcal G_\mu g}\,\mathrm d\nu`.
:::

:::definition "def:spectral-space-range" (lean := "OperatorRidgelet.spectralRange") (uses := "def:spectral-space")
$`\mathcal K=\overline{\mathcal G_\mu(\mathcal D)}^{L^2(\nu)}`, which represents
$`\mathcal E_\alpha`.
:::

:::definition "def:spectral-space-embed" (lean := "OperatorRidgelet.spectralEmbed") (uses := "def:spectral-space-range")
$`U:\mathcal D\to\mathcal K`, $`f\mapsto\mathcal G_\mu f`.
:::

:::theorem "lem:spectral-unitary-i" (lean := "OperatorRidgelet.Paper.lem_spectral_unitary_i") (uses := "def:spectral-space-inner")
The spectral form is positive definite on $`\mathcal D`.
:::

:::theorem "lem:spectral-unitary-ii" (lean := "OperatorRidgelet.Paper.lem_spectral_unitary_ii") (uses := "def:spectral-space-embed, def:spectral-space-inner")
$`\mathcal G_\mu` is an isometry from $`(\mathcal D,\langle\cdot,\cdot\rangle_{\mathcal E})`
into $`\mathcal K`.
:::

:::theorem "lem:spectral-unitary-iii" (lean := "OperatorRidgelet.Paper.lem_spectral_unitary_iii") (uses := "def:spectral-space-embed")
$`\mathcal G_\mu(\mathcal D)` is dense in $`\mathcal K`, so the isometry extends uniquely to a
unitary $`U_\alpha:\mathcal E_\alpha\to\mathcal K_\alpha`.
:::

:::theorem "lem:gaussian-decay-i" (lean := "OperatorRidgelet.Paper.lem_gaussian_decay_i") (uses := "lem:mixture-integration-iii")
$`\int_H\|\xi\|^{2m}e^{-t\langle Q\xi,\xi\rangle}\,\nu_\alpha(\mathrm d\xi)<\infty`.
:::

:::theorem "lem:gaussian-decay-ii" (lean := "OperatorRidgelet.Paper.lem_gaussian_decay_ii") (uses := "lem:gaussian-decay-i, def:spectral-space")
Gaussian decay of $`\mathcal G_Qf` with a polynomial weight implies $`f\in\mathcal D_\alpha`.
:::

:::theorem "ex:core-elements-i" (lean := "OperatorRidgelet.Paper.ex_core_elements_i") (uses := "transform:gauss-fourier, transform:centered-gaussian")
$`\mathcal G_Q1(\xi)=e^{-\langle Q\xi,\xi\rangle/2}`.
:::

:::theorem "ex:core-elements-ii" (lean := "OperatorRidgelet.Paper.ex_core_elements_ii") (uses := "ex:core-elements-i, lem:gaussian-decay-ii")
$`1\in\mathcal D_\alpha` for every $`\alpha>0`.
:::

:::theorem "ex:core-elements-iii" (lean := "OperatorRidgelet.Paper.ex_core_elements_iii") (uses := "ex:core-elements-ii")
$`\mathcal E_\alpha\ne\{0\}`.
:::

# Plancherel identity, closed range, and injectivity

:::theorem "thm:general-weights-plancherel-memLp" (lean := "OperatorRidgelet.Paper.thm_general_weights_plancherel_memLp") (uses := "lem:fourier-slice-v, lem:homogeneous-mixture-vi, def:admissible-filter")
For the abstract pair $`(\mu,\nu)`, $`R_\rho f\in L^2(\lambda)` for $`f\in\mathcal D_{\mu,\nu}`.
:::

:::theorem "thm:general-weights-plancherel" (lean := "OperatorRidgelet.Paper.thm_general_weights_plancherel") (uses := "thm:general-weights-plancherel-memLp, def:admissible-filter-cross, def:spectral-space-inner")
$`\langle R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle f,g\rangle_{\mathcal E_{\mu,\nu}}`.
:::

:::theorem "thm:general-weights-extension" (lean := "OperatorRidgelet.Paper.thm_general_weights_extension") (uses := "thm:general-weights-plancherel, lem:spectral-unitary-iii")
$`R_\rho` has a unique bounded extension $`\mathcal E_{\mu,\nu}\to L^2(\lambda)`.
:::

:::theorem "thm:general-weights-extension-norm" (lean := "OperatorRidgelet.Paper.thm_general_weights_extension_norm") (uses := "thm:general-weights-extension")
$`\|R_\rho f\|^2=C^{(\alpha)}_\rho\|f\|^2_{\mathcal E_{\mu,\nu}}`.
:::

:::theorem "thm:general-weights-extension-closed-range" (lean := "OperatorRidgelet.Paper.thm_general_weights_extension_closed_range") (uses := "thm:general-weights-extension-norm")
The range of the extension is closed.
:::

:::theorem "thm:general-weights-extension-coefficient" (lean := "OperatorRidgelet.Paper.thm_general_weights_extension_coefficient") (uses := "thm:general-weights-extension, lem:coefficient-isometry-iii, lem:fourier-slice-v")
$`R_\rho=W_\rho U`.
:::

:::theorem "thm:general-weights-injective" (lean := "OperatorRidgelet.Paper.thm_general_weights_injective") (uses := "lem:fourier-slice-v, lem:spectral-unitary-i")
$`R_\rho f=0` $`\lambda`-a.e. implies $`f=0` $`\mu`-a.e.
:::

:::theorem "thm:general-weights-one-mem-iff" (lean := "OperatorRidgelet.Paper.thm_general_weights_one_mem_iff") (uses := "def:spectral-space, transform:gauss-fourier")
$`1\in\mathcal D_{\mu,\nu}` if and only if $`\int_H|\widehat\mu|^2\,\mathrm d\nu<\infty`.
:::

:::theorem "thm:B-i-a" (lean := "OperatorRidgelet.Paper.thm_B_i_a") (uses := "thm:general-weights-plancherel-memLp, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
For $`f\in\mathcal D_\alpha` and $`\alpha`-admissible $`\rho`, $`R_\rho f\in L^2(\lambda_\alpha)`.
:::

:::theorem "thm:B-i-b" (lean := "OperatorRidgelet.Paper.thm_B_i_b") (uses := "thm:general-weights-plancherel, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
$`\langle R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle f,g\rangle_{\mathcal E_\alpha}`.
:::

:::theorem "thm:B-ii-a" (lean := "OperatorRidgelet.Paper.thm_B_ii_a") (uses := "thm:general-weights-extension, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
An $`\alpha`-admissible $`\rho` determines a unique bounded extension
$`R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)`.
:::

:::theorem "thm:B-ii-b" (lean := "OperatorRidgelet.Paper.thm_B_ii_b") (uses := "thm:general-weights-extension-norm, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
$`\|R_\rho f\|^2=C^{(\alpha)}_\rho\|f\|_{\mathcal E_\alpha}^2`.
:::

:::theorem "thm:B-ii-c" (lean := "OperatorRidgelet.Paper.thm_B_ii_c") (uses := "thm:general-weights-extension-closed-range, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
The range of $`R_\rho` is closed.
:::

:::theorem "thm:B-ii-d" (lean := "OperatorRidgelet.Paper.thm_B_ii_d") (uses := "thm:general-weights-extension-coefficient, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
$`R_\rho=W_\rho U_\alpha`.
:::

:::theorem "thm:B-iii" (lean := "OperatorRidgelet.Paper.thm_B_iii") (uses := "thm:general-weights-injective, lem:homogeneous-mixture-i, lem:homogeneous-mixture-iv, lem:homogeneous-mixture-v")
If $`\rho` is $`\alpha`-admissible and $`f\in L^2(\mu_Q)`, then $`R_\rho f=0`
$`\lambda_\alpha`-a.e. implies $`f=0` $`\mu_Q`-a.e.
:::

# The finite-dimensional case and the dilation obstruction

:::definition "finite-dim:direction-measure" (lean := "OperatorRidgelet.FiniteDim.directionMeasure")
$`\nu_\alpha(\mathrm da)=c_{m,\alpha}\|a\|^{\alpha-m}\,\mathrm da` on $`\mathbb R^m`.
:::

:::definition "finite-dim:frame-representative" (lean := "OperatorRidgelet.FiniteDim.frameRepresentative")
$`t_f(x)=\int e^{i\langle x,\xi\rangle}\widehat g(\xi)\,\nu(\mathrm d\xi)` with $`g=fp`.
:::

:::definition "finite-dim:frac-laplacian" (lean := "OperatorRidgelet.FiniteDim.fracLaplacian")
$`(-\Delta)^s g` as the Fourier multiplier $`\|\xi\|^{2s}`.
:::

:::theorem "cor:finite-backprojection-i" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_i") (uses := "finite-dim:direction-measure, def:spectral-space")
If $`f\in L^2(p\,\mathrm dx)` with $`g=fp\in\mathcal S(\mathbb R^m)`, then $`f\in\mathcal D_\alpha`.
:::

:::theorem "cor:finite-backprojection-ii" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_ii") (uses := "finite-dim:frame-representative, finite-dim:frac-laplacian")
$`t_f=k_{m,\alpha}(-\Delta)^{-(m-\alpha)/2}g`.
:::

:::theorem "cor:finite-backprojection-iii" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_iii") (uses := "cor:finite-backprojection-i, cor:finite-backprojection-ii, thm:general-weights-plancherel")
For band-pass $`\rho`, $`S_\rho R_\rho f` is represented against $`p\,\mathrm dx` by
$`C^{(\alpha)}_\rho t_f`.
:::

:::theorem "cor:finite-backprojection-iv" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_iv") (uses := "cor:finite-backprojection-ii, cor:finite-backprojection-iii")
Distributionally, $`f=\frac{p^{-1}}{k_{m,\alpha}C^{(\alpha)}_\rho}(-\Delta)^{(m-\alpha)/2}S_\rho R_\rho f`.
:::

:::theorem "cor:finite-backprojection-v" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_v") (uses := "finite-dim:frame-representative")
With Lebesgue direction measure and $`\alpha=m`, $`t_f=(2\pi)^mg`.
:::

:::theorem "cor:finite-backprojection-vi" (lean := "OperatorRidgelet.Paper.cor_finite_backprojection_vi") (uses := "cor:finite-backprojection-v, thm:general-weights-plancherel")
With Lebesgue direction measure and $`\alpha=m`,
$`f=(2\pi)^{-m}(C^{(m)}_\rho)^{-1}p^{-1}S_\rho R_\rho f`.
:::

:::definition "transform:strong-law-set" (lean := "OperatorRidgelet.strongLawSet")
$`E_t=\{x:\lim_n\frac1n\sum_{j\le n}\langle x,e_j\rangle^2/w_j=t\}`.
:::

:::theorem "prop:dilation-obstruction-i-a" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_i_a") (uses := "transform:strong-law-set")
The sets $`E_t` are Borel.
:::

:::theorem "prop:dilation-obstruction-i-b" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_i_b") (uses := "transform:strong-law-set")
The sets $`E_t` are pairwise disjoint.
:::

:::theorem "prop:dilation-obstruction-i-c" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_i_c") (uses := "transform:strong-law-set, transform:centered-gaussian")
$`\mathcal N(0,tW)(E_t)=1` for $`t>0`.
:::

:::theorem "prop:dilation-obstruction-i-d" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_i_d") (uses := "prop:dilation-obstruction-i-b, prop:dilation-obstruction-i-c")
A $`\sigma`-finite measure dominates $`\mathcal N(0,tW)` for at most countably many $`t`.
:::

:::theorem "prop:dilation-obstruction-ii" (lean := "OperatorRidgelet.Paper.prop_dilation_obstruction_ii") (uses := "prop:dilation-obstruction-i-d")
No finite complex Borel measure on $`H\times\mathbb R` has bias slices
$`r(\omega)(D_{1/\omega})_\#\mathcal N(0,W)` for almost every $`\omega\ne0`.
:::

# Explicit admissible filters

:::definition "filters:band-pass" (lean := "OperatorRidgelet.Filters.bandPass")
The band-pass filter $`\rho_{\mathrm{bp}}` with $`\widehat\rho_{\mathrm{bp}}(\omega)=-\eta(2|\omega|-3)`.
:::

:::definition "filters:mexican-hat" (lean := "OperatorRidgelet.Filters.mexicanHat")
The Mexican hat $`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}`.
:::

:::theorem "ex:bandlimited-filter-i" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_i") (uses := "filters:band-pass")
$`\widehat\rho_{\mathrm{bp}}` is smooth.
:::

:::theorem "ex:bandlimited-filter-ii" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_ii") (uses := "filters:band-pass")
$`\widehat\rho_{\mathrm{bp}}` is nonpositive.
:::

:::theorem "ex:bandlimited-filter-iii" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_iii") (uses := "filters:band-pass")
$`\widehat\rho_{\mathrm{bp}}` is nonzero.
:::

:::theorem "ex:bandlimited-filter-iv" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_iv") (uses := "filters:band-pass")
$`\widehat\rho_{\mathrm{bp}}` is supported in $`\{1\le|\omega|\le2\}`.
:::

:::theorem "ex:bandlimited-filter-v" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_v") (uses := "filters:band-pass, ex:bandlimited-filter-i, ex:bandlimited-filter-iv")
$`\rho_{\mathrm{bp}}` is a real Schwartz function.
:::

:::theorem "ex:bandlimited-filter-vi" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_vi") (uses := "ex:bandlimited-filter-v")
$`\rho_{\mathrm{bp}}` is even.
:::

:::theorem "ex:bandlimited-filter-vii" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_vii") (uses := "ex:bandlimited-filter-v, transform:filter-fourier")
The Fourier transform of $`\rho_{\mathrm{bp}}` is the prescribed $`\widehat\rho_{\mathrm{bp}}`.
:::

:::theorem "ex:bandlimited-filter-viii" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_viii") (uses := "ex:bandlimited-filter-vii, ex:bandlimited-filter-i, ex:bandlimited-filter-iii, ex:bandlimited-filter-iv, def:admissible-filter-bandpass")
$`\rho_{\mathrm{bp}}` satisfies the band-pass condition.
:::

:::theorem "ex:bandlimited-filter-ix" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_ix") (uses := "ex:bandlimited-filter-viii, def:admissible-filter-every-alpha")
$`\rho_{\mathrm{bp}}` is $`\alpha`-admissible for every $`\alpha>0`.
:::

:::theorem "ex:bandlimited-filter-x" (lean := "OperatorRidgelet.Paper.ex_bandlimited_filter_x") (uses := "ex:bandlimited-filter-ix")
Multiplying by $`(C^{(\alpha)}_{\rho_{\mathrm{bp}}})^{-1/2}` normalizes the admissibility
constant to one.
:::

:::theorem "ex:mexican-hat-i" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_i") (uses := "filters:mexican-hat")
$`\rho_{\mathrm{MH}}` is a Schwartz function.
:::

:::theorem "ex:mexican-hat-ii" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_ii") (uses := "ex:mexican-hat-i, transform:filter-fourier")
$`\widehat\rho_{\mathrm{MH}}(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}`.
:::

:::theorem "ex:mexican-hat-iii" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_iii") (uses := "ex:mexican-hat-ii, def:admissible-filter")
$`\rho_{\mathrm{MH}}` is $`\alpha`-admissible exactly for $`0<\alpha<5`.
:::

:::theorem "ex:mexican-hat-iv" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_iv") (uses := "ex:mexican-hat-ii, def:admissible-filter-const")
$`C^{(\alpha)}_{\rho_{\mathrm{MH}}}=\Gamma((5-\alpha)/2)` for $`0<\alpha<5`.
:::

:::theorem "ex:mexican-hat-v" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_v") (uses := "ex:mexican-hat-iv")
$`C^{(1)}_{\rho_{\mathrm{MH}}}=1`.
:::

:::theorem "ex:mexican-hat-vi" (lean := "OperatorRidgelet.Paper.ex_mexican_hat_vi") (uses := "ex:mexican-hat-ii, def:admissible-filter-bandpass")
$`\rho_{\mathrm{MH}}` is not band pass.
:::
