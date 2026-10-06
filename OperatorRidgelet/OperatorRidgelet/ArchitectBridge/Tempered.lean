import Architect
import OperatorRidgelet.Paper.Tempered

/-!
# LeanArchitect metadata for Section 5

Reconstruction formulas and activation functions.

`attribute [blueprint ...]` commands for the declarations of `OperatorRidgelet.Paper.Tempered`
and the definitions it uses.  Labels are the manuscript labels with the part appended; auxiliary
definitions carry `tempered:` labels.  Statements whose proof is still `sorry` carry
`(notReady := true)`.
-/

/-! ## Definitions: the distributional admissibility constant (shared with Section 4) -/

attribute [blueprint "tempered:test-filter"
  (statement := /-- The test filter $\omega\mapsto\rho^\sharp(-\omega)|\omega|^{-\alpha}$ as
    a Schwartz function (when one with these values exists, in particular for band-pass
    $\rho$). -/)
  (hasProof := false)] OperatorRidgelet.temperedTestFilter

attribute [blueprint "tempered:admissibility-const"
  (statement := /-- The distributional admissibility constant
    $C^{(\alpha)}_{\beta,\rho}=\frac1{2\pi}\langle\beta^\sharp,
    \rho^\sharp(-\,\cdot\,)|\cdot|^{-\alpha}\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.temperedAdmissibilityConst

/-! ## Definitions: real distributions, cutoffs, approximate identities -/

attribute [blueprint "tempered:real-distribution"
  (statement := /-- $\beta\in\mathcal S'(\mathbb R)$ is real: it is fixed by distributional
    conjugation $\overline u[\varphi]=\overline{u[\overline\varphi]}$. -/)
  (hasProof := false)] OperatorRidgelet.IsRealDistribution

attribute [blueprint "tempered:polynomial-distribution"
  (statement := /-- $\beta\in\mathcal S'(\mathbb R)$ is a polynomial, i.e. $\beta=0$ in
    $\mathcal S'/\mathcal P$: it acts by integration against some $p\in\mathbb C[x]$. -/)
  (hasProof := false)] OperatorRidgelet.IsPolynomialDistribution

attribute [blueprint "tempered:schwartz-of-fun"
  (statement := /-- The Schwartz function with prescribed values, when one exists. -/)
  (hasProof := false)] OperatorRidgelet.schwartzOfFun

attribute [blueprint "tempered:distribution-convolution"
  (statement := /-- The convolution $(u*\eta)(\omega)=\langle u,\eta(\omega-\cdot)\rangle$ of
    a tempered distribution with a test function. -/)
  (hasProof := false)] OperatorRidgelet.distributionConvolution

attribute [blueprint "def:5.3-cutoff"
  (statement := /-- An even $\chi\in C_c^\infty(\mathbb R\setminus\{0\})$ equal to one on a
    neighbourhood of $\operatorname{supp}\rho^\sharp$. -/)
  (hasProof := false)] OperatorRidgelet.IsCutoff

attribute [blueprint "def:5.3-approximate-identity"
  (statement := /-- An even, compactly supported, smooth approximate identity
    $(\eta_\varepsilon)_{\varepsilon>0}$: nonnegative, of integral one, with supports shrinking
    to $\{0\}$. -/)
  (hasProof := false)] OperatorRidgelet.IsApproximateIdentity

attribute [blueprint "def:5.3-spectrum"
  (statement := /-- The regularized spectrum
    $\beta_\varepsilon^\sharp=\chi\,(\beta^\sharp*\eta_\varepsilon)$. -/)
  (hasProof := false)] OperatorRidgelet.regularizedSpectrum

attribute [blueprint "def:5.3-activation"
  (statement := /-- The real Schwartz function $\beta_\varepsilon$ with
    $\beta_\varepsilon^\sharp=\chi\,(\beta^\sharp*\eta_\varepsilon)$. -/)
  (hasProof := false)] OperatorRidgelet.regularizedActivation

/-! ## Definitions: regularized synthesis and its limit

The anti-dual `𝓔_α'`, the extended transform `R_ρ`, the synthesis `S_ρ`, the Riesz map and its
inverse, the target `g_G`, and regularity along rays are the Section 4 definitions tagged in
`OperatorRidgelet.ArchitectBridge.Reconstruction`. -/

attribute [blueprint "def:5.3-regularized"
  (statement := /-- The regularized synthesis
    $S_{\beta_\varepsilon}\gamma:=R_{\beta_\varepsilon}'\gamma\in\mathcal E_\alpha'$. -/)
  (hasProof := false)] OperatorRidgelet.regularizedSynthesis

attribute [blueprint "def:5.3"
  (statement := /-- Synthesis with an activation represented by a real tempered distribution,
    $S_\beta\gamma:=\lim_{\varepsilon\downarrow0}S_{\beta_\varepsilon}\gamma$ in
    the norm of $\mathcal E_\alpha'$, whenever the limit exists. -/)
  (hasProof := false)] OperatorRidgelet.temperedSynthesis

/-! ## Definitions: standard activations and the weighted Sobolev spaces -/

attribute [blueprint "tempered:weighted-distribution"
  (statement := /-- The tempered distribution $\langle x\rangle^t(\langle x\rangle^{-t}\beta)$
    of a function $\beta$ with $\langle x\rangle^{-t}\beta\in L^2(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.weightedDistribution

attribute [blueprint "tempered:relu-distribution"
  (statement := /-- $\operatorname{ReLU}\in\mathcal S'(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.reluDistribution

attribute [blueprint "tempered:tanh-distribution"
  (statement := /-- $\tanh\in\mathcal S'(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.tanhDistribution

attribute [blueprint "tempered:gaussian-cdf"
  (statement := /-- The Gaussian distribution function
    $\Phi(u)=\int_{-\infty}^u(2\pi)^{-1/2}e^{-v^2/2}\,\mathrm dv$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianCdf

attribute [blueprint "tempered:gaussian-cdf-distribution"
  (statement := /-- $\Phi\in\mathcal S'(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianCdfDistribution

attribute [blueprint "tempered:gaussian-fun"
  (statement := /-- The Gaussian activation $u\mapsto e^{-u^2/2}$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianFun

attribute [blueprint "tempered:gaussian-distribution"
  (statement := /-- $e^{-u^2/2}\in\mathcal S'(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussianDistribution

attribute [blueprint "tempered:mem-activation-space-fun"
  (statement := /-- A function $\beta$ belongs to $\mathcal A_{s,t}$: some tempered distribution
    acting by integration against $\beta$ lies in
    $\mathcal A_{s,t}=\langle\cdot\rangle^tH^s(\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.MemActivationSpaceFun

attribute [blueprint "cor:5.5-scale"
  (statement := /-- The constant $-\frac1{2\pi}\int_{\mathbb
    R}\rho^\sharp(\omega)|\omega|^{-\alpha-2}\,\mathrm d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.reluAdmissibilityScale

attribute [blueprint "cor:5.5-normalized-filter"
  (statement := /-- The filter $\rho$ rescaled so that
    $C^{(\alpha)}_{\operatorname{ReLU},\rho}=1$. -/)
  (hasProof := false)] OperatorRidgelet.reluNormalizedFilter

attribute [blueprint "lem:5.1-fourier-coordinate"
  (statement := /-- The coordinate $\langle\omega\rangle^sB^{-t}\beta^\sharp$ as a tempered
    distribution. -/)
  (hasProof := false)] OperatorRidgelet.activationFourierCoordinate

attribute [blueprint "lem:5.1-coordinate"
  (statement := /-- The element of $L^2(\mathbb R)$ representing
    $\langle\omega\rangle^sB^{-t}\beta^\sharp$, when there is one. -/)
  (hasProof := false)] OperatorRidgelet.activationCoordinate

attribute [blueprint "lem:5.1-norm"
  (statement := /-- $\|\beta\|_{\mathcal
    A_{s,t}}=\|\langle\omega\rangle^sB^{-t}\beta^\sharp\|_{L^2}$. -/)
  (hasProof := false)] OperatorRidgelet.activationNorm

attribute [blueprint "lem:5.1-test-coordinate"
  (statement := /-- The test coordinate $\langle\omega\rangle^{-s}B^tr$ of a Schwartz filter
    $r$. -/)
  (hasProof := false)] OperatorRidgelet.testFilterCoordinate

attribute [blueprint "lem:5.1-test-norm"
  (statement := /-- The dual test norm $\|r\|_{\mathcal
    H^\sharp_{s,t}}=\|\langle\omega\rangle^{-s}B^tr\|_{L^2}$. -/)
  (hasProof := false)] OperatorRidgelet.testFilterNorm

/-! ## Paper statements: Definition `def:5.3` -/

attribute [blueprint "def:5.3-i"
  (statement := /-- For band-pass $\rho$ there is an even $\chi\in C_c^\infty(\mathbb
    R\setminus\{0\})$ equal to one on a neighbourhood of $\operatorname{supp}\rho^\sharp$. -/)]
  OperatorRidgelet.Paper.def_5_3_i

attribute [blueprint "def:5.3-ii"
  (statement := /-- There is an even, compactly supported, smooth approximate identity
    $(\eta_\varepsilon)_{\varepsilon>0}$. -/)]
  OperatorRidgelet.Paper.def_5_3_ii

attribute [blueprint "def:5.3-iii"
  (statement := /-- $\beta_\varepsilon^\sharp=\chi(\beta^\sharp*\eta_\varepsilon)\in
    C_c^\infty(\mathbb R\setminus\{0\})$. -/)]
  OperatorRidgelet.Paper.def_5_3_iii

attribute [blueprint "def:5.3-iv"
  (statement := /-- There is a real Schwartz function $\beta_\varepsilon$ with
    $\beta_\varepsilon^\sharp=\chi(\beta^\sharp*\eta_\varepsilon)$. -/)]
  OperatorRidgelet.Paper.def_5_3_iv

attribute [blueprint "def:5.3-v"
  (statement := /-- The real Schwartz function $\beta_\varepsilon$ is unique. -/)]
  OperatorRidgelet.Paper.def_5_3_v

attribute [blueprint "def:5.3-vi"
  (statement := /-- For $\gamma\in\operatorname{Ran}R_\rho$,
    $S_{\beta_\varepsilon}\gamma=R_{\beta_\varepsilon}'\gamma$ is the continuous anti-linear
    functional $g\mapsto\langle\gamma,R_{\beta_\varepsilon}g\rangle_{L^2(\lambda_\alpha)}$. -/)]
  OperatorRidgelet.Paper.def_5_3_vi

/-! ## Paper statements: Theorem `thm:5.4` -/

attribute [blueprint "thm:5.4-i"
  (statement := /-- For every $f\in\mathcal E_\alpha$ the limit
    $\lim_{\varepsilon\downarrow0}S_{\beta_\varepsilon}R_\rho f$ exists in $\mathcal
    E_\alpha'$. -/)]
  OperatorRidgelet.Paper.thm_5_4_i

attribute [blueprint "thm:5.4-ii"
  (statement := /-- The limit $S_\beta R_\rho f$ does not depend on $\chi$ or
    $(\eta_\varepsilon)$. -/)]
  OperatorRidgelet.Paper.thm_5_4_ii

attribute [blueprint "thm:5.4-iii"
  (statement := /-- $S_\beta R_\rho f=C^{(\alpha)}_{\beta,\rho}T_\alpha f$ for
    $f\in\mathcal E_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_5_4_iii

attribute [blueprint "thm:5.4-iv"
  (statement := /-- If $C^{(\alpha)}_{\beta,\rho}\ne0$, then
    $f=(C^{(\alpha)}_{\beta,\rho})^{-1}T_\alpha^{-1}S_\beta R_\rho f$ for
    $f\in\mathcal E_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_5_4_iv

attribute [blueprint "thm:5.4-v"
  (statement := /-- If $C^{(\alpha)}_{\beta,\rho}\ne0$, then
    $g=(C^{(\alpha)}_{\beta,\rho})^{-1}S_\beta(R_\rho T_\alpha^{-1}g)$ for
    $g\in\mathcal E_\alpha'$. -/)]
  OperatorRidgelet.Paper.thm_5_4_v

attribute [blueprint "thm:5.4-vi"
  (statement := /-- If $\beta$ is not a polynomial, then a band-pass $\rho$ with
    $C^{(\alpha)}_{\beta,\rho}\ne0$ exists. -/)]
  OperatorRidgelet.Paper.thm_5_4_vi

/-! ## Paper statements: Corollary `cor:5.5` -/

attribute [blueprint "cor:5.5-i"
  (statement := /-- $\operatorname{ReLU}^\sharp=-\operatorname{fp}(\omega^{-2})+i\pi\delta_0'$:
    tested against $\varphi$, the finite part
    $\lim_{\varepsilon\downarrow0}\bigl(\int_{|\omega|>\varepsilon}\varphi(\omega)\omega^{-2}\,
    \mathrm d\omega-2\varphi(0)/\varepsilon\bigr)$ equals
    $-\langle\operatorname{ReLU}^\sharp,\varphi\rangle-i\pi\varphi'(0)$. -/)]
  OperatorRidgelet.Paper.cor_5_5_i

attribute [blueprint "cor:5.5-ii"
  (statement := /-- $\operatorname{ReLU}^\sharp=-\omega^{-2}$ away from the origin. -/)]
  OperatorRidgelet.Paper.cor_5_5_ii

attribute [blueprint "cor:5.5-iii"
  (statement := /-- For nonzero, even, nonpositive $\rho^\sharp\in C_c^\infty(\mathbb
    R\setminus\{0\})$, $C^{(\alpha)}_{\operatorname{ReLU},\rho}=-\frac1{2\pi}\int_{\mathbb
    R}\rho^\sharp(\omega)|\omega|^{-\alpha-2}\,\mathrm d\omega$. -/)]
  OperatorRidgelet.Paper.cor_5_5_iii

attribute [blueprint "cor:5.5-iv"
  (statement := /-- $-\frac1{2\pi}\int_{\mathbb R}\rho^\sharp(\omega)|\omega|^{-\alpha-2}\,
    \mathrm d\omega>0$. -/)]
  OperatorRidgelet.Paper.cor_5_5_iv

attribute [blueprint "cor:5.5-v"
  (statement := /-- After rescaling, $\rho$ is band-pass and
    $C^{(\alpha)}_{\operatorname{ReLU},\rho}=1$. -/)]
  OperatorRidgelet.Paper.cor_5_5_v

attribute [blueprint "cor:5.5-vi"
  (statement := /-- With the rescaled filter, $f=T_\alpha^{-1}S_{\operatorname{ReLU}}R_\rho f$
    for $f\in\mathcal E_\alpha$ and every $\alpha>0$. -/)]
  OperatorRidgelet.Paper.cor_5_5_vi

attribute [blueprint "cor:5.5-vii"
  (statement := /-- With the rescaled filter, $g=S_{\operatorname{ReLU}}(R_\rho T_\alpha^{-1}g)$
    for $g\in\mathcal E_\alpha'$ and every $\alpha>0$. -/)]
  OperatorRidgelet.Paper.cor_5_5_vii

attribute [blueprint "cor:5.5-viii"
  (statement := /-- With the rescaled filter, Theorem 4.5(iii) holds with ReLU synthesis: for $G$
    regular along rays and every $x$, $\int_H\int_{\mathbb R}\gamma_G(a,c)\operatorname{ReLU}
    (\langle a,x\rangle+c)\,\mathrm dc\,\nu_\alpha(\mathrm da)=g_G(x)$ with absolute
    convergence. -/)]
  OperatorRidgelet.Paper.cor_5_5_viii

/-! ## Paper statements: Example `ex:5.6` -/

attribute [blueprint "ex:5.6-relu"
  (statement := /-- For every $\alpha>0$ there is a band-pass $\rho$ with
    $C^{(\alpha)}_{\operatorname{ReLU},\rho}\ne0$. -/)]
  OperatorRidgelet.Paper.ex_5_6_relu

attribute [blueprint "ex:5.6-tanh"
  (statement := /-- For every $\alpha>0$ there is a band-pass $\rho$ with
    $C^{(\alpha)}_{\tanh,\rho}\ne0$. -/)]
  OperatorRidgelet.Paper.ex_5_6_tanh

attribute [blueprint "ex:5.6-gaussian-cdf"
  (statement := /-- For every $\alpha>0$ there is a band-pass $\rho$ with
    $C^{(\alpha)}_{\Phi,\rho}\ne0$. -/)]
  OperatorRidgelet.Paper.ex_5_6_gaussianCdf

attribute [blueprint "ex:5.6-gaussian"
  (statement := /-- For every $\alpha>0$ there is a band-pass $\rho$ with
    $C^{(\alpha)}_{e^{-u^2/2},\rho}\ne0$. -/)]
  OperatorRidgelet.Paper.ex_5_6_gaussian

/-! ## Paper statements: Lemma `lem:5.1` -/

attribute [blueprint "lem:5.1-i"
  (statement := /-- For $\beta\in\mathcal A_{s,t}$ the coordinate
    $\langle\omega\rangle^sB^{-t}\beta^\sharp$ is represented by an element of $L^2(\mathbb
    R)$. -/)]
  OperatorRidgelet.Paper.lem_5_1_i

attribute [blueprint "lem:5.1-ii"
  (statement := /-- $\beta\mapsto\langle\omega\rangle^sB^{-t}\beta^\sharp$ is injective on
    $\mathcal A_{s,t}$. -/)]
  OperatorRidgelet.Paper.lem_5_1_ii

attribute [blueprint "lem:5.1-iii"
  (statement := /-- $\beta\mapsto\langle\omega\rangle^sB^{-t}\beta^\sharp$ is onto $L^2(\mathbb
    R)$: every $\sigma$ is the coordinate of
    $\beta=F_{\mathbb R}^{-1}[B^t\langle\omega\rangle^{-s}\sigma]\in\mathcal A_{s,t}$. -/)]
  OperatorRidgelet.Paper.lem_5_1_iii

attribute [blueprint "lem:5.1-iv"
  (statement := /-- $\bigl|\frac1{2\pi}\langle\beta^\sharp,r\rangle\bigr|\le\frac1{2\pi}
    \|\beta\|_{\mathcal A_{s,t}}\|r\|_{\mathcal T^\sharp_{s,t}}$. -/)]
  OperatorRidgelet.Paper.lem_5_1_iv

attribute [blueprint "lem:5.1-v"
  (statement := /-- The pairing extends to the completion of the test filters in $\mathcal
    H^\sharp_{s,t}$. -/)]
  OperatorRidgelet.Paper.lem_5_1_v

/-! ## Paper statements: Lemma `lem:5.2` -/

attribute [blueprint "lem:5.2-relu-mem"
  (statement := /-- $\operatorname{ReLU}\in\mathcal A_{0,2}$. -/)]
  OperatorRidgelet.Paper.lem_5_2_relu_mem

attribute [blueprint "lem:5.2-relu-lipschitz"
  (statement := /-- $\operatorname{ReLU}$ is globally Lipschitz. -/)]
  OperatorRidgelet.Paper.lem_5_2_relu_lipschitz

attribute [blueprint "lem:5.2-relu-not-polynomial"
  (statement := /-- $\operatorname{ReLU}$ is not a polynomial. -/)]
  OperatorRidgelet.Paper.lem_5_2_relu_not_polynomial

attribute [blueprint "lem:5.2-tanh-mem"
  (statement := /-- $\tanh\in\mathcal A_{0,2}$. -/)]
  OperatorRidgelet.Paper.lem_5_2_tanh_mem

attribute [blueprint "lem:5.2-tanh-lipschitz"
  (statement := /-- $\tanh$ is globally Lipschitz. -/)]
  OperatorRidgelet.Paper.lem_5_2_tanh_lipschitz

attribute [blueprint "lem:5.2-tanh-not-polynomial"
  (statement := /-- $\tanh$ is not a polynomial. -/)]
  OperatorRidgelet.Paper.lem_5_2_tanh_not_polynomial

attribute [blueprint "lem:5.2-gaussian-cdf-mem"
  (statement := /-- $\Phi\in\mathcal A_{0,2}$. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussianCdf_mem

attribute [blueprint "lem:5.2-gaussian-cdf-lipschitz"
  (statement := /-- $\Phi$ is globally Lipschitz. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussianCdf_lipschitz

attribute [blueprint "lem:5.2-gaussian-cdf-not-polynomial"
  (statement := /-- $\Phi$ is not a polynomial. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussianCdf_not_polynomial

attribute [blueprint "lem:5.2-gaussian-mem"
  (statement := /-- $e^{-u^2/2}\in\mathcal A_{0,2}$. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussian_mem

attribute [blueprint "lem:5.2-gaussian-lipschitz"
  (statement := /-- $e^{-u^2/2}$ is globally Lipschitz. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussian_lipschitz

attribute [blueprint "lem:5.2-gaussian-not-polynomial"
  (statement := /-- $e^{-u^2/2}$ is not a polynomial. -/)]
  OperatorRidgelet.Paper.lem_5_2_gaussian_not_polynomial

attribute [blueprint "lem:5.2-exists-filter"
  (statement := /-- For every non-polynomial real $\beta\in\mathcal S'$ there is a real
    band-pass $\rho$ with $C^{(\alpha)}_{\beta,\rho}=1$. -/)]
  OperatorRidgelet.Paper.lem_5_2_exists_filter
