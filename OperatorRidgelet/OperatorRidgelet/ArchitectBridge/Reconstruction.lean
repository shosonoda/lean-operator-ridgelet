import Architect
import OperatorRidgelet.Paper.Reconstruction

/-!
# LeanArchitect metadata for Section 4 (representation and reconstruction) and Appendix B

`attribute [blueprint ...]` commands for the declarations of
`OperatorRidgelet.Paper.Reconstruction` and the definitions it uses.  Labels are the manuscript
labels with the part appended; auxiliary definitions carry `reconstruction:` labels.  Statements
whose proof is still `sorry` carry `(notReady := true)`.
-/

/-! ## Definitions -/

attribute [blueprint "reconstruction:spectral-target"
  (statement := /-- The target with spectral density $G$: $g_G(x)=\int_He^{i\langle
    x,\xi\rangle}G(\xi)\,\nu(\mathrm d\xi)$. -/)
  (hasProof := false)] OperatorRidgelet.spectralTarget

attribute [blueprint "reconstruction:frequency-window"
  (statement := /-- A symmetric compact set $I\subset\mathbb R\setminus\{0\}$ containing
    $\operatorname{supp}\widehat\rho$. -/)
  (hasProof := false)] OperatorRidgelet.IsFrequencyWindow

attribute [blueprint "reconstruction:ray-deriv-bound"
  (statement := /-- The ray-derivative bound $\max_{k\le m}\sup_{\omega\in
    I}\|\partial_\omega^kG(\omega a)\|$ at the direction $a$. -/)
  (hasProof := false)] OperatorRidgelet.rayDerivBound

attribute [blueprint "reconstruction:ray-moment"
  (statement := /-- The ray moment $M_m(G)=\int_H(1+\|a\|)^{m+2}\max_{k\le m}\sup_{\omega\in
    I}\|\partial_\omega^kG(\omega a)\|\,\nu(\mathrm da)$. -/)
  (hasProof := false)] OperatorRidgelet.rayMoment

attribute [blueprint "def:ray-regular"
  (statement := /-- A bounded Borel $G$ is regular along rays if $\omega\mapsto G(\omega a)$ is
    $C^\infty$ on a neighbourhood of $I$ for every $a$ and $M_m(G)<\infty$ for every $m$. -/)
  (hasProof := false)] OperatorRidgelet.IsRegularAlongRays

attribute [blueprint "reconstruction:tempered-function"
  (statement := /-- $\beta\in\mathcal S'(\mathbb R)$ is the continuous function $b$ of
    polynomial growth: $b$ is continuous, $|b(t)|\le C(1+|t|)^p$, and
    $\langle\beta,\varphi\rangle=\int b\varphi$. -/)
  (hasProof := false)] OperatorRidgelet.IsTemperedFunction

attribute [blueprint "reconstruction:anti-dual-conj"
  (statement := /-- The linear functional $g\mapsto\overline{F(g)}$ of a continuous
    conjugate-linear functional $F$. -/)
  (hasProof := false)] OperatorRidgelet.antiDualConj

attribute [blueprint "reconstruction:ridgelet-extension"
  (statement := /-- The bounded extension $R_\rho:\mathcal E_\alpha\to L^2(\lambda_\alpha)$ of
    Theorem B(ii), represented on $\mathcal K_\alpha$ and chosen when it exists. -/)
  (hasProof := false)] OperatorRidgelet.ridgeletExtension

attribute [blueprint "reconstruction:ridgelet-range"
  (statement := /-- The range $\operatorname{Ran}R_\rho\subseteq L^2(\lambda_\alpha)$. -/)
  (hasProof := false)] OperatorRidgelet.ridgeletRange

attribute [blueprint "reconstruction:spectral-anti-dual"
  (statement := /-- The continuous anti-dual $\mathcal E_\alpha'$ of $\mathcal E_\alpha$,
    represented as the continuous conjugate-linear functionals on $\mathcal K_\alpha$. -/)
  (hasProof := false)] OperatorRidgelet.SpectralAntiDual

attribute [blueprint "reconstruction:riesz-map"
  (statement := /-- The Riesz map $J_\alpha f[g]=\langle f,g\rangle_{\mathcal E_\alpha}$. -/)
  (hasProof := false)] OperatorRidgelet.rieszMap

attribute [blueprint "reconstruction:riesz-inv"
  (statement := /-- The inverse Riesz map $J_\alpha^{-1}:\mathcal E_\alpha'\to\mathcal E_\alpha$
    (Riesz representation). -/)
  (hasProof := false)] OperatorRidgelet.rieszInv

attribute [blueprint "reconstruction:transpose-embed"
  (statement := /-- The transpose $U_\alpha'F[g]=\langle F,U_\alpha g\rangle_{L^2(\nu_\alpha)}$. -/)
  (hasProof := false)] OperatorRidgelet.transposeEmbed

attribute [blueprint "reconstruction:frame-operator"
  (statement := /-- The frame operator $T_\alpha=U_\alpha'U_\alpha$. -/)
  (hasProof := false)] OperatorRidgelet.frameOperator

attribute [blueprint "reconstruction:synthesis"
  (statement := /-- The synthesis operator $S_\rho=R_\rho'$,
    $(S_\rho\gamma)[g]=\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}$. -/)
  (hasProof := false)] OperatorRidgelet.synthesis

attribute [blueprint "reconstruction:backprojection-of"
  (statement := /-- The ray average $\Lambda_\rho\Phi(\xi)=\frac1{2\pi}\int_{\mathbb
    R}\overline{\widehat\rho(\omega)}|\omega|^{-\alpha}\Phi(-\xi/\omega,\omega)\,\mathrm
    d\omega$ of a bias-Fourier representative $\Phi$. -/)
  (hasProof := false)] OperatorRidgelet.backprojectionOf

attribute [blueprint "reconstruction:backprojection"
  (statement := /-- The backprojection $\Lambda_\rho\gamma$, computed from a jointly measurable
    bias-Fourier representative of $\gamma$. -/)
  (hasProof := false)] OperatorRidgelet.backprojection

attribute [blueprint "reconstruction:backprojection-lp"
  (statement := /-- $\Lambda_\rho\gamma$ as an element of $L^2(\nu_\alpha)$. -/)
  (hasProof := false)] OperatorRidgelet.backprojectionLp

attribute [blueprint "reconstruction:coefficient-projection"
  (statement := /-- The coefficient projection $\Pi_\rho=C^{-1}W_\rho P_{\mathcal
    K_\alpha}\Lambda_\rho$. -/)
  (hasProof := false)] OperatorRidgelet.coefficientProjection

attribute [blueprint "reconstruction:gauss-fourier-line"
  (statement := /-- The analytic continuation $z\mapsto\mathcal G_\mu
    f(z\xi)=\int_Hf(x)e^{-iz\langle x,\xi\rangle}\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierLine

attribute [blueprint "reconstruction:hermite-extension"
  (statement := /-- $G_f(z\xi)=e^{z^2\tau(\xi)^2/2}\mathcal G_Qf(z\xi)$ with
    $\tau(\xi)^2=\langle Q\xi,\xi\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.hermiteExtension

attribute [blueprint "reconstruction:hermite-coefficient"
  (statement := /-- The Hermite coefficient $\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle
    x,\xi\rangle/\tau(\xi))]$. -/)
  (hasProof := false)] OperatorRidgelet.hermiteCoefficient

attribute [blueprint "reconstruction:gauss-fourier-inv"
  (statement := /-- $\Delta_Q$, the inverse of $\mathcal G_Q$ on its range on $\mathcal
    D_\alpha$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierInv

attribute [blueprint "reconstruction:gauss-fourier-vec"
  (statement := /-- The $Y$-valued weighted Fourier transform $\mathcal G_\mu
    f(\xi)=\int_He^{-i\langle x,\xi\rangle}f(x)\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierVec

attribute [blueprint "reconstruction:ridgelet-vec"
  (statement := /-- The $Y$-valued ridgelet transform $R_\rho f(a,c)=\int_H\rho(\langle
    a,x\rangle+c)f(x)\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.ridgeletVec

attribute [blueprint "reconstruction:coefficient-formula-vec"
  (statement := /-- The explicit $Y$-valued coefficient
    $\gamma_G(a,c)=\frac1{2\pi}\int\widehat\rho(\omega)e^{i\omega c}G(-\omega a)\,\mathrm
    d\omega$. -/)
  (hasProof := false)] OperatorRidgelet.coefficientFormulaVec

attribute [blueprint "reconstruction:bias-fourier-vec"
  (statement := /-- The partial Fourier transform in the bias of a $Y$-valued coefficient. -/)
  (hasProof := false)] OperatorRidgelet.biasFourierVec

attribute [blueprint "reconstruction:has-bias-fourier-vec"
  (statement := /-- A $Y$-valued coefficient has partial bias-Fourier transform $\Phi$ (Parseval
    against Schwartz test functions, $\nu$-a.e. direction). -/)
  (hasProof := false)] OperatorRidgelet.HasBiasFourierVec

attribute [blueprint "reconstruction:spectral-coefficient-vec"
  (statement := /-- The $Y$-valued coefficient $W_\rho G\in L^2(\lambda_\alpha;Y)$. -/)
  (hasProof := false)] OperatorRidgelet.spectralCoefficientVec

attribute [blueprint "reconstruction:gauss-fourier-line-vec"
  (statement := /-- The analytic continuation of the $Y$-valued $z\mapsto\mathcal G_\mu
    f(z\xi)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierLineVec

attribute [blueprint "reconstruction:hermite-extension-vec"
  (statement := /-- The $Y$-valued $G_f(z\xi)=e^{z^2\tau(\xi)^2/2}\mathcal G_Qf(z\xi)$. -/)
  (hasProof := false)] OperatorRidgelet.hermiteExtensionVec

attribute [blueprint "reconstruction:hermite-coefficient-vec"
  (statement := /-- The $Y$-valued Hermite coefficient $\mathbb E_{\mu_Q}[\mathrm{He}_n(\langle
    x,\xi\rangle/\tau(\xi))f]$. -/)
  (hasProof := false)] OperatorRidgelet.hermiteCoefficientVec

attribute [blueprint "reconstruction:backprojection-of-vec"
  (statement := /-- The $Y$-valued ray average of a bias-Fourier representative. -/)
  (hasProof := false)] OperatorRidgelet.backprojectionOfVec

attribute [blueprint "reconstruction:backprojection-vec"
  (statement := /-- The $Y$-valued backprojection $\Lambda_\rho\gamma$. -/)
  (hasProof := false)] OperatorRidgelet.backprojectionVec

attribute [blueprint "reconstruction:backprojection-lp-vec"
  (statement := /-- The $Y$-valued $\Lambda_\rho\gamma$ as an element of $L^2(\nu_\alpha;Y)$. -/)
  (hasProof := false)] OperatorRidgelet.backprojectionLpVec

attribute [blueprint "reconstruction:spectral-core-vec"
  (statement := /-- The $Y$-valued core $\mathcal D_\alpha(Y)=\{f\in L^2(\mu;Y):\mathcal G_\mu
    f\in L^2(\nu;Y)\}$. -/)
  (hasProof := false)] OperatorRidgelet.spectralCoreVec

attribute [blueprint "reconstruction:gauss-fourier-lp-vec"
  (statement := /-- $\mathcal G_\mu f$ as an element of $L^2(\nu;Y)$ for $f\in\mathcal
    D_\alpha(Y)$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierLpVec

attribute [blueprint "reconstruction:spectral-range-vec"
  (statement := /-- $\mathcal K_\alpha(Y)=\overline{\mathcal G_\mu(\mathcal
    D_\alpha(Y))}\subseteq L^2(\nu;Y)$, representing $\mathcal E_\alpha(Y)$. -/)
  (hasProof := false)] OperatorRidgelet.spectralRangeVec

attribute [blueprint "reconstruction:spectral-embed-vec"
  (statement := /-- The map $U:\mathcal D_\alpha(Y)\to\mathcal K_\alpha(Y)$, $f\mapsto\mathcal
    G_\mu f$. -/)
  (hasProof := false)] OperatorRidgelet.spectralEmbedVec

attribute [blueprint "reconstruction:ridgelet-extension-vec"
  (statement := /-- The bounded extension $R_\rho:\mathcal E_\alpha(Y)\to
    L^2(\lambda_\alpha;Y)$, chosen when it exists. -/)
  (hasProof := false)] OperatorRidgelet.ridgeletExtensionVec

attribute [blueprint "reconstruction:ridgelet-range-vec"
  (statement := /-- The range $\operatorname{Ran}R_\rho\subseteq L^2(\lambda_\alpha;Y)$. -/)
  (hasProof := false)] OperatorRidgelet.ridgeletRangeVec

attribute [blueprint "reconstruction:gauss-fourier-inv-vec"
  (statement := /-- The $Y$-valued $\Delta_Q$. -/)
  (hasProof := false)] OperatorRidgelet.gaussFourierInvVec

attribute [blueprint "reconstruction:spectral-inner-vec"
  (statement := /-- $\langle f,g\rangle_{\mathcal E_\alpha(Y)}=\int_H\langle\mathcal G_\mu
    f,\mathcal G_\mu g\rangle_Y\,\mathrm d\nu$. -/)
  (hasProof := false)] OperatorRidgelet.spectralInnerVec

attribute [blueprint "reconstruction:spectral-anti-dual-vec"
  (statement := /-- The continuous anti-dual $\mathcal E_\alpha(Y)'$. -/)
  (hasProof := false)] OperatorRidgelet.SpectralAntiDualVec

attribute [blueprint "reconstruction:riesz-map-vec"
  (statement := /-- The Riesz map of $\mathcal E_\alpha(Y)$. -/)
  (hasProof := false)] OperatorRidgelet.rieszMapVec

attribute [blueprint "reconstruction:riesz-inv-vec"
  (statement := /-- The inverse Riesz map of $\mathcal E_\alpha(Y)$. -/)
  (hasProof := false)] OperatorRidgelet.rieszInvVec

attribute [blueprint "reconstruction:transpose-embed-vec"
  (statement := /-- The $Y$-valued transpose $U_\alpha'$. -/)
  (hasProof := false)] OperatorRidgelet.transposeEmbedVec

attribute [blueprint "reconstruction:frame-operator-vec"
  (statement := /-- The $Y$-valued frame operator $T_\alpha=U_\alpha'U_\alpha$. -/)
  (hasProof := false)] OperatorRidgelet.frameOperatorVec

attribute [blueprint "reconstruction:synthesis-vec"
  (statement := /-- The $Y$-valued synthesis operator $S_\rho=R_\rho'$. -/)
  (hasProof := false)] OperatorRidgelet.synthesisVec

attribute [blueprint "reconstruction:coefficient-projection-vec"
  (statement := /-- The $Y$-valued coefficient projection $\Pi_\rho=C^{-1}W_\rho P_{\mathcal
    K_\alpha(Y)}\Lambda_\rho$. -/)
  (hasProof := false)] OperatorRidgelet.coefficientProjectionVec

/-! ## Paper statements -/

attribute [blueprint "def:ray-regular-integrable"
  (statement := /-- A density that is regular along rays belongs to $L^1(\nu_\alpha)\cap
    L^2(\nu_\alpha)$. -/)]
  OperatorRidgelet.Paper.def_ray_regular

attribute [blueprint "thm:A-i-a"
  (statement := /-- For $G\in L^1(\nu_\alpha)$, $\|g_G\|_\infty\le\|G\|_{L^1(\nu_\alpha)}$. -/)]
  OperatorRidgelet.Paper.thm_A_i_a

attribute [blueprint "thm:A-i-b"
  (statement := /-- For $G\in L^1(\nu_\alpha)$, $g_G$ is continuous. -/)]
  OperatorRidgelet.Paper.thm_A_i_b

attribute [blueprint "thm:A-i-c"
  (statement := /-- For $G\in L^1(\nu_\alpha)$, $g_G=0$ only if $G=0$ $\nu_\alpha$-a.e. -/)]
  OperatorRidgelet.Paper.thm_A_i_c

attribute [blueprint "thm:A-ii-a"
  (statement := /-- For $G\in L^1(\nu_\alpha)\cap L^2(\nu_\alpha)$ the iterated integral
    $\int_H[\int_{\mathbb R}\gamma_G(a,c)\rho(\langle a,x\rangle+c)\,\mathrm
    dc]\,\nu_\alpha(\mathrm da)$ converges absolutely. -/)]
  OperatorRidgelet.Paper.thm_A_ii_a

attribute [blueprint "thm:A-ii-b"
  (statement := /-- $\int_H[\int_{\mathbb R}\gamma_G(a,c)\rho(\langle a,x\rangle+c)\,\mathrm
    dc]\,\nu_\alpha(\mathrm da)=C^{(\alpha)}_\rho g_G(x)$. -/)]
  OperatorRidgelet.Paper.thm_A_ii_b

attribute [blueprint "thm:A-ii-c"
  (statement := /-- If moreover $\gamma_G\in L^1(\lambda_\alpha)$, the left side is the integral
    network $S_\rho[\gamma_G\lambda_\alpha](x)$. -/)]
  OperatorRidgelet.Paper.thm_A_ii_c

attribute [blueprint "thm:A-iii-a"
  (statement := /-- For tempered $\beta$ that is a continuous non-polynomial function of
    polynomial growth and $G$ regular along rays, $\int_{\mathbb R}\gamma_G(a,c)\beta(\langle
    a,x\rangle+c)\,\mathrm dc$ converges absolutely for $\nu_\alpha$-a.e. $a$. -/)]
  OperatorRidgelet.Paper.thm_A_iii_a

attribute [blueprint "thm:A-iii-b"
  (statement := /-- The $\nu_\alpha$-integral of the inner integral converges absolutely. -/)]
  OperatorRidgelet.Paper.thm_A_iii_b

attribute [blueprint "thm:A-iii-c"
  (statement := /-- $\int_H[\int_{\mathbb R}\gamma_G(a,c)\beta(\langle a,x\rangle+c)\,\mathrm
    dc]\,\nu_\alpha(\mathrm da)=C^{(\alpha)}_{\beta,\rho}g_G(x)$. -/)]
  OperatorRidgelet.Paper.thm_A_iii_c

attribute [blueprint "thm:A-iii-d"
  (statement := /-- For every non-polynomial $\beta$ a band-pass $\rho$ with
    $C^{(\alpha)}_{\beta,\rho}\ne0$ exists. -/)]
  OperatorRidgelet.Paper.thm_A_iii_d

attribute [blueprint "thm:C-i-a"
  (statement := /-- The frame operator $T_\alpha=U_\alpha'U_\alpha$ equals the Riesz map
    $J_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_i_a

attribute [blueprint "thm:C-i-b"
  (statement := /-- $J_\alpha$ is an isometry $\mathcal E_\alpha\to\mathcal E_\alpha'$. -/)]
  OperatorRidgelet.Paper.thm_C_i_b

attribute [blueprint "thm:C-i-c"
  (statement := /-- $J_\alpha$ is a bijection $\mathcal E_\alpha\to\mathcal E_\alpha'$. -/)]
  OperatorRidgelet.Paper.thm_C_i_c

attribute [blueprint "thm:C-i-d"
  (statement := /-- $S_\rho R_\rho f=C^{(\alpha)}_\rho T_\alpha f$ for $f\in\mathcal E_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_i_d

attribute [blueprint "thm:C-ii-a"
  (statement := /-- $f=(C^{(\alpha)}_\rho)^{-1}T_\alpha^{-1}S_\rho R_\rho f$ for $f\in\mathcal
    E_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_ii_a

attribute [blueprint "thm:C-ii-b"
  (statement := /-- $g=(C^{(\alpha)}_\rho)^{-1}S_\rho(R_\rho T_\alpha^{-1}g)$ for $g\in\mathcal
    E_\alpha'$. -/)]
  OperatorRidgelet.Paper.thm_C_ii_b

attribute [blueprint "thm:C-iii-a"
  (statement := /-- If $f\in\mathcal D_\alpha$ and $\mathcal G_Qf\in L^1(\nu_\alpha)$, then
    $T_\alpha f[g]=\int_Hg_{\mathcal G_Qf}(x)\overline{g(x)}\,\mu_Q(\mathrm dx)$ for
    $g\in\mathcal D_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_iii_a

attribute [blueprint "thm:C-iii-b"
  (statement := /-- For $G\in\mathcal K_\alpha$, $R_\rho T_\alpha^{-1}U_\alpha'G=W_\rho G$. -/)]
  OperatorRidgelet.Paper.thm_C_iii_b

attribute [blueprint "thm:C-iii-c"
  (statement := /-- For $G\in\mathcal K_\alpha\cap L^1(\nu_\alpha)$, $U_\alpha'G$ is represented
    by $g_G$. -/)]
  OperatorRidgelet.Paper.thm_C_iii_c

attribute [blueprint "thm:C-iii-d"
  (statement := /-- For $G\in\mathcal K_\alpha$, $U_\alpha'G=(C^{(\alpha)}_\rho)^{-1}S_\rho
    W_\rho G$. -/)]
  OperatorRidgelet.Paper.thm_C_iii_d

attribute [blueprint "thm:C-iii-e"
  (statement := /-- For $G\in\mathcal K_\alpha\cap L^1(\nu_\alpha)$ with $\gamma_G\in
    L^1(\lambda_\alpha)$, the second reconstruction formula for $U_\alpha'G$ is the spectral
    synthesis identity paired with $g\in\mathcal D_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_iii_e

attribute [blueprint "thm:C-iv-a"
  (statement := /-- $\Lambda_\rho$ is a bounded operator $L^2(\lambda_\alpha)\to
    L^2(\nu_\alpha)$. -/)]
  OperatorRidgelet.Paper.thm_C_iv_a

attribute [blueprint "thm:C-iv-b"
  (statement := /-- $\Lambda_\rho W_\rho=C^{(\alpha)}_\rho\,\mathrm{Id}$. -/)]
  OperatorRidgelet.Paper.thm_C_iv_b

attribute [blueprint "thm:C-iv-c"
  (statement := /-- $\Lambda_\rho R_\rho f=C^{(\alpha)}_\rho\mathcal G_Qf$ pointwise for
    $f\in\mathcal D_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_iv_c

attribute [blueprint "thm:C-iv-d"
  (statement := /-- $\mathbb E_{\mu_Q}[f\,\mathrm{He}_n(\langle
    x,\xi\rangle/\tau(\xi))]=\frac{i^n}{\tau(\xi)^n}\frac{\mathrm d^n}{\mathrm
    dt^n}(e^{t^2\tau(\xi)^2/2}\mathcal G_Qf(t\xi))|_{t=0}$ for $f\in\mathcal D_\alpha$,
    $\xi\ne0$. -/)
  ] OperatorRidgelet.Paper.thm_C_iv_d

attribute [blueprint "thm:C-iv-e"
  (statement := /-- The Hermite coefficients over all $\xi\ne0$ and $n$ determine $f\in\mathcal
    D_\alpha$ in $L^2(\mu_Q)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_C_iv_e

attribute [blueprint "thm:C-iv-f"
  (statement := /-- $f=\Delta_Q[(C^{(\alpha)}_\rho)^{-1}\Lambda_\rho R_\rho f]$ for
    $f\in\mathcal D_\alpha$. -/)]
  OperatorRidgelet.Paper.thm_C_iv_f

attribute [blueprint "lem:weak-equals-strong-i"
  (statement := /-- For real $\rho\in\mathcal S(\mathbb R)$ and $\gamma\in
    L^1(\lambda_\alpha)\cap L^2(\lambda_\alpha)$, $S_\rho[\gamma\lambda_\alpha]$ is a bounded
    Borel function. -/)]
  OperatorRidgelet.Paper.lem_weak_equals_strong_i

attribute [blueprint "lem:weak-equals-strong-ii"
  (statement := /-- $(S_\rho\gamma)[g]=\langle\gamma,R_\rho
    g\rangle_{L^2(\lambda_\alpha)}=\int_HS_\rho[\gamma\lambda_\alpha](x)\overline{g(x)}\,
    \mu_Q(\mathrm dx)$ for $g\in\mathcal D_\alpha$. -/)]
  OperatorRidgelet.Paper.lem_weak_equals_strong_ii

attribute [blueprint "lem:hermite-totality-i"
  (statement := /-- $z\mapsto G_f(z\xi)$ is entire. -/)
  ] OperatorRidgelet.Paper.lem_hermite_totality_i

attribute [blueprint "lem:hermite-totality-ii"
  (statement := /-- $G_f(z\xi)=\sum_n\frac{(-iz\tau(\xi))^n}{n!}\mathbb
    E_{\mu_Q}[f\,\mathrm{He}_n(\langle x,\xi\rangle/\tau(\xi))]$. -/)
  ] OperatorRidgelet.Paper.lem_hermite_totality_ii

attribute [blueprint "lem:hermite-totality-iii"
  (statement := /-- The Hermite series converges locally uniformly. -/)
  ] OperatorRidgelet.Paper.lem_hermite_totality_iii

attribute [blueprint "lem:hermite-totality-iv"
  (statement := /-- $|G_f(z\xi)|\le\|f\|_{L^2(\mu_Q)}e^{|z|^2\tau(\xi)^2/2}$. -/)
  ] OperatorRidgelet.Paper.lem_hermite_totality_iv

attribute [blueprint "lem:hermite-totality-v"
  (statement := /-- The Hermite inversion formula holds for $f\in L^2(\mu_Q)$ and $\xi\ne0$. -/)
  ] OperatorRidgelet.Paper.lem_hermite_totality_v

attribute [blueprint "lem:hermite-totality-vi"
  (statement := /-- The Hermite coefficients over all $\xi\ne0$ and $n$ determine $f$ in
    $L^2(\mu_Q)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_hermite_totality_vi

attribute [blueprint "prop:coefficient-projection-i"
  (statement := /-- The ray-average integral converges absolutely for $\nu_\alpha$-a.e. $\xi$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_i

attribute [blueprint "prop:coefficient-projection-ii"
  (statement := /-- $\Lambda_\rho\gamma$ is independent, as an $L^2$ class, of the jointly
    measurable Fourier representative of $\gamma$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_ii

attribute [blueprint "prop:coefficient-projection-iii"
  (statement := /-- $\|\Lambda_\rho\gamma\|_{L^2(\nu_\alpha)}\le\sqrt C\|\gamma\|_{\mathcal Y}$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_iii

attribute [blueprint "prop:coefficient-projection-iv"
  (statement := /-- $\Lambda_\rho$ is the Hilbert adjoint of $W_\rho$: $\langle\gamma,W_\rho
    F\rangle=\langle\Lambda_\rho\gamma,F\rangle$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_iv

attribute [blueprint "prop:coefficient-projection-v"
  (statement := /-- $\Lambda_\rho W_\rho=C\,\mathrm{Id}$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_v

attribute [blueprint "prop:coefficient-projection-vi"
  (statement := /-- $\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}\Lambda_\rho$ is the orthogonal
    projection onto $\operatorname{Ran}R_\rho$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_vi

attribute [blueprint "prop:coefficient-projection-vii"
  (statement := /-- The minimum-norm solution of $S_\rho\gamma=F\in\mathcal E_\alpha'$ is
    $C^{-1}R_\rho J_\alpha^{-1}F$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_vii

attribute [blueprint "prop:coefficient-projection-viii"
  (statement := /-- All solutions of $S_\rho\gamma=F$ differ from the minimum-norm solution by
    an element of $(\operatorname{Ran}R_\rho)^\perp$. -/)]
  OperatorRidgelet.Paper.prop_coefficient_projection_viii

attribute [blueprint "lem:ray-regular-examples-a"
  (statement := /-- Gaussian-type densities $G(\xi)=q(\xi)e^{-\kappa(\xi)/2}$,
    $\kappa(\xi)=\langle S\xi,\xi\rangle$, $S\ge\theta Q$, with $q$ a polynomial in $\kappa$
    and in functionals $\ell_i$ dominated by the quadratic form,
    $|\ell_i(\xi)|^2\le C_i\kappa(\xi)$, are regular along rays for every band-pass $\rho$. -/)
] OperatorRidgelet.Paper.lem_ray_regular_examples_a

attribute [blueprint "lem:ray-regular-examples-b-i"
  (statement := /-- $G(\xi)=\varphi(\|\xi-\xi_0\|^2)$ with $\varphi\in C_c^\infty(\mathbb R)$ is
    regular along rays for every band-pass $\rho$. -/)]
  OperatorRidgelet.Paper.lem_ray_regular_examples_b_i

attribute [blueprint "lem:ray-regular-examples-b-ii"
  (statement := /-- A bounded $G$ that is $C^\infty$ along rays, vanishes outside a bounded set,
    and has polynomially bounded ray derivatives is regular along rays. -/)]
  OperatorRidgelet.Paper.lem_ray_regular_examples_b_ii

attribute [blueprint "lem:ray-regular-examples-c-i"
  (statement := /-- Finite linear combinations of densities regular along rays are regular along
    rays. -/)]
  OperatorRidgelet.Paper.lem_ray_regular_examples_c_i

attribute [blueprint "lem:ray-regular-examples-c-ii"
  (statement := /-- Bochner integrals $\int G_y\,m(\mathrm dy)$ of a measurable family with
    uniform bounds over a finite measure are regular along rays. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_ray_regular_examples_c_ii

attribute [blueprint "thm:vector-valued-A-i-a"
  (statement := /-- Theorem A for $Y$-valued targets:
    $\|g_G\|_\infty\le\|G\|_{L^1(\nu_\alpha;Y)}$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_i_a

attribute [blueprint "thm:vector-valued-A-i-b"
  (statement := /-- Theorem A for $Y$-valued targets: $g_G$ is continuous. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_i_b

attribute [blueprint "thm:vector-valued-A-i-c"
  (statement := /-- Theorem A for $Y$-valued targets: $g_G=0$ only if $G=0$ $\nu_\alpha$-a.e. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_i_c

attribute [blueprint "thm:vector-valued-A-ii-a"
  (statement := /-- Theorem A for $Y$-valued targets: The iterated integral of Theorem A(ii)
    converges absolutely. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_ii_a

attribute [blueprint "thm:vector-valued-A-ii-b"
  (statement := /-- Theorem A for $Y$-valued targets: $\int_H[\int_{\mathbb R}\rho(\langle
    a,x\rangle+c)\gamma_G(a,c)\,\mathrm dc]\,\nu_\alpha(\mathrm da)=C^{(\alpha)}_\rho g_G(x)$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_ii_b

attribute [blueprint "thm:vector-valued-A-ii-c"
  (statement := /-- Theorem A for $Y$-valued targets: If $\gamma_G\in L^1(\lambda_\alpha;Y)$,
    the left side is the integral network $S_\rho[\gamma_G\lambda_\alpha](x)$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_ii_c

attribute [blueprint "thm:vector-valued-A-iii-a"
  (statement := /-- Theorem A for $Y$-valued targets: The inner integral with a tempered $\beta$
    converges absolutely for $\nu_\alpha$-a.e. $a$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_iii_a

attribute [blueprint "thm:vector-valued-A-iii-b"
  (statement := /-- Theorem A for $Y$-valued targets: The outer integral converges absolutely. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_iii_b

attribute [blueprint "thm:vector-valued-A-iii-c"
  (statement := /-- Theorem A for $Y$-valued targets: $\int_H[\int_{\mathbb R}\beta(\langle
    a,x\rangle+c)\gamma_G(a,c)\,\mathrm dc]\,\nu_\alpha(\mathrm
    da)=C^{(\alpha)}_{\beta,\rho}g_G(x)$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_iii_c

attribute [blueprint "thm:vector-valued-B-i-a"
  (statement := /-- Theorem B for $Y$-valued targets: $R_\rho f\in L^2(\lambda_\alpha;Y)$ for
    $f\in\mathcal D_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_i_a

attribute [blueprint "thm:vector-valued-B-i-b"
  (statement := /-- Theorem B for $Y$-valued targets: $\langle
    R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda_\alpha;Y)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle
    f,g\rangle_{\mathcal E_\alpha(Y)}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_i_b

attribute [blueprint "thm:vector-valued-B-ii-a"
  (statement := /-- Theorem B for $Y$-valued targets: An $\alpha$-admissible $\rho$ determines a
    unique bounded extension $R_\rho:\mathcal E_\alpha(Y)\to L^2(\lambda_\alpha;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_ii_a

attribute [blueprint "thm:vector-valued-B-ii-b"
  (statement := /-- Theorem B for $Y$-valued targets: $\|R_\rho
    f\|^2=C^{(\alpha)}_\rho\|f\|_{\mathcal E_\alpha(Y)}^2$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_ii_b

attribute [blueprint "thm:vector-valued-B-ii-c"
  (statement := /-- Theorem B for $Y$-valued targets: The range of $R_\rho$ is closed. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_ii_c

attribute [blueprint "thm:vector-valued-B-ii-d"
  (statement := /-- Theorem B for $Y$-valued targets: $R_\rho=W_\rho U_\alpha$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_ii_d

attribute [blueprint "thm:vector-valued-B-iii"
  (statement := /-- Theorem B for $Y$-valued targets: $R_\rho f=0$ $\lambda_\alpha$-a.e. implies
    $f=0$ $\mu_Q$-a.e. for $f\in L^2(\mu_Q;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_B_iii

attribute [blueprint "thm:vector-valued-C-i-a"
  (statement := /-- Theorem C for $Y$-valued targets: $T_\alpha=J_\alpha$ on $\mathcal
    E_\alpha(Y)$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_C_i_a

attribute [blueprint "thm:vector-valued-C-i-b"
  (statement := /-- Theorem C for $Y$-valued targets: $J_\alpha$ is an isometry $\mathcal
    E_\alpha(Y)\to\mathcal E_\alpha(Y)'$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_C_i_b

attribute [blueprint "thm:vector-valued-C-i-c"
  (statement := /-- Theorem C for $Y$-valued targets: $J_\alpha$ is a bijection $\mathcal
    E_\alpha(Y)\to\mathcal E_\alpha(Y)'$. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_C_i_c

attribute [blueprint "thm:vector-valued-C-i-d"
  (statement := /-- Theorem C for $Y$-valued targets: $S_\rho R_\rho f=C^{(\alpha)}_\rho
    T_\alpha f$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_i_d

attribute [blueprint "thm:vector-valued-C-ii-a"
  (statement := /-- Theorem C for $Y$-valued targets:
    $f=(C^{(\alpha)}_\rho)^{-1}T_\alpha^{-1}S_\rho R_\rho f$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_ii_a

attribute [blueprint "thm:vector-valued-C-ii-b"
  (statement := /-- Theorem C for $Y$-valued targets: $g=(C^{(\alpha)}_\rho)^{-1}S_\rho(R_\rho
    T_\alpha^{-1}g)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_ii_b

attribute [blueprint "thm:vector-valued-C-iii-a"
  (statement := /-- Theorem C for $Y$-valued targets: $T_\alpha f[g]=\int_H\langle g_{\mathcal
    G_Qf}(x),g(x)\rangle_Y\,\mu_Q(\mathrm dx)$ for $f\in\mathcal D_\alpha(Y)$ with $\mathcal
    G_Qf\in L^1(\nu_\alpha;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iii_a

attribute [blueprint "thm:vector-valued-C-iii-b"
  (statement := /-- Theorem C for $Y$-valued targets: $R_\rho T_\alpha^{-1}U_\alpha'G=W_\rho G$
    for $G\in\mathcal K_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iii_b

attribute [blueprint "thm:vector-valued-C-iii-c"
  (statement := /-- Theorem C for $Y$-valued targets: For $G\in\mathcal K_\alpha(Y)\cap
    L^1(\nu_\alpha;Y)$, $U_\alpha'G$ is represented by $g_G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iii_c

attribute [blueprint "thm:vector-valued-C-iii-d"
  (statement := /-- Theorem C for $Y$-valued targets: $U_\alpha'G=(C^{(\alpha)}_\rho)^{-1}S_\rho
    W_\rho G$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iii_d

attribute [blueprint "thm:vector-valued-C-iii-e"
  (statement := /-- Theorem C for $Y$-valued targets: The second reconstruction formula for
    $U_\alpha'G$ is the spectral synthesis identity paired with $g\in\mathcal D_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iii_e

attribute [blueprint "thm:vector-valued-C-iv-a"
  (statement := /-- Theorem C for $Y$-valued targets: $\Lambda_\rho$ is a bounded operator
    $L^2(\lambda_\alpha;Y)\to L^2(\nu_\alpha;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_a

attribute [blueprint "thm:vector-valued-C-iv-b"
  (statement := /-- Theorem C for $Y$-valued targets: $\Lambda_\rho
    W_\rho=C^{(\alpha)}_\rho\,\mathrm{Id}$ on $L^2(\nu_\alpha;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_b

attribute [blueprint "thm:vector-valued-C-iv-c"
  (statement := /-- Theorem C for $Y$-valued targets: $\Lambda_\rho R_\rho
    f=C^{(\alpha)}_\rho\mathcal G_Qf$ pointwise for $f\in\mathcal D_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_c

attribute [blueprint "thm:vector-valued-C-iv-d"
  (statement := /-- Theorem C for $Y$-valued targets: The Hermite inversion formula holds
    componentwise for $f\in\mathcal D_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_d

attribute [blueprint "thm:vector-valued-C-iv-e"
  (statement := /-- Theorem C for $Y$-valued targets: The Hermite coefficients determine
    $f\in\mathcal D_\alpha(Y)$ in $L^2(\mu_Q;Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_e

attribute [blueprint "thm:vector-valued-C-iv-f"
  (statement := /-- Theorem C for $Y$-valued targets:
    $f=\Delta_Q[(C^{(\alpha)}_\rho)^{-1}\Lambda_\rho R_\rho f]$ for $f\in\mathcal D_\alpha(Y)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_vector_valued_C_iv_f
