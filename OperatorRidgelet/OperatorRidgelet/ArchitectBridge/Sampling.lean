import Architect
import OperatorRidgelet.Paper.Sampling

/-!
# LeanArchitect metadata for Section 6 (finite-width approximation) and Appendix D

`attribute [blueprint ...]` commands for the declarations of `OperatorRidgelet.Paper.Sampling`
and the definitions it uses.  Labels are the manuscript labels with the part appended;
auxiliary definitions carry `sampling:` labels.  Statements whose proof is still `sorry` carry
`(notReady := true)`.
-/

/-! ## Definitions -/

attribute [blueprint "sampling:compact-sup-norm"
  (statement := /-- The compact-open seminorm $\|f\|_{C(K;Y)}=\sup_{x\in K}\|f(x)\|_Y$. -/)
  (hasProof := false)] OperatorRidgelet.compactSupNorm

attribute [blueprint "sampling:compact-radius"
  (statement := /-- $R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}$. -/)
  (hasProof := false)] OperatorRidgelet.compactRadius

attribute [blueprint "sampling:polar-density"
  (statement := /-- The phase $h$ of the polar decomposition $\Gamma=h|\Gamma|$, $|h|=1$
    $|\Gamma|$-almost everywhere. -/)
  (hasProof := false)] OperatorRidgelet.polarDensity

attribute [blueprint "sampling:polar-weight"
  (statement := /-- $V=\|\Gamma\|_{\mathrm{TV}}$. -/)
  (hasProof := false)] OperatorRidgelet.polarWeight

attribute [blueprint "sampling:polar-law"
  (statement := /-- The parameter law $p=|\Gamma|/V$. -/)
  (hasProof := false)] OperatorRidgelet.polarLaw

attribute [blueprint "sampling:density-weight"
  (statement := /-- $V=\|\gamma\|_{L^1(\lambda)}$ for a coefficient measure $\gamma\lambda$. -/)
  (hasProof := false)] OperatorRidgelet.densityWeight

attribute [blueprint "sampling:density-law"
  (statement := /-- $p=|\gamma|\lambda/V$ for a coefficient measure $\gamma\lambda$. -/)
  (hasProof := false)] OperatorRidgelet.densityLaw

attribute [blueprint "sampling:density-phase"
  (statement := /-- $h=\gamma/|\gamma|$ for a coefficient measure $\gamma\lambda$. -/)
  (hasProof := false)] OperatorRidgelet.densityPhase

attribute [blueprint "sampling:sample-law"
  (statement := /-- The law $p^{\otimes N}$ of $N$ independent samples $\theta_j\sim p$. -/)
  (hasProof := false)] OperatorRidgelet.sampleLaw

attribute [blueprint "sampling:rademacher-measure"
  (statement := /-- The law of $N$ independent Rademacher signs $\varepsilon_j\in\{-1,1\}$. -/)
  (hasProof := false)] OperatorRidgelet.rademacherMeasure

attribute [blueprint "sampling:sampled-network"
  (statement := /-- The sampled network
    $f_N(x)=\frac VN\sum_{j=1}^Nh(\theta_j)\beta(\langle a_j,x\rangle+c_j)$. -/)
  (hasProof := false)] OperatorRidgelet.sampledNetwork

attribute [blueprint "sampling:polar-sampled-network"
  (statement := /-- The sampled network of the polar decomposition of $\Gamma$. -/)
  (hasProof := false)] OperatorRidgelet.polarSampledNetwork

attribute [blueprint "sampling:density-sampled-network"
  (statement := /-- The sampled network of a coefficient measure $\gamma\lambda$ with
    $V=\|\gamma\|_{L^1(\lambda)}$, $p=|\gamma|\lambda/V$, $h=\gamma/|\gamma|$. -/)
  (hasProof := false)] OperatorRidgelet.densitySampledNetwork

attribute [blueprint "def:rademacher-complexity"
  (statement := /-- For compact $K\subset H$,
    $\mathfrak R_N(K;p,\beta)=\mathbb E_{\theta,\varepsilon}\sup_{x\in K}
    \bigl|\frac1N\sum_{j=1}^N\varepsilon_jh(\theta_j)\beta(\langle a_j,x\rangle+c_j)\bigr|$
    with independent $\theta_j\sim p$ and independent Rademacher signs $\varepsilon_j$; with
    $Y$-valued phases it is $\mathfrak R_N^Y(K;p,\beta)$. -/)
  (hasProof := false)] OperatorRidgelet.rademacherComplexity

attribute [blueprint "sampling:second-moment"
  (statement := /-- $M_2^2=\int_{H\times\mathbb R}(\|a\|^2+|c|^2)\,p(\mathrm da,\mathrm dc)$. -/)
  (hasProof := false)] OperatorRidgelet.secondMoment

attribute [blueprint "sampling:atomic-measure"
  (statement := /-- The finite atomic measure $\sum_jw_j\delta_{\theta_j}$. -/)
  (hasProof := false)] OperatorRidgelet.atomicMeasure

attribute [blueprint "sampling:sampled-operator-network"
  (statement := /-- The sampled operator network
    $f_{{\rm op},N}(x)=\frac VN\sum_jh_{\rm op}(A_j,b_j)\,\mathrm n_{\ell,A_j,b_j}(x)$. -/)
  (hasProof := false)] OperatorRidgelet.sampledOperatorNetwork

attribute [blueprint "sampling:operator-second-moment"
  (statement := /-- $M_{\rm op}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,
    \mathrm dp_{\rm op}$. -/)
  (hasProof := false)] OperatorRidgelet.operatorSecondMoment

attribute [blueprint "sampling:finite-rank-projection"
  (statement := /-- $P$ is a finite-rank orthogonal projection. -/)
  (hasProof := false)] OperatorRidgelet.IsFiniteRankProjection

/-! ## Section 6: sampling bounds -/

attribute [blueprint "thm:general-rademacher"
  (statement := /-- Whenever the atoms $x\mapsto h(\theta)\beta(\langle a,x\rangle+c)$ are
    measurable and integrably bounded in $C(K)$, the sampled network satisfies
    $\mathbb E\|f_N-f\|_{C(K)}\le2V\,\mathfrak R_N(K;p,\beta)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_general_rademacher

attribute [blueprint "thm:lipschitz-barron-i"
  (statement := /-- For real globally Lipschitz $\beta$ and
    $M_2^2=\int(\|a\|^2+|c|^2)\,\mathrm dp<\infty$,
    $\mathbb E\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)$
    with $R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_lipschitz_barron_i

attribute [blueprint "thm:lipschitz-barron-ii"
  (statement := /-- At least one deterministic width-$N$ realization satisfies the same
    bound. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_lipschitz_barron_ii

/-! ## Section 6: finite variation from the spectral density -/

attribute [blueprint "thm:E-i"
  (statement := /-- For a band-pass $\rho$ there is a constant $c_\rho<\infty$, depending only
    on $\rho$ and $\alpha$, such that every $G$ regular along rays satisfies
    $\int(1+\|a\|^2+|c|^2)|\gamma_G|\,\mathrm d\lambda_\alpha\le c_\rho M_4(G)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_E_i

attribute [blueprint "thm:E-ii"
  (statement := /-- For $G$ regular along rays,
    $\int(1+\|a\|^2+|c|^2)|\gamma_G|\,\mathrm d\lambda_\alpha<\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_E_ii

attribute [blueprint "thm:E-iii"
  (statement := /-- For every real globally Lipschitz non-polynomial $\beta$,
    $C^{(\alpha)}_{\beta,\rho}g_G=S_\beta[\gamma_G\lambda_\alpha]$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_E_iii

attribute [blueprint "thm:E-iv"
  (statement := /-- The sampled network of $\gamma_G\lambda_\alpha$, with
    $V=\|\gamma_G\|_{L^1(\lambda_\alpha)}$ and $M_2$ the second moment of
    $|\gamma_G|\lambda_\alpha/V$, satisfies
    $\mathbb E\|f_N-C^{(\alpha)}_{\beta,\rho}g_G\|_{C(K)}
    \le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)$
    for every compact $K$. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_E_iv

/-! ## Section 6: constructive universal approximation -/

attribute [blueprint "thm:D"
  (statement := /-- For continuous, polynomially growing, non-polynomial real $\beta$, a
    band-pass $\rho$ with $C^{(\alpha)}_{\beta,\rho}=1$, continuous $f:H\to\mathbb C$, compact
    $K$, and $\varepsilon>0$, there is a spectral density $G$, regular along rays, smooth, and
    vanishing outside a bounded set, with (i) $\|f-g_G\|_{C(K)}<\varepsilon$; (ii)
    $g_G=S_\beta[\gamma_G\lambda_\alpha]$ with a finite coefficient measure with finite moments
    of all orders; (iii) for globally Lipschitz $\beta$,
    $\mathbb E\|f-f_N\|_{C(K)}\le\varepsilon+\frac{8V}{\sqrt N}
    (|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)$, and one deterministic width-$N$ network
    satisfies the same bound. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_D

attribute [blueprint "thm:D-dense"
  (statement := /-- The finite-width networks with activation $\beta$ are dense in $C(H)$ for
    the compact-open topology. -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_D_dense

attribute [blueprint "thm:D-vec"
  (statement := /-- The same statements hold for continuous $f:H\to Y$ with $C(K;Y)$ in (i)
    and (ii) and the vector-valued compact-open rate
    $\mathbb E\|f-f_N\|_{C(K;Y)}\le\varepsilon+2V\mathfrak R^Y_N(K;p,\beta)$ in (iii). -/)
  (notReady := true)] OperatorRidgelet.Paper.thm_D_vec

/-! ## Section 6: vector-valued sampling -/

attribute [blueprint "cor:vector-rates-i-a"
  (statement := /-- For every Borel probability measure $\zeta$ on $H$ with
    $\int\|x\|^2\,\mathrm d\zeta<\infty$,
    $\mathbb E\|f_N-f\|^2_{L^2(\zeta;Y)}\le\frac{V^2}N\int
    \|\beta(\langle a,\cdot\rangle+c)\|^2_{L^2(\zeta)}\,\mathrm dp$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_vector_rates_i_a

attribute [blueprint "cor:vector-rates-i-b"
  (statement := /-- $\frac{V^2}N\int\|\beta(\langle a,\cdot\rangle+c)\|^2_{L^2(\zeta)}\,
    \mathrm dp\le\frac{2V^2}N\bigl(|\beta(0)|^2+\operatorname{Lip}(\beta)^2
    (1+\int\|x\|^2\,\mathrm d\zeta)M_2^2\bigr)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_vector_rates_i_b

attribute [blueprint "cor:vector-rates-ii-a"
  (statement := /-- For every compact $K$,
    $\mathbb E\|f_N-f\|_{C(K;Y)}\le2V\,\mathfrak R^Y_N(K;p,\beta)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_vector_rates_ii_a

attribute [blueprint "cor:vector-rates-ii-b"
  (statement := /-- $\mathfrak R^Y_N(K;p,\beta)\to0$ as $N\to\infty$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_vector_rates_ii_b

/-! ## Appendix D: supplementary sampling results -/

attribute [blueprint "lem:qualitative-sampling"
  (statement := /-- For continuous $\beta$, compact $K$, and
    $\int\|\beta(\langle a,\cdot\rangle+c)\|_{C(K)}\,\mathrm d|\Gamma|<\infty$, for every
    $\varepsilon>0$ there is a finite atomic complex measure $\Gamma_\varepsilon$ with
    $\|S_\beta\Gamma_\varepsilon-S_\beta\Gamma\|_{C(K)}<\varepsilon$. -/)
  (notReady := true)] OperatorRidgelet.Paper.lem_qualitative_sampling

attribute [blueprint "cor:sampling-concentration"
  (statement := /-- Under the hypotheses of the Barron bound, if $\|a\|^2+|c|^2\le B^2$ almost
    surely and $M_K=|\beta(0)|+\operatorname{Lip}(\beta)R_KB$, then with probability at least
    $1-\delta$, $\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)
    R_KM_2)+VM_K\sqrt{2\log(1/\delta)/N}$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_sampling_concentration

attribute [blueprint "lem:hilbert-sampling-i"
  (statement := /-- For $Y\in L^2(p;X)$ with values in a separable Hilbert space, independent
    copies $Y_j$, $f=V\mathbb EY$, and $f_N=VN^{-1}\sum_jY_j$,
    $\mathbb E\|f_N-f\|_X^2=\frac{V^2}N(\mathbb E\|Y\|_X^2-\|\mathbb EY\|_X^2)$. -/)]
  OperatorRidgelet.Paper.lem_hilbert_sampling_i

attribute [blueprint "lem:hilbert-sampling-ii"
  (statement := /-- $\mathbb E\|f_N-f\|_X^2\le\frac{V^2}N\mathbb E\|Y\|_X^2$. -/)]
  OperatorRidgelet.Paper.lem_hilbert_sampling_ii

attribute [blueprint "lem:hilbert-sampling-iii"
  (statement := /-- A deterministic sample satisfies the same upper bound. -/)]
  OperatorRidgelet.Paper.lem_hilbert_sampling_iii

attribute [blueprint "cor:operator-sampling-i"
  (statement := /-- For a finite complex measure $\Gamma_{\rm op}$ on $\mathcal L_2(H)\times H$
    with polar decomposition $h_{\rm op}|\Gamma_{\rm op}|$, real globally Lipschitz $\beta$, and
    $M_{\rm op}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,\mathrm dp_{\rm op}<\infty$,
    sampling $(A_j,b_j)$ from $p_{\rm op}$ with the weights $h_{\rm op}$ gives
    $\mathbb E\|f_{{\rm op},N}-S_{\rm op}\Gamma_{\rm op}\|_{C(K)}
    \le8V_{\rm op}N^{-1/2}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_{\rm op})$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_operator_sampling_i

attribute [blueprint "cor:operator-sampling-ii"
  (statement := /-- $M_{\rm op}^2\le\|\psi\|^2\int(\|A\|_{\mathcal L_2}^2+\|b\|^2)\,
    \mathrm dp_{\rm op}$. -/)]
  OperatorRidgelet.Paper.cor_operator_sampling_ii

attribute [blueprint "cor:two-stage-error-i"
  (statement := /-- For finite-rank orthogonal projections $\Pi_m$ converging strongly to the
    identity, $f\in C(H)$, and compact $K$, $\|f-f\circ\Pi_m\|_{C(K)}\to0$. -/)]
  OperatorRidgelet.Paper.cor_two_stage_error_i

attribute [blueprint "cor:two-stage-error-ii"
  (statement := /-- If $f=S_\beta\Gamma$ satisfies the hypotheses of the Barron bound and the
    same samples are used with directions $\Pi_ma_j$, then
    $\mathbb E\|f-f_{m,N}\|_{C(K)}\le\operatorname{Lip}(\beta)\bigl(\int\|a\|\,\mathrm d|\Gamma|
    \bigr)\sup_K\|x-\Pi_mx\|+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)$. -/)
  (notReady := true)] OperatorRidgelet.Paper.cor_two_stage_error_ii
