import Architect
import OperatorRidgelet.Paper.Sobolev

/-! # Weak Sobolev tools metadata -/

attribute [blueprint "lem:sobolev-tools-i"
  (statement := /-- For $0\le r<s-1/2$, $\int\langle t\rangle^r\|\check h(t)\|\,\mathrm
    dt\le A_{s,r}\|h\|_{H^s_\omega}$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_tools_i

attribute [blueprint "lem:sobolev-tools-ii"
  (statement := /-- Reflection $Rh(\omega)=h(-\omega)$ is an isometry of $H^s_\omega$, with
    coefficient $\check h(-\cdot)$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_tools_ii

attribute [blueprint "lem:sobolev-tools-iii"
  (statement := /-- Modulation satisfies $\|M_uh\|_{H^s_\omega}\le(1+|u|)^s\|h\|_{H^s_\omega}$,
    with coefficient $\check h(\cdot+u)$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_tools_iii

attribute [blueprint "lem:sobolev-tools-iv"
  (statement := /-- The map $(u,h)\mapsto M_uh$ is jointly continuous. -/)]
  OperatorRidgelet.Paper.lem_sobolev_tools_iv

attribute [blueprint "lem:sobolev-pairing-i"
  (statement := /-- For continuous $\sigma$ of polynomial growth $p$ and $s>p+1/2$, the weighted
    activation $\langle\cdot\rangle^{-s}\sigma$ is square integrable, so
    $b_{\sigma,s}<\infty$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_pairing_i

attribute [blueprint "lem:sobolev-pairing-ii"
  (statement := /-- The pairing converges absolutely and
    $\|L_\sigma^Y(h)\|\le(2\pi)^{-1/2}b_{\sigma,s}\|h\|_{H^s_\omega}$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_pairing_ii

attribute [blueprint "lem:sobolev-pairing-iii"
  (statement := /-- $\int\sigma(u-b)\gamma(b)\,\mathrm db=L_\sigma^Y(M_uh)$. -/)]
  OperatorRidgelet.Paper.lem_sobolev_pairing_iii

attribute [blueprint "thm:weak-sobolev-synthesis-i"
  (statement := /-- For $0\le r<s-1/2$, $\int(1+\|a\|+|b|)^r\|\gamma_g(a,b)\|\,\mathrm
    d\nu\,\mathrm db\le2^{r/2}A_{s,r}\mathfrak B_s(\rho,g)$. -/)]
  OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_i

attribute [blueprint "thm:weak-sobolev-synthesis-ii"
  (statement := /-- The coefficient measure $\Gamma_g=\gamma_g(\nu\otimes\mathrm db)$ is
    finite. -/)]
  OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_ii

attribute [blueprint "thm:weak-sobolev-synthesis-iii"
  (statement := /-- $S_\sigma[\Gamma_g](x)=C^{(\alpha)}_{\sigma,\rho}f_g(x)$, with the cross
    constant given by the Sobolev pairing. -/)]
  OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_iii

attribute [blueprint "thm:weak-sobolev-synthesis-iv"
  (statement := /-- The synthesis integrand has one integrable majorant on each ball of
    inputs. -/)]
  OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_iv

attribute [blueprint "thm:weak-sobolev-synthesis-v"
  (statement := /-- The synthesis is continuous. -/)]
  OperatorRidgelet.Paper.thm_weak_sobolev_synthesis_v

attribute [blueprint "prop:nonbandpass-sobolev-i"
  (statement := /-- The Gaussian-derivative filter is a real Schwartz function with
    $\widehat\rho_k(\omega)=\omega^{2k}e^{-\omega^2}$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_i

attribute [blueprint "prop:nonbandpass-sobolev-ii"
  (statement := /-- The filter is not band pass. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_ii

attribute [blueprint "prop:nonbandpass-sobolev-iii"
  (statement := /-- The filter is $\alpha$-admissible for $\alpha<4k+1$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_iii

attribute [blueprint "prop:nonbandpass-sobolev-iv"
  (statement := /-- $\int(1+\|a\|^2)^{-d/2}\,\mathrm d\nu<\infty$ whenever $d>\alpha$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_iv

attribute [blueprint "prop:nonbandpass-sobolev-v"
  (statement := /-- The coefficient of the rays is jointly strongly measurable. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_v

attribute [blueprint "prop:nonbandpass-sobolev-vi"
  (statement := /-- Each ray lies in $H^s_\omega$ and has the profile
    $\widehat\rho_k(-\omega)g(\omega a)$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_vi

attribute [blueprint "prop:nonbandpass-sobolev-vii"
  (statement := /-- $\mathfrak B_s(\rho_k,g)<\infty$ when $2k>\alpha+2s-1/2$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_vii

attribute [blueprint "prop:nonbandpass-sobolev-viii"
  (statement := /-- $q_{\alpha,\rho_k}\in H^s_\omega$ in the same range. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_viii

attribute [blueprint "prop:nonbandpass-sobolev-ix"
  (statement := /-- The synthesis identity of {bpref "thm:weak-sobolev-synthesis"} holds for this
    filter and every continuous activation of growth order $p<s-1/2$. -/)]
  OperatorRidgelet.Paper.prop_nonbandpass_sobolev_ix
