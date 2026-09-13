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
