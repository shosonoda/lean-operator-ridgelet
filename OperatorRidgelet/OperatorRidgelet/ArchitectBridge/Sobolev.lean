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
