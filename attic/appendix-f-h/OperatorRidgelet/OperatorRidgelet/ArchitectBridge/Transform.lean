/-! Historical annotations. -/

attribute [blueprint "thm:H.1-plancherel-memLp"
  (statement := /-- For the abstract pair $(\mu,\nu)$, $R_\rho f\in L^2(\lambda)$ for
    $f\in\mathcal D_{\mu,\nu}$. -/)]
  OperatorRidgelet.Paper.thm_H_1_plancherel_memLp

attribute [blueprint "thm:H.1-plancherel"
  (statement := /-- For the abstract pair, $\langle
    R_{\rho_1}f,R_{\rho_2}g\rangle_{L^2(\lambda)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle
    f,g\rangle_{\mathcal E_{\mu,\nu}}$. -/)]
  OperatorRidgelet.Paper.thm_H_1_plancherel

attribute [blueprint "thm:H.1-extension"
  (statement := /-- For the abstract pair, $R_\rho$ has a unique bounded extension $\mathcal
    E_{\mu,\nu}\to L^2(\lambda)$. -/)]
  OperatorRidgelet.Paper.thm_H_1_extension

attribute [blueprint "thm:H.1-extension-norm"
  (statement := /-- For the abstract pair, $\|R_\rho f\|^2=C^{(\alpha)}_\rho\|f\|_{\mathcal
    E_{\mu,\nu}}^2$. -/)]
  OperatorRidgelet.Paper.thm_H_1_extension_norm

attribute [blueprint "thm:H.1-extension-closed-range"
  (statement := /-- For the abstract pair, the range of $R_\rho$ is closed. -/)]
  OperatorRidgelet.Paper.thm_H_1_extension_closed_range

attribute [blueprint "thm:H.1-extension-coefficient"
  (statement := /-- For the abstract pair, $R_\rho=W_\rho U$. -/)]
  OperatorRidgelet.Paper.thm_H_1_extension_coefficient

attribute [blueprint "thm:H.1-injective"
  (statement := /-- For the abstract pair, $R_\rho f=0$ $\lambda$-a.e. implies $f=0$ $\mu$-a.e. -/)]
  OperatorRidgelet.Paper.thm_H_1_injective

attribute [blueprint "thm:H.1-one-mem-iff"
  (statement := /-- $1\in\mathcal D_{\mu,\nu}$ if and only if
    $\int_H|\widehat\mu(\xi)|^2\,\nu(\mathrm d\xi)<\infty$. -/)]
  OperatorRidgelet.Paper.thm_H_1_one_mem_iff
