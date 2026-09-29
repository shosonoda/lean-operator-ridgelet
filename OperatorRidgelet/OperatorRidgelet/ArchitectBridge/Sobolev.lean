import Architect
import OperatorRidgelet.Paper.Sobolev

/-! # Sobolev tools metadata

For Hilbert-valued profiles, `H^s_ω` denotes the Bessel potential space. For general Banach
values, the notation refers to the weighted `L²` norm of a specified inverse Fourier
transform, as defined in `Sobolev.Defs`; no Banach-valued Plancherel identity is used.
-/

attribute [blueprint "lem:C.3-i"
  (statement := /-- For $0\le r<s-1/2$, $\int\langle t\rangle^r\|\check h(t)\|\,\mathrm
    dt\le A_{s,r}\|h\|_{H^s_\omega}$. -/)]
  OperatorRidgelet.Paper.lem_C_3_i

attribute [blueprint "lem:C.3-ii"
  (statement := /-- Reflection $Rh(\omega)=h(-\omega)$ is an isometry of $H^s_\omega$, with
    coefficient $\check h(-\cdot)$. -/)]
  OperatorRidgelet.Paper.lem_C_3_ii

attribute [blueprint "lem:C.3-iii"
  (statement := /-- Modulation satisfies $\|M_uh\|_{H^s_\omega}\le(1+|u|)^s\|h\|_{H^s_\omega}$,
    with coefficient $\check h(\cdot+u)$. -/)]
  OperatorRidgelet.Paper.lem_C_3_iii

attribute [blueprint "lem:C.3-iv"
  (statement := /-- The map $(u,h)\mapsto M_uh$ is jointly continuous. -/)]
  OperatorRidgelet.Paper.lem_C_3_iv

attribute [blueprint "lem:C.4-i"
  (statement := /-- For continuous $\sigma$ of polynomial growth $p$ and $s>p+1/2$, the weighted
    activation $\langle\cdot\rangle^{-s}\sigma$ is square integrable, so
    $b_{\sigma,s}<\infty$. -/)]
  OperatorRidgelet.Paper.lem_C_4_i

attribute [blueprint "lem:C.4-ii"
  (statement := /-- The pairing converges absolutely and
    $\|L_\sigma^Y(h)\|\le(2\pi)^{-1/2}b_{\sigma,s}\|h\|_{H^s_\omega}$. -/)]
  OperatorRidgelet.Paper.lem_C_4_ii

attribute [blueprint "lem:C.4-iii"
  (statement := /-- $\int\sigma(u-b)\gamma(b)\,\mathrm db=L_\sigma^Y(M_uh)$. -/)]
  OperatorRidgelet.Paper.lem_C_4_iii

attribute [blueprint "thm:5.6-i"
  (statement := /-- For $0\le r<s-1/2$, $\int(1+\|a\|+|b|)^r\|\gamma_g(a,b)\|\,\mathrm
    d\nu\,\mathrm db\le2^{r/2}A_{s,r}\mathfrak B_s(\rho,g)$. -/)]
  OperatorRidgelet.Paper.thm_5_6_i

attribute [blueprint "thm:5.6-ii"
  (statement := /-- The coefficient measure $\Gamma_g=\gamma_g(\nu\otimes\mathrm db)$ is
    finite. -/)]
  OperatorRidgelet.Paper.thm_5_6_ii

attribute [blueprint "thm:5.6-iii"
  (statement := /-- $S_\sigma[\Gamma_g](x)=C^{(\alpha)}_{\sigma,\rho}f_g(x)$, with the cross
    constant given by the Sobolev pairing. -/)]
  OperatorRidgelet.Paper.thm_5_6_iii

attribute [blueprint "thm:5.6-iv"
  (statement := /-- The synthesis integrand has one integrable majorant on each ball of
    inputs. -/)]
  OperatorRidgelet.Paper.thm_5_6_iv

attribute [blueprint "thm:5.6-v"
  (statement := /-- The synthesis is continuous. -/)]
  OperatorRidgelet.Paper.thm_5_6_v

attribute [blueprint "prop:I.3-i"
  (statement := /-- The Gaussian-derivative filter is a real Schwartz function with
    $\widehat\rho_k(\omega)=\omega^{2k}e^{-\omega^2}$. -/)]
  OperatorRidgelet.Paper.prop_I_3_i

attribute [blueprint "prop:I.3-ii"
  (statement := /-- The filter is not band pass. -/)]
  OperatorRidgelet.Paper.prop_I_3_ii

attribute [blueprint "prop:I.3-iii"
  (statement := /-- The filter is $\alpha$-admissible for $\alpha<4k+1$. -/)]
  OperatorRidgelet.Paper.prop_I_3_iii

attribute [blueprint "prop:I.3-iv"
  (statement := /-- $\int(1+\|a\|^2)^{-d/2}\,\mathrm d\nu<\infty$ whenever $d>\alpha$. -/)]
  OperatorRidgelet.Paper.prop_I_3_iv

attribute [blueprint "prop:I.3-v"
  (statement := /-- The coefficient is jointly strongly measurable. -/)]
  OperatorRidgelet.Paper.prop_I_3_v

attribute [blueprint "prop:I.3-vi"
  (statement := /-- Each frequency profile lies in $H^s_\omega$ and equals
    $\widehat\rho_k(-\omega)g(\omega a)$. -/)]
  OperatorRidgelet.Paper.prop_I_3_vi

attribute [blueprint "prop:I.3-vii"
  (statement := /-- $\mathfrak B_s(\rho_k,g)<\infty$ when $2k>\alpha+2s-1/2$. -/)]
  OperatorRidgelet.Paper.prop_I_3_vii

attribute [blueprint "prop:I.3-viii"
  (statement := /-- $q_{\alpha,\rho_k}\in H^s_\omega$ in the same range. -/)]
  OperatorRidgelet.Paper.prop_I_3_viii

attribute [blueprint "prop:I.3-ix"
  (statement := /-- The synthesis identity of {bpref "thm:5.6"} holds for this
    filter and every continuous activation of growth order $p<s-1/2$. -/)]
  OperatorRidgelet.Paper.prop_I_3_ix
