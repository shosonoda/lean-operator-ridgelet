/-! Historical annotations. -/

attribute [blueprint "sampling:sampled-operator-network"
  (statement := /-- The sampled operator network
    $f_{{\rm op},N}(x)=\frac VN\sum_jh_{\rm op}(A_j,b_j)\,\mathrm n_{\ell,A_j,b_j}(x)$. -/)
  (hasProof := false)] OperatorRidgelet.sampledOperatorNetwork

attribute [blueprint "sampling:operator-second-moment"
  (statement := /-- $M_{\rm op}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,
    \mathrm dp_{\rm op}$. -/)
  (hasProof := false)] OperatorRidgelet.operatorSecondMoment

attribute [blueprint "cor:D.7-i"
  (statement := /-- For a finite complex measure $\Gamma_{\rm op}$ on $\mathcal L_2(H)\times H$
    with polar decomposition $h_{\rm op}|\Gamma_{\rm op}|$, real globally Lipschitz $\beta$, and
    $M_{\rm op}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,\mathrm dp_{\rm op}<\infty$,
    sampling $(A_j,b_j)$ from $p_{\rm op}$ with the weights $h_{\rm op}$ gives
    $\mathbb E\|f_{{\rm op},N}-S_{\rm op}\Gamma_{\rm op}\|_{C(K)}
    \le8V_{\rm op}N^{-1/2}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_{\rm op})$. -/)]
  OperatorRidgelet.Paper.cor_D_7_i

attribute [blueprint "cor:D.7-ii"
  (statement := /-- $M_{\rm op}^2\le\|\psi\|^2\int(\|A\|_{\mathcal L_2}^2+\|b\|^2)\,
    \mathrm dp_{\rm op}$. -/)]
  OperatorRidgelet.Paper.cor_D_7_ii
