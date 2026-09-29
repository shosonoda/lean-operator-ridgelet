:::corollary "cor:D.7" (lean := "OperatorRidgelet.Paper.cor_D_7_i, OperatorRidgelet.Paper.cor_D_7_ii") (uses := "aux:sampling-data")
Let $`\Gamma_{\mathrm{op}}` be a finite complex measure on $`\mathcal L_2(H)\times H` with
polar decomposition $`h_{\mathrm{op}}|\Gamma_{\mathrm{op}}|`, $`V_{\mathrm{op}}>0`,
$`p_{\mathrm{op}}=|\Gamma_{\mathrm{op}}|/V_{\mathrm{op}}`, let $`\beta` be real and globally
Lipschitz, and assume $`M_{\mathrm{op}}^2<\infty`. Sampling $`(A_j,b_j)` from
$`p_{\mathrm{op}}` with the weights $`h_{\mathrm{op}}` gives
$`\mathbb E\|f_{\mathrm{op},N}-S_{\mathrm{op}}\Gamma_{\mathrm{op}}\|_{C(K)}\le8V_{\mathrm{op}}N^{-1/2}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_{\mathrm{op}})`
(i), and $`M_{\mathrm{op}}^2\le\|\psi\|^2\int(\|A\|_{\mathcal L_2}^2+\|b\|^2)\,\mathrm dp_{\mathrm{op}}`
(ii).
:::

:::proof "cor:D.7" (uses := "thm:6.3, lem:F.4")
The atom is the scalar ridge with parameter $`\pi_\psi(A,b)`, so the proof of
{bpref "thm:6.3"}[] applies on the operator probability space with $`M_2`
replaced by $`M_{\mathrm{op}}`; Cauchy–Schwarz and $`\|A\|_{\mathrm{op}}\le\|A\|_{\mathcal L_2}`
give the last estimate.
:::
