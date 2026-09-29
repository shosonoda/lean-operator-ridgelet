:::definition "aux:sampling-data" (lean := "OperatorRidgelet.compactRadius, OperatorRidgelet.densityWeight, OperatorRidgelet.densityLaw, OperatorRidgelet.densityPhase, OperatorRidgelet.polarSampledNetwork, OperatorRidgelet.densitySampledNetwork, OperatorRidgelet.secondMoment, OperatorRidgelet.atomicMeasure, OperatorRidgelet.sampledOperatorNetwork, OperatorRidgelet.operatorSecondMoment, OperatorRidgelet.IsFiniteRankProjection") (uses := "def:6.1, aux:operator-neuron")
The radius $`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}` of a compact set, the second moment
$`M_2^2=\int_{H\times\mathbb R}(\|a\|^2+|c|^2)\,p(\mathrm da,\mathrm dc)`, the polar data
$`V=\|\gamma\|_{L^1(\lambda)}`, $`p=|\gamma|\lambda/V`, $`h=\gamma/|\gamma|` of a coefficient
measure $`\gamma\lambda` and the sampled networks of $`\Gamma` and of $`\gamma\lambda`, the
finite atomic measure $`\sum_jw_j\delta_{\theta_j}`, the sampled operator network
$`f_{\mathrm{op},N}(x)=\frac VN\sum_jh_{\mathrm{op}}(A_j,b_j)\,\mathrm n_{\ell,A_j,b_j}(x)`
with $`M_{\mathrm{op}}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,\mathrm dp_{\mathrm{op}}`,
and finite-rank orthogonal projections.
:::
