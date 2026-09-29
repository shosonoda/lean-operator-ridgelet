import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.BasisIndependence
import OperatorRidgelet.Paper.Examples
import OperatorRidgelet.Paper.Networks
import OperatorRidgelet.Paper.Reconstruction
import OperatorRidgelet.Paper.Revision
import OperatorRidgelet.Paper.Sampling
import OperatorRidgelet.Paper.SamplingRevision
import OperatorRidgelet.Paper.Sobolev
import OperatorRidgelet.Paper.Tempered
import OperatorRidgelet.Paper.Transform
import OperatorRidgelet.ToMathlib.VectorMeasureRadonNikodym
import OperatorRidgelet.Transform.Infra

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Approximation by finite-width networks" =>
%%%
file := "sampling"
%%%

Monte Carlo approximation converts a finite coefficient measure into a finite-width network.
The first
estimate uses an activation-dependent Rademacher complexity. For a globally Lipschitz
activation, a separate contraction argument gives an explicit dimension-free
$`N^{-1/2}` rate. Regularity of a spectral density supplies the total variation and
parameter moments needed to apply these estimates.

Universality proceeds through targets with a spectral density. It does not provide a
uniform width–accuracy relation for all continuous targets: the coefficient moments may
depend on the chosen spectral approximation. Appendix D contains the proofs and supplementary
approximation results.

# Approximation rates

:::definition "aux:sampling-data" (lean := "OperatorRidgelet.compactRadius, OperatorRidgelet.densityWeight, OperatorRidgelet.densityLaw, OperatorRidgelet.densityPhase, OperatorRidgelet.polarSampledNetwork, OperatorRidgelet.densitySampledNetwork, OperatorRidgelet.secondMoment, OperatorRidgelet.atomicMeasure, OperatorRidgelet.IsFiniteRankProjection") (uses := "def:6.1")
The radius $`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}` of a compact set, the second moment
$`M_2^2=\int_{H\times\mathbb R}(\|a\|^2+|c|^2)\,p(\mathrm da,\mathrm dc)`, the polar data
$`V=\|\gamma\|_{L^1(\lambda)}`, $`p=|\gamma|\lambda/V`, $`h=\gamma/|\gamma|` of a coefficient
measure $`\gamma\lambda` and the sampled networks of $`\Gamma` and of $`\gamma\lambda`, the
finite atomic measure $`\sum_jw_j\delta_{\theta_j}`, and finite-rank orthogonal projections.
:::

:::definition "def:6.1" (lean := "OperatorRidgelet.compactSupNorm, OperatorRidgelet.polarDensity, OperatorRidgelet.polarWeight, OperatorRidgelet.polarLaw, OperatorRidgelet.sampleLaw, OperatorRidgelet.rademacherMeasure, OperatorRidgelet.sampledNetwork, OperatorRidgelet.rademacherComplexity") (uses := "def:2.1, def:2.2")
For a compact $`K\subset H`, the activation-dependent Rademacher complexity is
$`\mathfrak R_N(K;p,\beta)=\mathbb E_{\theta,\varepsilon}\sup_{x\in K}\bigl|\frac1N\sum_{j=1}^N\varepsilon_jh(\theta_j)\beta(\langle a_j,x\rangle+c_j)\bigr|`,
where $`\varepsilon_j` are independent Rademacher signs; with $`Y`-valued phases $`h` it is
$`\mathfrak R_N^Y(K;p,\beta)`. The Lean definition carries the polar data $`h`, $`V`, $`p` of
$`\Gamma`, the product law $`p^{\otimes N}` of the sample, the law of the signs, the sampled
network, and the compact sup norm $`\|f\|_{C(K)}=\sup_{x\in K}\|f(x)\|`.
:::

:::theorem "thm:6.2" (lean := "OperatorRidgelet.Paper.thm_6_2") (uses := "def:6.1, def:2.2")
Whenever the atoms $`x\mapsto h(\theta)\beta(\langle a,x\rangle+c)` are strongly measurable
and integrable as $`C(K)`-valued functions, the sampled network satisfies
$`\mathbb E\|f_N-f\|_{C(K)}\le2V\,\mathfrak R_N(K;p,\beta)`.
:::

:::proof "thm:6.2" (uses := "roadmap:polar-decomposition, lem:D.1")
Apply {bpref "lem:D.1"}[] in $`C(K)` and multiply by $`V`.
The same lemma gives convergence to zero. This step needs only Bochner integrability.
:::

:::theorem "thm:6.3" (lean := "OperatorRidgelet.Paper.thm_6_3_i, OperatorRidgelet.Paper.thm_6_3_ii, OperatorRidgelet.Paper.thm_6_3_iii") (uses := "aux:sampling-data")
Suppose $`\beta:\mathbb R\to\mathbb R` is globally Lipschitz, $`\Gamma` is a
finite-variation $`Y`-valued measure for a separable complex Hilbert space $`Y`, and
$`M_2^2=\int(\|a\|^2+|c|^2)\,\mathrm dp<\infty`. For compact $`K\subset H` with
$`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}`,
$`\mathbb E\|f_N-f\|_{C(K;Y)}\le\frac{V}{\sqrt N}\bigl(4|\beta(0)|
  +8\operatorname{Lip}(\beta)R_KM_2\bigr)`
(i), at least one deterministic width-$`N` realization satisfies the same bound (ii), and the
weaker bound $`\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)` follows
(iii). The scalar case is $`Y=\mathbb C`.
:::

See the [proof in Appendix D](appendix-d/D___1-Proof-of-Theorem-6___3/#--informal-preview-_FLQQ_thm___6___3_FLQQ_--proof).

# Finite variation from the spectral density

:::theorem "thm:6.4" (lean := "OperatorRidgelet.Paper.thm_6_4_i, OperatorRidgelet.Paper.thm_6_4_ii, OperatorRidgelet.Paper.thm_6_4_iii, OperatorRidgelet.Paper.thm_6_4_iv, OperatorRidgelet.Paper.thm_6_4_moments") (uses := "def:4.1, def:3.5, aux:tempered-activation, aux:sampling-data")
Let $`\rho` be a band-pass filter with frequency window $`I`, and let $`G` satisfy
{bpref "def:4.1"}[]. For every integer $`r\ge0` there is a finite constant $`c_{\rho,r}` such that
$`\int_{H\times\mathbb R}(1+\|a\|+|c|)^r\|\gamma_G(a,c)\|\,\mathrm d\lambda_\alpha\le c_{\rho,r}M_{r+2}(G)<\infty`.
The same constant works for every Hilbert output space $`Y`; it depends only on the filter
and the order. In particular,
$`\int(1+\|a\|^2+|c|^2)|\gamma_G(a,c)|\,\mathrm d\lambda_\alpha\le c_{\rho,2}M_4(G)<\infty`.
For every real globally Lipschitz $`\beta`, the target $`C_{\beta,\rho}^{(\alpha)}g_G` is
the integral network $`S_\beta[\gamma_G\lambda_\alpha]`. Its sampled network satisfies
$`\mathbb E\|f_N-C_{\beta,\rho}^{(\alpha)}g_G\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`
for every compact $`K`, where $`V=\|\gamma_G\|_{L^1}` and $`M_2` is computed under
$`|\gamma_G|\lambda_\alpha/V`. If $`V=0`, use the zero network.
:::

See the [proof in Appendix D](appendix-d/D___2-Proof-of-Theorem-6___4/#--informal-preview-_FLQQ_thm___6___4_FLQQ_--proof).

# Constructive universal approximation

:::theorem "thm:6.5" (lean := "OperatorRidgelet.Paper.thm_6_5, OperatorRidgelet.Paper.thm_6_5_dense, OperatorRidgelet.Paper.thm_6_5_vec") (uses := "def:2.1, def:4.1, aux:tempered-activation, thm:6.3")
Let $`\beta:\mathbb R\to\mathbb R` be continuous, of polynomial growth, and not a polynomial,
let $`\rho` be a band-pass filter with $`C_{\beta,\rho}^{(\alpha)}=1`, let $`f:H\to\mathbb C`
be continuous, $`K\subset H` compact, and $`\varepsilon>0`. The direction measure has full
support and is finite on bounded sets; these properties hold for $`\nu_\alpha` and are
required for general input and direction measures. Then there is a spectral density
$`G` satisfying {bpref "def:4.1"}[], smooth and vanishing outside a bounded set, such that (i)
$`\|f-g_G\|_{C(K)}<\varepsilon`; (ii) $`g_G=S_\beta[\gamma_G\lambda_\alpha]` is an integral
network whose coefficient measure is finite with finite moments of all orders; (iii) if
$`\beta` is globally Lipschitz, the sampled network $`f_N` of $`\gamma_G\lambda_\alpha`
satisfies
$`\mathbb E\|f-f_N\|_{C(K)}\le\varepsilon+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`,
and one deterministic width-$`N` network satisfies the same bound. In particular the
finite-width networks with activation $`\beta` are dense in $`C(H)` for the compact-open
topology, and the same statements hold for continuous $`f:H\to Y` with $`C(K;Y)` norms and the
same explicit rate in (iii), by the Hilbert-valued {bpref "thm:6.3"}[].
:::

See the [proof in Appendix D](appendix-d/D___3-Proof-of-Theorem-6___5/#--informal-preview-_FLQQ_thm___6___5_FLQQ_--proof).

# Vector-valued approximation

A vector coefficient measure has a polar density of norm one almost everywhere
with respect to its variation. This supplies the output weights in the sampled network.
The uniform estimate is expressed through a vector Rademacher average; Hilbert outputs
also admit the explicit contraction bound.

:::corollary "cor:6.6" (lean := "OperatorRidgelet.Paper.cor_6_6_i_a, OperatorRidgelet.Paper.cor_6_6_i_b, OperatorRidgelet.Paper.cor_6_6_ii_a, OperatorRidgelet.Paper.cor_6_6_ii_b, OperatorRidgelet.Paper.cor_6_6_i_exact") (uses := "def:6.1, aux:sampling-data")
Let $`\Gamma` be a $`Y`-valued measure of bounded variation with polar decomposition
$`\Gamma=h|\Gamma|`, let $`\beta` be real and globally Lipschitz, and let $`N\ge1`.
If $`V=0`, use the zero network; otherwise let $`p=|\Gamma|/V`.
(i) Assume the parameter second moment is finite. For every Borel probability measure
$`\zeta` with $`\int\|x\|^2\,\mathrm d\zeta<\infty`,
$`\mathbb E\|f_N-f\|_{L^2(\zeta;Y)}^2=\frac1N\left(V^2\int\|\beta(\langle a,\cdot\rangle+c)\|_{L^2(\zeta)}^2\,\mathrm dp-\|f\|_{L^2(\zeta;Y)}^2\right)`.
Consequently this is at most
$`\frac{V^2}N\int\|\beta(\langle a,\cdot\rangle+c)\|_{L^2(\zeta)}^2\,\mathrm dp\le\frac{2V^2}N\left(|\beta(0)|^2+\operatorname{Lip}(\beta)^2(1+\int\|x\|^2\,\mathrm d\zeta)M_2^2\right)`.
(ii) Only the first moment $`\int(\|a\|+|c|)\,\mathrm dp<\infty` is needed for
$`\mathbb E\|f_N-f\|_{C(K;Y)}\le2V\,\mathfrak R_N^Y(K;p,\beta)` on compact $`K`,
and for $`\mathfrak R_N^Y(K;p,\beta)\to0`.
:::

:::proof "cor:6.6" (uses := "lem:D.6, thm:6.2, lem:D.1")
Apply {bpref "lem:D.6"}[] in $`L^2(\zeta;Y)` to obtain the exact variance.
The polar phase has norm one almost everywhere. The elementary bounds
$`|\beta(u)|^2\le2|\beta(0)|^2+2\operatorname{Lip}(\beta)^2u^2` and
$`u^2\le(\|a\|^2+c^2)(\|x\|^2+1)` give the second-moment estimate.
For (ii), the compact atom map is continuous before composition with the measurable polar
phase, hence strongly measurable. Its norm is bounded by
$`|\beta(0)|+\operatorname{Lip}(\beta)R_K\sqrt{\|a\|^2+c^2}`, which is integrable under
the first-moment hypothesis. Apply {bpref "lem:D.1"}[] in $`C(K;Y)`.
:::
