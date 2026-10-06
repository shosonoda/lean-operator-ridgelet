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

Monte Carlo approximation turns a finite coefficient measure into a finite-width network. The Banach-valued Rademacher lemma precedes the general bound; a two-coordinate comparison then gives the dimension-free Lipschitz rate. We prove spectral moments and qualitative discretization before compact-open universality. The final subsection gives the Hilbert variance and vector rates. Appendix C records additional concentration and input-truncation consequences.

# Rademacher complexity and the general approximation bound

For a finite coefficient measure with $`V=\|\Gamma\|_{\mathrm{TV}}>0`, choose its polar decomposition $`\Gamma=h|\Gamma|`, where $`\|h\|_Y=1` almost everywhere, and put $`p=|\Gamma|/V`. Draw neuron parameters independently from $`p`; the polar density supplies the output weights. For $`V=0`, use the zero network.

:::definition "def:6.1" (lean := "OperatorRidgelet.compactSupNorm, OperatorRidgelet.polarDensity, OperatorRidgelet.polarWeight, OperatorRidgelet.polarLaw, OperatorRidgelet.sampleLaw, OperatorRidgelet.rademacherMeasure, OperatorRidgelet.sampledNetwork, OperatorRidgelet.rademacherComplexity") (uses := "def:2.1, def:2.2, roadmap:polar-decomposition")
For a compact $`K\subset H`, the activation-dependent Rademacher complexity is
$`\mathfrak R_N(K;p,\beta)=\mathbb E_{\theta,\varepsilon}\sup_{x\in K}\bigl|\frac1N\sum_{j=1}^N\varepsilon_jh(\theta_j)\beta(\langle a_j,x\rangle+c_j)\bigr|`,
where $`\varepsilon_j` are independent Rademacher signs; with $`Y`-valued phases $`h` it is
$`\mathfrak R_N^Y(K;p,\beta)`. The Lean definition carries the polar data $`h`, $`V`, $`p` of
$`\Gamma`, the product law $`p^{\otimes N}` of the sample, the law of the signs, the sampled
network, and the compact sup norm $`\|f\|_{C(K)}=\sup_{x\in K}\|f(x)\|`.
:::

:::definition "aux:sampling-data" (lean := "OperatorRidgelet.compactRadius, OperatorRidgelet.densityWeight, OperatorRidgelet.densityLaw, OperatorRidgelet.densityPhase, OperatorRidgelet.polarSampledNetwork, OperatorRidgelet.densitySampledNetwork, OperatorRidgelet.secondMoment, OperatorRidgelet.atomicMeasure, OperatorRidgelet.IsFiniteRankProjection") (uses := "def:6.1")
These are the sampling definitions used across Section 6: polar data in Section 6.1,
radius and moment bounds in Theorem 6.5, atomic measures in Lemma 6.7,
and finite-rank projections in Corollary C.2.

The radius $`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}` of a compact set, the second moment
$`M_2^2=\int_{H\times\mathbb R}(\|a\|^2+|c|^2)\,p(\mathrm da,\mathrm dc)`, the polar data
$`V=\|\gamma\|_{L^1(\lambda)}`, $`p=|\gamma|\lambda/V`, $`h=\gamma/|\gamma|` of a coefficient
measure $`\gamma\lambda` and the sampled networks of $`\Gamma` and of $`\gamma\lambda`, the
finite atomic measure $`\sum_jw_j\delta_{\theta_j}`, and finite-rank orthogonal projections.
:::

:::lemma_ "lem:6.2" (lean := "OperatorRidgelet.Paper.lem_6_2_i, OperatorRidgelet.Paper.lem_6_2_ii") (uses := "def:6.1")
Let $`X` be a separable Banach space, $`p` a probability measure, and $`\Phi\in L^1(p;X)`.
For independent samples $`\theta_j\sim p` and independent Rademacher signs $`\varepsilon_j`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X\to0`.
Moreover, for $`N\ge1` and $`m=\int\Phi\,\mathrm dp`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\Phi(\theta_j)-m\|_X\le2\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X`.
:::

:::proof "lem:6.2"
Approximate $`\Phi` in $`L^1` by a simple function
$`\Psi=\sum_{k=1}^Jx_k\mathbf1_{E_k}`. The signed-average error has expected norm at most
$`\|\Phi-\Psi\|_{L^1}`. For $`\Psi`, the scalar second-moment identity and Cauchy–Schwarz
bound the expected norm by $`\sum_k\|x_k\|\sqrt{p(E_k)/N}`, which tends to zero.
For symmetrization, introduce a ghost sample, apply Jensen, and insert independent signs
using exchangeability of each pair. The triangle inequality gives the factor two.
Bochner integrability justifies every expectation.
:::

:::theorem "thm:6.3" (lean := "OperatorRidgelet.Paper.thm_6_3") (uses := "def:6.1, def:2.2")
Whenever the atoms $`x\mapsto h(\theta)\beta(\langle a,x\rangle+c)` are strongly measurable
and integrable as $`C(K)`-valued functions, the sampled network satisfies
$`\mathbb E\|f_N-f\|_{C(K)}\le2V\,\mathfrak R_N(K;p,\beta)`.
:::

:::proof "thm:6.3" (uses := "lem:6.2")
Apply {bpref "lem:6.2"}[] in $`C(K)` and multiply by $`V`.
The same lemma gives convergence to zero. This step needs only Bochner integrability.
:::

# Explicit Lipschitz approximation rate

:::lemma_ "lem:6.4" (lean := "OperatorRidgelet.Paper.lem_6_4") (uses := "def:6.1")
Let $`S` be a nonempty set and let $`\psi_i,u_i,v_i:S\to\mathbb R` be bounded with
$`|\psi_i(s)-\psi_i(t)|\le|u_i(s)-u_i(t)|+|v_i(s)-v_i(t)|` for all $`s,t`. Then
$`\mathbb E\sup_s\sum_i\varepsilon_i\psi_i(s)
  \le2\mathbb E\sup_s\sum_i(\varepsilon_{i1}u_i(s)+\varepsilon_{i2}v_i(s))`
for independent Rademacher signs.
:::

:::proof "lem:6.4"
Fix all signs but $`\varepsilon_i`. Choosing near-maximizers $`s_\pm` of $`F\pm\psi_i` and
using $`\mathbb E|A+D|\ge\mathbb E|D|` for a symmetric $`D`, together with
$`\mathbb E|\eta_1r+\eta_2q|=\max\{|r|,|q|\}\ge(|r|+|q|)/2`, gives the one-sign comparison
with an arbitrary bounded offset $`F`. Replacing one coordinate at a time and averaging over
the remaining signs proves the statement.
:::

:::theorem "thm:6.5" (lean := "OperatorRidgelet.Paper.thm_6_5_i, OperatorRidgelet.Paper.thm_6_5_ii, OperatorRidgelet.Paper.thm_6_5_iii") (uses := "aux:sampling-data")
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

:::proof "thm:6.5" (uses := "thm:6.3, lem:6.4")
Write the output norm as a supremum of real inner products over the unit ball of $`Y`, so that
the signed process is indexed by $`K\times B_Y`. The increments of
$`\psi_j(x,y)=\beta(\langle a_j,x\rangle+c_j)\langle y,h_j\rangle` are dominated by those
of $`\operatorname{Lip}(\beta)(\langle a_j,x\rangle+c_j)` and of
$`B_j\langle y,h_j\rangle` with $`B_j=|\beta(0)|+\operatorname{Lip}(\beta)R_K\|(a_j,c_j)\|`,
so {bpref "lem:6.4"}[] applies. Hilbert duality and the Khintchine
inequality bound the two resulting averages by
$`\operatorname{Lip}(\beta)R_K(\sum_j\|(a_j,c_j)\|^2)^{1/2}` and
$`(\sum_jB_j^2)^{1/2}`, and symmetrization and Jensen's inequality give (i). An integrable
random variable cannot exceed its expectation almost surely, which gives (ii).
:::

# Finite variation and moments from a spectral density

:::theorem "thm:6.6" (lean := "OperatorRidgelet.Paper.thm_6_6_i, OperatorRidgelet.Paper.thm_6_6_ii, OperatorRidgelet.Paper.thm_6_6_iii, OperatorRidgelet.Paper.thm_6_6_iv, OperatorRidgelet.Paper.thm_6_6_moments") (uses := "def:4.2, def:3.7, aux:tempered-activation, aux:sampling-data")
Let $`\rho` be a band-pass filter with frequency window $`I`, and let $`G` satisfy
{bpref "def:4.2"}[]. For every integer $`r\ge0` there is a finite constant $`c_{\rho,r}` such that
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

:::proof "thm:6.6" (uses := "lem:4.3, thm:4.5, thm:6.5, lem:3.2")
Apply {bpref "lem:4.3"}[] and $`A_{r+2,r}(G)\le M_{r+2}(G)`.
The coefficient decays as $`(1+|c|)^{-r-2}`; two powers give an integrable bias weight and
the other $`r` powers control the parameter moment. The scalar constant is independent of $`Y`.
Use $`1+\|a\|^2+|c|^2\le(1+\|a\|+|c|)^2` for the second moment, then
{bpref "thm:4.5"}[] (iii) and {bpref "thm:6.5"}[] for synthesis and sampling.
:::

# Constructive universal approximation

:::lemma_ "lem:6.7" (lean := "OperatorRidgelet.Paper.lem_6_7") (uses := "def:2.2, def:6.1, aux:sampling-data")
Let $`\beta:\mathbb R\to\mathbb C` be continuous, $`K\subset H` compact, and
$`\int\|\beta(\langle a,\cdot\rangle+c)\|_{C(K)}\,\mathrm d|\Gamma|(a,c)<\infty`. Then for
every $`\varepsilon>0` there is a finite atomic complex measure $`\Gamma_\varepsilon` with
$`\|S_\beta\Gamma_\varepsilon-S_\beta\Gamma\|_{C(K)}<\varepsilon`.
:::

:::proof "lem:6.7"
The atom map is continuous into the separable Banach space $`C(K)`, so
$`Y(a,c)=h(a,c)\beta(\langle a,\cdot\rangle+c)|_K` is Bochner integrable and its mean lies in
the closed convex hull of its essential range by Hahn–Banach separation; approximate the mean
by a finite convex combination of essential-range values.
:::

:::theorem "thm:6.8" (lean := "OperatorRidgelet.Paper.thm_6_8, OperatorRidgelet.Paper.thm_6_8_dense, OperatorRidgelet.Paper.thm_6_8_vec") (uses := "def:2.1, def:4.2, aux:tempered-activation, thm:6.5")
Let $`\beta:\mathbb R\to\mathbb R` be continuous, of polynomial growth, and not a polynomial,
let $`\rho` be a band-pass filter with $`C_{\beta,\rho}^{(\alpha)}=1`, let $`f:H\to\mathbb C`
be continuous, $`K\subset H` compact, and $`\varepsilon>0`. The direction measure has full
support and is finite on bounded sets; these properties hold for $`\nu_\alpha` and are
required for general input and direction measures. Then there is a spectral density
$`G` satisfying {bpref "def:4.2"}[], smooth and vanishing outside a bounded set, such that (i)
$`\|f-g_G\|_{C(K)}<\varepsilon`; (ii) $`g_G=S_\beta[\gamma_G\lambda_\alpha]` is an integral
network whose coefficient measure is finite with finite moments of all orders; (iii) if
$`\beta` is globally Lipschitz, the sampled network $`f_N` of $`\gamma_G\lambda_\alpha`
satisfies
$`\mathbb E\|f-f_N\|_{C(K)}\le\varepsilon+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`,
and one deterministic width-$`N` network satisfies the same bound. In particular the
finite-width networks with activation $`\beta` are dense in $`C(H)` for the compact-open
topology, and the same statements hold for continuous $`f:H\to Y` with $`C(K;Y)` norms and the
same explicit rate in (iii), by the Hilbert-valued {bpref "thm:6.5"}[].
:::

:::proof "thm:6.8" (uses := "thm:5.4, lem:4.4, thm:4.5, thm:6.6, lem:6.7, thm:4.11")
Finite sums of characters $`e^{i\langle x,\xi\rangle}` form a self-conjugate algebra
containing the constants and separating points, so Stone–Weierstrass gives a trigonometric
approximant on $`K`; each character is within $`r_K\delta` of $`g_{G_j}` for a normalized
smooth bump $`G_j` supported in the ball of radius $`\delta` around $`\xi_j`. Full support
makes its normalizing integral positive, and finiteness on bounded sets makes it finite.
By {bpref "lem:4.4"}[], the sum $`G=\sum_jw_jG_j` satisfies
{bpref "def:4.2"}[]. Then {bpref "thm:4.5"}[] (iii), {bpref "thm:6.6"}[], and
{bpref "thm:6.5"}[] give (ii) and (iii); the vector-valued case uses a partition
of unity and {bpref "thm:4.11"}[].
:::

# Vector-valued approximation

:::lemma_ "lem:6.9" (lean := "OperatorRidgelet.Paper.lem_6_9_i, OperatorRidgelet.Paper.lem_6_9_ii, OperatorRidgelet.Paper.lem_6_9_iii") (uses := "def:6.1")
Let $`X` be a separable Hilbert space and $`Y\in L^2(p;X)`. For independent copies $`Y_j`,
$`f=V\,\mathbb EY`, and $`f_N=VN^{-1}\sum_jY_j`,
$`\mathbb E\|f_N-f\|_X^2=\frac{V^2}N(\mathbb E\|Y\|_X^2-\|\mathbb EY\|_X^2)` (i), which is
at most $`\frac{V^2}N\mathbb E\|Y\|_X^2` (ii), and a deterministic sample satisfies the same
upper bound (iii).
:::

:::proof "lem:6.9"
With $`Z_j=Y_j-\mathbb EY`, independence and zero means make
$`\mathbb E\langle Z_j,Z_k\rangle=0` for $`j\ne k`, so the expanded squared norm leaves
$`N\,\mathbb E\|Z_1\|^2`.
:::

:::corollary "cor:6.10" (lean := "OperatorRidgelet.Paper.cor_6_10_i_a, OperatorRidgelet.Paper.cor_6_10_i_b, OperatorRidgelet.Paper.cor_6_10_ii_a, OperatorRidgelet.Paper.cor_6_10_ii_b, OperatorRidgelet.Paper.cor_6_10_i_exact") (uses := "def:6.1, aux:sampling-data")
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

:::proof "cor:6.10" (uses := "lem:6.9, thm:6.3, lem:6.2")
Apply {bpref "lem:6.9"}[] in $`L^2(\zeta;Y)` to obtain the exact variance.
The polar phase has norm one almost everywhere. The elementary bounds
$`|\beta(u)|^2\le2|\beta(0)|^2+2\operatorname{Lip}(\beta)^2u^2` and
$`u^2\le(\|a\|^2+c^2)(\|x\|^2+1)` give the second-moment estimate.
For (ii), the compact atom map is continuous before composition with the measurable polar
phase, hence strongly measurable. Its norm is bounded by
$`|\beta(0)|+\operatorname{Lip}(\beta)R_K\sqrt{\|a\|^2+c^2}`, which is integrable under
the first-moment hypothesis. Apply {bpref "lem:6.2"}[] in $`C(K;Y)`.
:::
