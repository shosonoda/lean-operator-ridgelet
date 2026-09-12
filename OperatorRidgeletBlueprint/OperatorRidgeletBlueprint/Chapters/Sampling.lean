import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Paper.Sampling
import OperatorRidgelet.Paper.Reconstruction
import OperatorRidgelet.Paper.Revision
import OperatorRidgelet.Paper.SamplingRevision

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Approximation by finite-width networks" =>
%%%
file := "sampling"
%%%

This chapter is Section 6 of the manuscript together with Appendix D. Exact representation
uses a continuous parameter integral; finite width is obtained by sampling the coefficient
measure, with no projection of the input space or of the direction parameter. The sampling
bounds come first, then the coefficients produced by the spectral representation are shown to
satisfy their hypotheses, and both are combined with the density of targets with a spectral
density into the approximation theorem {bpref "thm:D"}[].

# Sampling bounds

Let $`\Gamma` be a finite complex measure on $`H\times\mathbb R` with polar decomposition
$`\Gamma=h|\Gamma|`, $`|h|=1` $`|\Gamma|`-almost everywhere. If $`\Gamma=0` take the zero
network; otherwise write $`V=\|\Gamma\|_{\mathrm{TV}}` and $`p=|\Gamma|/V`, sample independent
$`\theta_j=(a_j,c_j)\sim p`, and form the sampled network
$`f_N(x)=\frac VN\sum_{j=1}^Nh(\theta_j)\,\beta(\langle a_j,x\rangle+c_j)`, which is unbiased
for $`f=S_\beta[\Gamma]`.

:::definition "def:rademacher-complexity" (lean := "OperatorRidgelet.compactSupNorm, OperatorRidgelet.polarDensity, OperatorRidgelet.polarWeight, OperatorRidgelet.polarLaw, OperatorRidgelet.sampleLaw, OperatorRidgelet.rademacherMeasure, OperatorRidgelet.sampledNetwork, OperatorRidgelet.rademacherComplexity") (uses := "def:finite-network, def:integral-network")
For a compact $`K\subset H`, the activation-dependent Rademacher complexity is
$`\mathfrak R_N(K;p,\beta)=\mathbb E_{\theta,\varepsilon}\sup_{x\in K}\bigl|\frac1N\sum_{j=1}^N\varepsilon_jh(\theta_j)\beta(\langle a_j,x\rangle+c_j)\bigr|`,
where $`\varepsilon_j` are independent Rademacher signs; with $`Y`-valued phases $`h` it is
$`\mathfrak R_N^Y(K;p,\beta)`. The Lean definition carries the polar data $`h`, $`V`, $`p` of
$`\Gamma`, the product law $`p^{\otimes N}` of the sample, the law of the signs, the sampled
network, and the compact sup norm $`\|f\|_{C(K)}=\sup_{x\in K}\|f(x)\|`.
:::

:::definition "aux:sampling-data" (lean := "OperatorRidgelet.compactRadius, OperatorRidgelet.densityWeight, OperatorRidgelet.densityLaw, OperatorRidgelet.densityPhase, OperatorRidgelet.polarSampledNetwork, OperatorRidgelet.densitySampledNetwork, OperatorRidgelet.secondMoment, OperatorRidgelet.atomicMeasure, OperatorRidgelet.sampledOperatorNetwork, OperatorRidgelet.operatorSecondMoment, OperatorRidgelet.IsFiniteRankProjection") (uses := "def:rademacher-complexity, aux:operator-neuron")
The radius $`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}` of a compact set, the second moment
$`M_2^2=\int_{H\times\mathbb R}(\|a\|^2+|c|^2)\,p(\mathrm da,\mathrm dc)`, the polar data
$`V=\|\gamma\|_{L^1(\lambda)}`, $`p=|\gamma|\lambda/V`, $`h=\gamma/|\gamma|` of a coefficient
measure $`\gamma\lambda` and the sampled networks of $`\Gamma` and of $`\gamma\lambda`, the
finite atomic measure $`\sum_jw_j\delta_{\theta_j}`, the sampled operator network
$`f_{\mathrm{op},N}(x)=\frac VN\sum_jh_{\mathrm{op}}(A_j,b_j)\,\mathrm n_{\ell,A_j,b_j}(x)`
with $`M_{\mathrm{op}}^2=\int(\|A^*\psi\|^2+|\langle\psi,b\rangle|^2)\,\mathrm dp_{\mathrm{op}}`,
and finite-rank orthogonal projections.
:::

:::lemma_ "lem:banach-rademacher-vanishing" (lean := "OperatorRidgelet.Paper.lem_banach_rademacher_vanishing_i, OperatorRidgelet.Paper.lem_banach_rademacher_vanishing_ii") (uses := "def:rademacher-complexity")
Let $`X` be a separable Banach space, $`p` a probability measure, and $`\Phi\in L^1(p;X)`.
For independent samples $`\theta_j\sim p` and independent Rademacher signs $`\varepsilon_j`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X\to0`.
Moreover, for $`N\ge1` and $`m=\int\Phi\,\mathrm dp`,
$`\mathbb E\|N^{-1}\sum_{j=1}^N\Phi(\theta_j)-m\|_X\le2\mathbb E\|N^{-1}\sum_{j=1}^N\varepsilon_j\Phi(\theta_j)\|_X`.
:::

:::proof "lem:banach-rademacher-vanishing"
Approximate $`\Phi` in $`L^1` by a simple function
$`\Psi=\sum_{k=1}^Jx_k\mathbf1_{E_k}`. The signed-average error has expected norm at most
$`\|\Phi-\Psi\|_{L^1}`. For $`\Psi`, the scalar second-moment identity and Cauchy–Schwarz
bound the expected norm by $`\sum_k\|x_k\|\sqrt{p(E_k)/N}`, which tends to zero.
For symmetrization, introduce a ghost sample, apply Jensen, and insert independent signs
using exchangeability of each pair. The triangle inequality gives the factor two.
Bochner integrability justifies every expectation.
:::

:::theorem "thm:general-rademacher" (lean := "OperatorRidgelet.Paper.thm_general_rademacher") (uses := "def:rademacher-complexity, def:integral-network, roadmap:polar-decomposition, lem:banach-rademacher-vanishing")
Whenever the atoms $`x\mapsto h(\theta)\beta(\langle a,x\rangle+c)` are strongly measurable
and integrable as $`C(K)`-valued functions, the sampled network satisfies
$`\mathbb E\|f_N-f\|_{C(K)}\le2V\,\mathfrak R_N(K;p,\beta)`.
:::

:::proof "thm:general-rademacher"
Apply {bpref "lem:banach-rademacher-vanishing"}[] in $`C(K)` and multiply by $`V`.
The same lemma gives convergence to zero. This step needs only Bochner integrability.
:::

:::theorem "thm:lipschitz-barron" (lean := "OperatorRidgelet.Paper.thm_lipschitz_barron_i, OperatorRidgelet.Paper.thm_lipschitz_barron_ii") (uses := "thm:general-rademacher, aux:sampling-data, roadmap:contraction-principle")
Suppose $`\beta:\mathbb R\to\mathbb R` is globally Lipschitz and
$`M_2^2=\int(\|a\|^2+|c|^2)\,\mathrm dp<\infty`. For compact $`K\subset H` with
$`R_K=\sup_{x\in K}\sqrt{\|x\|^2+1}`,
$`\mathbb E\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}\bigl(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2\bigr)`
(i), and at least one deterministic width-$`N` realization satisfies the same bound (ii).
:::

:::proof "thm:lipschitz-barron"
Symmetrize, separate $`\beta(0)`, split the complex phases into real and imaginary parts, and
apply the real contraction principle; the remaining linear process is bounded by
$`R_K\|\sum_j\varepsilon_j(a_j,c_j)\|`, whose expectation is at most $`R_K\sqrt NM_2` by the
Hilbert-space Khintchine inequality. An integrable random variable cannot exceed its
expectation almost surely.
:::

:::lemma_ "lem:qualitative-sampling" (lean := "OperatorRidgelet.Paper.lem_qualitative_sampling") (uses := "def:integral-network, def:rademacher-complexity, aux:sampling-data")
Let $`\beta:\mathbb R\to\mathbb C` be continuous, $`K\subset H` compact, and
$`\int\|\beta(\langle a,\cdot\rangle+c)\|_{C(K)}\,\mathrm d|\Gamma|(a,c)<\infty`. Then for
every $`\varepsilon>0` there is a finite atomic complex measure $`\Gamma_\varepsilon` with
$`\|S_\beta\Gamma_\varepsilon-S_\beta\Gamma\|_{C(K)}<\varepsilon`.
:::

:::proof "lem:qualitative-sampling"
The atom map is continuous into the separable Banach space $`C(K)`, so
$`Y(a,c)=h(a,c)\beta(\langle a,\cdot\rangle+c)|_K` is Bochner integrable and its mean lies in
the closed convex hull of its essential range by Hahn–Banach separation; approximate the mean
by a finite convex combination of essential-range values.
:::

:::corollary "cor:sampling-concentration" (lean := "OperatorRidgelet.Paper.cor_sampling_concentration") (uses := "thm:lipschitz-barron, aux:sampling-data")
Under the hypotheses of {bpref "thm:lipschitz-barron"}[], suppose $`\|a\|^2+|c|^2\le B^2`
almost surely and put $`M_K=|\beta(0)|+\operatorname{Lip}(\beta)R_KB`. With probability at
least $`1-\delta`,
$`\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)+VM_K\sqrt{2\log(1/\delta)/N}`.
:::

:::proof "cor:sampling-concentration"
Each atom has norm at most $`M_K`, so replacing one sample changes $`\|f_N-f\|_{C(K)}` by at
most $`2VM_K/N`; the bounded-difference inequality bounds the excess over the expectation.
:::

:::lemma_ "lem:hilbert-sampling" (lean := "OperatorRidgelet.Paper.lem_hilbert_sampling_i, OperatorRidgelet.Paper.lem_hilbert_sampling_ii, OperatorRidgelet.Paper.lem_hilbert_sampling_iii") (uses := "def:rademacher-complexity")
Let $`X` be a separable Hilbert space and $`Y\in L^2(p;X)`. For independent copies $`Y_j`,
$`f=V\,\mathbb EY`, and $`f_N=VN^{-1}\sum_jY_j`,
$`\mathbb E\|f_N-f\|_X^2=\frac{V^2}N(\mathbb E\|Y\|_X^2-\|\mathbb EY\|_X^2)` (i), which is
at most $`\frac{V^2}N\mathbb E\|Y\|_X^2` (ii), and a deterministic sample satisfies the same
upper bound (iii).
:::

:::proof "lem:hilbert-sampling"
With $`Z_j=Y_j-\mathbb EY`, independence and zero means make
$`\mathbb E\langle Z_j,Z_k\rangle=0` for $`j\ne k`, so the expanded squared norm leaves
$`N\,\mathbb E\|Z_1\|^2`.
:::

:::corollary "cor:operator-sampling" (lean := "OperatorRidgelet.Paper.cor_operator_sampling_i, OperatorRidgelet.Paper.cor_operator_sampling_ii") (uses := "thm:lipschitz-barron, aux:sampling-data, lem:measure-transport")
Let $`\Gamma_{\mathrm{op}}` be a finite complex measure on $`\mathcal L_2(H)\times H` with
polar decomposition $`h_{\mathrm{op}}|\Gamma_{\mathrm{op}}|`, $`V_{\mathrm{op}}>0`,
$`p_{\mathrm{op}}=|\Gamma_{\mathrm{op}}|/V_{\mathrm{op}}`, let $`\beta` be real and globally
Lipschitz, and assume $`M_{\mathrm{op}}^2<\infty`. Sampling $`(A_j,b_j)` from
$`p_{\mathrm{op}}` with the weights $`h_{\mathrm{op}}` gives
$`\mathbb E\|f_{\mathrm{op},N}-S_{\mathrm{op}}\Gamma_{\mathrm{op}}\|_{C(K)}\le8V_{\mathrm{op}}N^{-1/2}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_{\mathrm{op}})`
(i), and $`M_{\mathrm{op}}^2\le\|\psi\|^2\int(\|A\|_{\mathcal L_2}^2+\|b\|^2)\,\mathrm dp_{\mathrm{op}}`
(ii).
:::

:::proof "cor:operator-sampling"
The atom is the scalar ridge with parameter $`\pi_\psi(A,b)`, so the proof of
{bpref "thm:lipschitz-barron"}[] applies on the operator probability space with $`M_2`
replaced by $`M_{\mathrm{op}}`; Cauchy–Schwarz and $`\|A\|_{\mathrm{op}}\le\|A\|_{\mathcal L_2}`
give the last estimate.
:::

:::corollary "cor:two-stage-error" (lean := "OperatorRidgelet.Paper.cor_two_stage_error_i, OperatorRidgelet.Paper.cor_two_stage_error_ii") (uses := "thm:lipschitz-barron, aux:sampling-data")
Let $`\Pi_m` be finite-rank orthogonal projections converging strongly to the identity. For
$`f\in C(H)` and compact $`K`, $`\|f-f\circ\Pi_m\|_{C(K)}\to0` (i). If $`f=S_\beta\Gamma`
satisfies the hypotheses of {bpref "thm:lipschitz-barron"}[] and the same samples are used
with directions $`\Pi_ma_j`, then
$`\mathbb E\|f-f_{m,N}\|_{C(K)}\le\operatorname{Lip}(\beta)\bigl(\int\|a\|\,\mathrm d|\Gamma|\bigr)\sup_K\|x-\Pi_mx\|+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`
(ii).
:::

:::proof "cor:two-stage-error"
A finite-net argument gives $`\sup_K\|x-\Pi_mx\|\to0`, and uniform convergence of
$`f\circ\Pi_m` on $`K` follows by compactness and continuity of $`f`; the triangle inequality
separates truncation from sampling, and projecting directions does not increase their second
moment.
:::

# Finite variation from the spectral density

:::theorem "thm:E" (lean := "OperatorRidgelet.Paper.thm_E_i, OperatorRidgelet.Paper.thm_E_ii, OperatorRidgelet.Paper.thm_E_iii, OperatorRidgelet.Paper.thm_E_iv, OperatorRidgelet.Paper.thm_E_moments") (uses := "def:ray-regular, def:spectral-coefficient, lem:coefficient-finite-order, aux:tempered-activation, aux:sampling-data, thm:A, thm:lipschitz-barron, lem:homogeneous-mixture")
Let $`\rho` be a band-pass filter with frequency window $`I`, and let $`G` be regular along
rays. For every integer $`r\ge0` there is a finite constant $`c_{\rho,r}` such that
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

:::proof "thm:E"
Apply {bpref "lem:coefficient-finite-order"}[] and $`A_{r+2,r}(G)\le M_{r+2}(G)`.
The coefficient decays as $`(1+|c|)^{-r-2}`; two powers give an integrable bias weight and
the other $`r` powers control the parameter moment. The scalar constant is independent of $`Y`.
Use $`1+\|a\|^2+|c|^2\le(1+\|a\|+|c|)^2` for the second moment, then
{bpref "thm:A"}[] (iii) and {bpref "thm:lipschitz-barron"}[] for synthesis and sampling.
:::

:::lemma_ "lem:ray-regular-examples" (lean := "OperatorRidgelet.Paper.lem_ray_regular_examples_a, OperatorRidgelet.Paper.lem_ray_regular_examples_b_i, OperatorRidgelet.Paper.lem_ray_regular_examples_b_ii, OperatorRidgelet.Paper.lem_ray_regular_examples_c_i, OperatorRidgelet.Paper.lem_ray_regular_examples_c_ii") (uses := "def:ray-regular, lem:gaussian-decay, lem:homogeneous-mixture")
The following functions are regular along rays for every band-pass $`\rho`.
(a) $`G(\xi)=q(\xi)e^{-\kappa(\xi)/2}`, where $`\kappa(\xi)=\langle S\xi,\xi\rangle`,
$`S` is bounded and positive, $`S\ge\theta Q` for some $`\theta>0`, and $`q` is a
polynomial in $`\kappa` and finitely many bounded linear functionals $`\ell_i` satisfying
$`|\ell_i(\xi)|^2\le C_i\kappa(\xi)` for every $`\xi`. Equivalently,
$`\ell_i=\langle S^{1/2}v_i,\cdot\rangle` for some $`v_i\in H`. A polynomial in
$`\kappa` alone requires no further condition.
(b) $`G(\xi)=\varphi(\|\xi-\xi_0\|^2)` for $`\varphi\in C_c^\infty(\mathbb R)`;
more generally, bounded densities smooth along rays, with bounded support and
$`\sup_{\omega\in I}|\partial_\omega^kG(\omega a)|\le C_k(1+\|a\|)^{p_k}` for every $`k`.
(c) Finite linear combinations, and Bochner integrals $`G=\int_\Omega G_y\,m(\mathrm dy)`
of uniformly bounded measurable families over a finite measure, subject to these
neighbourhood bounds: there is an open $`U\supset I` where every ray of every $`G_y` is
smooth, and finite-valued Borel $`h_k:H\to[0,\infty)` such that
$`\sup_{\omega\in U}|\partial_\omega^kG_y(\omega a)|\le h_k(a)` for every $`y,a,k`, and
$`\int_H(1+\|a\|)^{m+2}\max_{k\le m}h_k(a)\,\nu_\alpha(\mathrm da)<\infty` for every $`m`.
The bounds hold on the open neighbourhood and for every direction.
:::

:::proof "lem:ray-regular-examples"
For (a), domination of the linear functionals gives $`|q(\xi)|\le C(1+\kappa(\xi))^p`,
so $`G` is bounded. Ray derivatives are polynomials times $`e^{-\omega^2\kappa(a)/2}`;
on $`I\subset\{r\le|\omega|\le R\}` their bound is
$`C_k(1+\|a\|)^{p_k}e^{-r^2\theta\langle Qa,a\rangle/2}`. Apply
{bpref "lem:gaussian-decay"}[]. For (b), derivatives vanish outside a bounded set of
directions, on which $`\nu_\alpha` is finite. For (c), the finite neighbourhood bounds
justify differentiation under the Bochner integral for each direction. The triangle
inequality and Tonelli give
$`M_m(G)\le m(\Omega)\int_H(1+\|a\|)^{m+2}\max_{k\le m}h_k(a)\,\nu_\alpha(\mathrm da)<\infty`.
:::

# Constructive universal approximation

:::theorem "thm:D" (lean := "OperatorRidgelet.Paper.thm_D, OperatorRidgelet.Paper.thm_D_dense, OperatorRidgelet.Paper.thm_D_vec") (uses := "def:finite-network, def:ray-regular, aux:tempered-activation, thm:tempered-reconstruction, lem:ray-regular-examples, thm:A, thm:E, thm:lipschitz-barron, lem:qualitative-sampling, cor:vector-rates, thm:vector-valued")
Let $`\beta:\mathbb R\to\mathbb R` be continuous, of polynomial growth, and not a polynomial,
let $`\rho` be a band-pass filter with $`C_{\beta,\rho}^{(\alpha)}=1`, let $`f:H\to\mathbb C`
be continuous, $`K\subset H` compact, and $`\varepsilon>0`. The direction measure has full
support and is finite on bounded sets; these properties hold for $`\nu_\alpha` and are
required in the abstract-weight version. Then there is a spectral density
$`G`, regular along rays, smooth, and vanishing outside a bounded set, such that (i)
$`\|f-g_G\|_{C(K)}<\varepsilon`; (ii) $`g_G=S_\beta[\gamma_G\lambda_\alpha]` is an integral
network whose coefficient measure is finite with finite moments of all orders; (iii) if
$`\beta` is globally Lipschitz, the sampled network $`f_N` of $`\gamma_G\lambda_\alpha`
satisfies
$`\mathbb E\|f-f_N\|_{C(K)}\le\varepsilon+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`,
and one deterministic width-$`N` network satisfies the same bound. In particular the
finite-width networks with activation $`\beta` are dense in $`C(H)` for the compact-open
topology, and the same statements hold for continuous $`f:H\to Y` with the vector-valued rate
of {bpref "cor:vector-rates"}[] (ii) in (iii).
:::

:::proof "thm:D"
Finite sums of characters $`e^{i\langle x,\xi\rangle}` form a self-conjugate algebra
containing the constants and separating points, so Stone–Weierstrass gives a trigonometric
approximant on $`K`; each character is within $`r_K\delta` of $`g_{G_j}` for a normalized
smooth bump $`G_j` supported in the ball of radius $`\delta` around $`\xi_j`. Full support
makes its normalizing integral positive, and finiteness on bounded sets makes it finite. The sum $`G=\sum_jw_jG_j` is regular along rays by
{bpref "lem:ray-regular-examples"}[], and {bpref "thm:A"}[] (iii), {bpref "thm:E"}[], and
{bpref "thm:lipschitz-barron"}[] give (ii) and (iii); the vector-valued case uses a partition
of unity and {bpref "thm:vector-valued"}[].
:::

# Vector-valued sampling

:::corollary "cor:vector-rates" (lean := "OperatorRidgelet.Paper.cor_vector_rates_i_a, OperatorRidgelet.Paper.cor_vector_rates_i_b, OperatorRidgelet.Paper.cor_vector_rates_ii_a, OperatorRidgelet.Paper.cor_vector_rates_ii_b, OperatorRidgelet.Paper.cor_vector_rates_i_exact") (uses := "def:rademacher-complexity, aux:sampling-data, lem:hilbert-sampling, thm:general-rademacher, lem:banach-rademacher-vanishing")
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

:::proof "cor:vector-rates"
Apply {bpref "lem:hilbert-sampling"}[] in $`L^2(\zeta;Y)` to obtain the exact variance.
The polar phase has norm one almost everywhere. The elementary bounds
$`|\beta(u)|^2\le2|\beta(0)|^2+2\operatorname{Lip}(\beta)^2u^2` and
$`u^2\le(\|a\|^2+c^2)(\|x\|^2+1)` give the second-moment estimate.
For (ii), the compact atom map is continuous before composition with the measurable polar
phase, hence strongly measurable. Its norm is bounded by
$`|\beta(0)|+\operatorname{Lip}(\beta)R_K\sqrt{\|a\|^2+c^2}`, which is integrable under
the first-moment hypothesis. Apply {bpref "lem:banach-rademacher-vanishing"}[] in $`C(K;Y)`.
:::
