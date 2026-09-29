import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Transform
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

#doc (Manual) "Appendix A. Gaussian measures and proofs for Section 3" =>
%%%
file := "appendix-a"
number := false
%%%

This appendix constructs the Gaussian scale mixture and proves the analytic statements
used in Section 3. The partial Fourier transform is treated first, followed by the Gaussian
series, mixture integration, the Plancherel proof and injectivity. The regularized
characteristic functional at the end is not an absolutely convergent integral against the
infinite mixture measure.

:::lemma_ "lem:A.1" (lean := "OperatorRidgelet.Paper.lem_A_1, OperatorRidgelet.Paper.lem_A_1_uniqueness") (uses := "aux:conventions")
For a separable complex Hilbert space $`Y`, partial Fourier transformation in the bias is a
unitary map from $`L^2(\nu\otimes\mathrm dc;Y)` onto
$`L^2(\nu\otimes\mathrm d\omega/(2\pi);Y)`. Each transform admits a jointly strongly
measurable representative agreeing with the one-dimensional Plancherel transform of
$`c\mapsto\gamma(a,c)` for almost every $`a`. Such representatives agree almost everywhere.
:::

:::proof "lem:A.1"
Apply the one-dimensional Fourier unitary to the fibers of the product $`L^2` space. Its
inverse on the fibers proves surjectivity; the product $`L^2` identification supplies joint
measurability. Fiberwise uniqueness and Fubini prove independence of the representative.
:::

# A.1 The Gaussian series and the mixture
%%%
number := false
%%%

If $`P e_j=p_j e_j` with $`\sum_j p_j<\infty`, independent standard Gaussians
give the convergent series $`X=\sum_j\sqrt{p_j}Z_j e_j`. The scaled random variables
$`\sqrt{2s}X` realize the mixture components on one probability space. Joint
measurability in $`s` and the sample variable justifies the mixture integral.

:::lemma_ "lem:A.2" (lean := "OperatorRidgelet.Paper.lem_A_2_i, OperatorRidgelet.Paper.lem_A_2_ii, OperatorRidgelet.Paper.lem_A_2_iii, OperatorRidgelet.Paper.lem_A_2_iv") (uses := "aux:gaussian-mixture")
For every Borel set $`E`, the map $`s\mapsto\mathcal N(0,2sP)(E)` is Borel measurable (i), and
the mixture defines a countably additive Borel measure with
$`\nu_\alpha(E)=\int_0^\infty\mathcal N(0,2sP)(E)\,s^{\alpha/2-1}\,\mathrm ds` (ii). For every
nonnegative Borel $`F`,
$`\int_HF\,\mathrm d\nu_\alpha=\int_0^\infty\int_HF\,\mathrm d\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds`
(iii), and the identity holds for complex $`F` with $`\int_H|F|\,\mathrm d\nu_\alpha<\infty`
(iv).
:::

:::proof "lem:A.2"
$`\mathcal N(0,2sP)(E)=\int\mathbf 1_E(\sqrt{2s}\,x)\,\mathcal N(0,P)(\mathrm dx)` with a
jointly Borel integrand; monotone convergence gives countable additivity and extends the
integral identity from indicators to nonnegative Borel functions.
:::

# A.2 Proof of Lemma 3.1
%%%
number := false
%%%

We prove {bpref "lem:3.1"}[].

:::proof "lem:3.1" (uses := "lem:A.2")
Coordinate small-ball estimates of order $`s^{-k/2}` with $`k>\alpha` give finite mass on
bounded sets, the part $`s\le1` is integrable because $`s^{\alpha/2-1}` is, balls exhaust
$`H` while $`\nu_\alpha(H)=\int_0^\infty s^{\alpha/2-1}\mathrm ds=\infty`, injectivity of
$`P` gives full support, and the substitution $`u=s\omega^2` in each component proves homogeneity.
:::

# A.3 Proof of Lemma 3.9
%%%
number := false
%%%

We prove {bpref "lem:3.9"}[].

:::proof "lem:3.9" (uses := "lem:A.2")
On each Gaussian component, Cauchy–Schwarz separates the polynomial factor, whose moments are
finite, from the Gaussian factor, whose integral is $`\prod_j(1+8st\theta_j)^{-1/2}` with
$`\theta_j>0` the eigenvalues of $`P^{1/2}QP^{1/2}`; retaining $`k>4m+2\alpha` factors makes
the mixture integral finite.
:::

# A.4 Proof of Theorem 3.11(i) and (ii)
%%%
number := false
%%%

We prove {bpref "thm:3.11"}[].

:::proof "thm:3.11" (uses := "lem:3.4, lem:3.1, lem:B.1, lem:3.8, thm:H.1")
Apply the one-dimensional Plancherel identity in the bias to the Fourier-slice identity and
substitute $`\xi=-\omega a` by homogeneity; admissibility gives square integrability and
Cauchy–Schwarz justifies the cross identity. The norm identity extends $`R_\rho` to the
completion, an isometry up to a nonzero scalar has closed range, and
$`R_\rho=W_\rho U_\alpha` holds on the core and extends by continuity. For (iii), a fixed
frequency with $`\widehat\rho\ne0` and homogeneity give $`\mathcal G_Qf=0` almost everywhere,
and the argument of {bpref "lem:3.8"}[] finishes.
:::

# A.5 Proof of Theorem 3.11(iii)
%%%
number := false
%%%

The injectivity argument in the preceding proof does not need finite-dimensional
reduction. If $`R_\rho f=0`, choose a nonzero frequency where the continuous Fourier
transform of the filter does not vanish. The slice identity and homogeneity imply
$`F_Qf=0` almost everywhere for the direction measure. Continuity of $`F_Qf` and full
support make it zero everywhere. Fourier uniqueness for the finite measure $`f\mu_Q`
then gives $`f=0` almost everywhere for the input measure.

# A.6 The regularized characteristic functional of the mixture
%%%
number := false
%%%

:::lemma_ "lem:A.3" (lean := "OperatorRidgelet.Paper.lem_A_3_i, OperatorRidgelet.Paper.lem_A_3_ii, OperatorRidgelet.Paper.lem_A_3_iii, OperatorRidgelet.Paper.lem_A_3_iv") (uses := "aux:gaussian-mixture")
For $`z\ne0` put $`q=\langle Pz,z\rangle>0` (i) and
$`\nu_\alpha^{\varepsilon,M}=\int_\varepsilon^M\mathcal N(0,2sP)s^{\alpha/2-1}\mathrm ds`.
Then $`\lim_{\varepsilon\downarrow0,M\uparrow\infty}\int_He^{i\langle z,\xi\rangle}\,\nu_\alpha^{\varepsilon,M}(\mathrm d\xi)=\Gamma(\alpha/2)q^{-\alpha/2}`
(ii), where $`\int_0^\infty e^{-sq}s^{\alpha/2-1}\mathrm ds=\Gamma(\alpha/2)q^{-\alpha/2}`
(iii). In contrast $`\int_H|e^{i\langle z,\xi\rangle}|\,\nu_\alpha(\mathrm d\xi)=\infty`
(iv), so the limit is not a Lebesgue integral against $`\nu_\alpha`.
:::

:::proof "lem:A.3" (uses := "lem:A.2, lem:3.1")
The truncated mixture is finite, so Fubini and the characteristic functional of
$`\mathcal N(0,2sP)` reduce the integral to
$`\int_\varepsilon^Me^{-sq}s^{\alpha/2-1}\mathrm ds`; monotone convergence and the
substitution $`u=sq` finish the proof.
:::
