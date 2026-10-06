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

#doc (Manual) "Representation and reconstruction" =>
%%%
file := "reconstruction"
%%%

There are two complementary reconstruction statements. A target with a spectral density
has an explicit integral-network coefficient. Analysis of a target in the Hilbert space
$`\mathcal E_\alpha` followed by synthesis gives $`C T_\alpha f`, where the frame operator
is the correction induced by the weights. It can be inverted after synthesis, before
analysis, or on the coefficients. The last subsection gives the Hilbert-valued extension.
The supporting coefficient estimates and detailed proofs are in Appendix B.

# Targets with a spectral density

For a density $`G\in L^1(\nu_\alpha)`, write
$`f_G(x)=\int_H G(\xi)e^{i\langle x,\xi\rangle}\,\nu_\alpha(\mathrm d\xi)`.
The coefficient is obtained by inverse Fourier transformation of
$`\rho^\sharp(\omega)G(-\omega a)` in the bias coordinate $`c=-b`.
Regularity along rays supplies decay in that coordinate.

:::definition "def:4.1" (lean := "OperatorRidgelet.IsFrequencyWindow, OperatorRidgelet.rayDerivBound, OperatorRidgelet.rayMoment, OperatorRidgelet.IsRegularAlongRays, OperatorRidgelet.spectralTarget, OperatorRidgelet.Paper.def_4_1") (uses := "def:3.2, aux:gaussian-mixture, lem:3.1")
Fix a symmetric compact set
$`I\subset\mathbb R\setminus\{0\}` containing $`\operatorname{supp}\rho^\sharp` (a frequency
window). Write $`G_a(\omega):=G(\omega a)`, the restriction to the line through the origin
spanned by $`a\ne0`, with $`G_0` constant. A bounded Borel $`G:H\to\mathbb C` is
regular along rays if every $`G_a` is $`C^\infty` on a neighbourhood of $`I` and
$`M_m(G)=\int_H(1+\|a\|)^{m+2}\max_{k\le m}\sup_{\omega\in I}|\partial_\omega^kG(\omega a)|\,\nu_\alpha(\mathrm da)<\infty`
for every integer $`m\ge0`. Such a $`G` belongs to $`L^1(\nu_\alpha)\cap L^2(\nu_\alpha)`
(the theorem part of the definition).
:::

:::definition "aux:tempered-activation" (lean := "OperatorRidgelet.IsTemperedFunction, OperatorRidgelet.temperedTestFilter, OperatorRidgelet.temperedAdmissibilityConst") (uses := "def:3.2, aux:conventions")
A tempered distribution $`\beta\in\mathcal S'(\mathbb R)` that is a continuous function of
polynomial growth is the pair of $`\beta` and a continuous $`b:\mathbb R\to\mathbb R` with
$`|b(t)|\le C(1+|t|)^p` and $`\langle\beta,\varphi\rangle=\int b\varphi`. For a band-pass
$`\rho` the test filter $`\omega\mapsto\rho^\sharp(-\omega)|\omega|^{-\alpha}` is a Schwartz
function, and the distributional admissibility constant is
$`C_{\beta,\rho}^{(\alpha)}=\frac1{2\pi}\langle\beta^\sharp,\rho^\sharp(-\,\cdot\,)|\cdot|^{-\alpha}\rangle`.
:::

:::theorem "thm:4.2" (lean := "OperatorRidgelet.Paper.thm_4_2_i_a, OperatorRidgelet.Paper.thm_4_2_i_b, OperatorRidgelet.Paper.thm_4_2_i_c, OperatorRidgelet.Paper.thm_4_2_ii_a, OperatorRidgelet.Paper.thm_4_2_ii_b, OperatorRidgelet.Paper.thm_4_2_ii_c, OperatorRidgelet.Paper.thm_4_2_iii_a, OperatorRidgelet.Paper.thm_4_2_iii_b, OperatorRidgelet.Paper.thm_4_2_iii_c, OperatorRidgelet.Paper.thm_4_2_iii_d, OperatorRidgelet.Paper.thm_4_2_iii_e") (uses := "def:4.1, aux:tempered-activation, def:3.5, def:2.2")
Let $`\alpha>0`. Part (ii) assumes an $`\alpha`-admissible Schwartz filter $`\rho`; part
(iii) assumes a band-pass filter. (i) For $`G\in L^1(\nu_\alpha)`, the function $`g_G` is
bounded with $`\|g_G\|_\infty\le\|G\|_{L^1(\nu_\alpha)}` and continuous,
and $`g_G=0` only if $`G=0` $`\nu_\alpha`-almost everywhere. (ii) For
$`G\in L^1(\nu_\alpha)\cap L^2(\nu_\alpha)` and every $`x`, the iterated integral
$`\int_H[\int_{\mathbb R}\gamma_G(a,c)\rho(\langle a,x\rangle+c)\,\mathrm dc]\,\nu_\alpha(\mathrm da)=(\!(\rho,\rho)\!)_\alpha g_G(x)`
converges absolutely, and if $`\gamma_G\in L^1(\lambda_\alpha)` its left side is the integral
network $`S_\rho[\gamma_G\lambda_\alpha](x)`. (iii) For a tempered $`\beta` that is a
continuous function of polynomial growth and $`G` satisfying {bpref "def:4.1"}[], the integrand
$`\gamma_G(a,c)\beta(\langle a,x\rangle+c)` is absolutely integrable on the product space.
Its integral is the ordinary network with finite coefficient measure $`\gamma_G\lambda_\alpha`
and equals $`C_{\beta,\rho}^{(\alpha)}g_G(x)`. This identity allows a zero constant.
Non-polynomiality is needed separately to choose a band-pass filter with a nonzero constant,
then normalize it for reconstruction or universality. A polynomial activation has zero
band-pass pairing.
:::

See the [proof in Appendix B](appendix-b/B___2-Proof-of-Theorem-4___2/#--informal-preview-_FLQQ_thm___4___2_FLQQ_--proof).

# The frame operator and the reconstruction formula

The Hilbert-space completion and its continuous anti-dual are distinct spaces.
The frame operator is the Riesz isomorphism between them, while the backprojection takes
coefficients to a frequency-domain density. Keeping these maps separate makes the
reconstruction and stability statements precise.

:::definition "aux:frame-operator" (lean := "OperatorRidgelet.SpectralAntiDual, OperatorRidgelet.antiDualConj, OperatorRidgelet.rieszMap, OperatorRidgelet.rieszInv, OperatorRidgelet.transposeEmbed, OperatorRidgelet.frameOperator, OperatorRidgelet.ridgeletExtension, OperatorRidgelet.ridgeletRange, OperatorRidgelet.synthesis") (uses := "def:3.7, thm:3.11")
Let $`\mathcal E_\alpha'` be the continuous anti-dual of $`\mathcal E_\alpha`, represented as
the continuous conjugate-linear functionals on $`\mathcal K_\alpha`. The Riesz map is
$`T_\alpha f[g]=\langle f,g\rangle_{\mathcal E_\alpha}`, with inverse $`T_\alpha^{-1}` from the
Riesz representation theorem; the transpose of $`F_Q` is
$`F_Q'F[g]=\langle F,F_Q g\rangle_{L^2(\nu_\alpha)}` for $`F\in L^2(\nu_\alpha)`, and
the frame operator is $`T_\alpha=F_Q'F_Q`. With $`R_\rho:\mathcal E_\alpha\to
L^2(\lambda_\alpha)` the bounded extension of {bpref "thm:3.11"}[] (ii) and
$`\operatorname{Ran}R_\rho` its range, synthesis with the analysis filter is the transpose
$`S_\rho=R_\rho'`, $`(S_\rho\gamma)[g]=\langle\gamma,R_\rho g\rangle_{L^2(\lambda_\alpha)}`.
Here $`F_Q':L^2(\nu_\alpha)\to\mathcal E_\alpha'` is formed from the
completed input space. The prime denotes transpose into the anti-dual,
while the star denotes the Hilbert adjoint. No adjoint into the ambient
$`L^2(\mu_Q)` is asserted. With $`C=(\!(\rho,\rho)\!)_\alpha`, the Plancherel identity gives
$`R_\rho^*R_\rho=C I_{\mathcal E_\alpha}` and
$`R_\rho'R_\rho=CT_\alpha`.
:::

:::definition "aux:backprojection" (lean := "OperatorRidgelet.backprojectionOf, OperatorRidgelet.backprojection, OperatorRidgelet.backprojectionLp, OperatorRidgelet.coefficientProjection") (uses := "def:3.5, def:3.7, lem:A.1, lem:3.6")
For $`\gamma\in L^2(\lambda_\alpha)`, define the backprojection as $`W_\rho^*`.
By {bpref "lem:3.6"}[], it is represented by the integral
$`W_\rho^*\gamma(\xi)=\frac1{2\pi}\int_{\mathbb R\setminus\{0\}}
    \overline{\rho^\sharp(\omega)}\,|\omega|^{-\alpha}\,\gamma^\sharp(-\xi/\omega,\omega)\,\mathrm d\omega`,
computed from any jointly strongly measurable partial Fourier representative supplied by
{bpref "lem:A.1"}[]. The integral converges absolutely for almost every
$`\xi`, and its $`L^2(\nu_\alpha)` class is independent of the representative. With $`P_{\mathcal K_\alpha}` the
orthogonal projection onto $`\mathcal K_\alpha`, the coefficient projection is
$`\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}W_\rho^*`.
:::

:::theorem "thm:4.3" (lean := "OperatorRidgelet.Paper.thm_4_3_i_a, OperatorRidgelet.Paper.thm_4_3_i_b, OperatorRidgelet.Paper.thm_4_3_i_c, OperatorRidgelet.Paper.thm_4_3_i_d, OperatorRidgelet.Paper.thm_4_3_ii_a, OperatorRidgelet.Paper.thm_4_3_ii_b, OperatorRidgelet.Paper.thm_4_3_iii_a, OperatorRidgelet.Paper.thm_4_3_iii_b, OperatorRidgelet.Paper.thm_4_3_iii_c, OperatorRidgelet.Paper.thm_4_3_iii_d, OperatorRidgelet.Paper.thm_4_3_iii_e, OperatorRidgelet.Paper.thm_4_3_iv_a, OperatorRidgelet.Paper.thm_4_3_iv_b, OperatorRidgelet.Paper.thm_4_3_iv_c, OperatorRidgelet.Paper.thm_4_3_iv_d, OperatorRidgelet.Paper.thm_4_3_iv_e, OperatorRidgelet.Paper.thm_4_3_iv_f, OperatorRidgelet.Paper.thm_4_3_iv_completion") (uses := "aux:frame-operator, aux:backprojection, aux:hermite, def:4.1")
Let $`\alpha>0` and let $`\rho` be an $`\alpha`-admissible Schwartz filter. (i) The frame operator
$`T_\alpha=F_Q'F_Q` is the Riesz map, an isometric bijection
$`\mathcal E_\alpha\to\mathcal E_\alpha'`, and $`S_\rho R_\rho f=(\!(\rho,\rho)\!)_\alpha T_\alpha f`
for $`f\in\mathcal E_\alpha`. (ii) For $`f\in\mathcal E_\alpha` and $`g\in\mathcal E_\alpha'`,
$`f=((\!(\rho,\rho)\!)_\alpha)^{-1}T_\alpha^{-1}S_\rho R_\rho f` and
$`g=((\!(\rho,\rho)\!)_\alpha)^{-1}S_\rho(R_\rho T_\alpha^{-1}g)`. (iii) If $`f\in\mathcal D_\alpha`
and $`F_Qf\in L^1(\nu_\alpha)`, then $`T_\alpha f` is represented by
$`g_{F_Qf}` against $`\mu_Q`; conversely, for $`G\in\mathcal K_\alpha`,
$`R_\rho T_\alpha^{-1}F_Q'G=W_\rho G`, and when $`G\in L^1(\nu_\alpha)`, $`F_Q'G` is
represented by $`g_G` and the second reconstruction formula is the spectral synthesis identity
of {bpref "thm:4.2"}[] (ii). (iv) The backprojection $`W_\rho^*` is a bounded operator
$`L^2(\lambda_\alpha)\to L^2(\nu_\alpha)` with $`W_\rho^* W_\rho=(\!(\rho,\rho)\!)_\alpha\mathrm{Id}`,
and $`W_\rho^* R_\rho f=(\!(\rho,\rho)\!)_\alpha F_Q f` holds in $`L^2(\nu_\alpha)` for
every $`f\in\mathcal E_\alpha`. For an input $`f\in\mathcal D_\alpha`, choose the Gaussian integral
as the representative of $`F_Qf`. The identity then holds pointwise with
the continuous Fourier-slice representative.
The remaining inversion step uses Gaussian input: the Hermite formula at $`\xi\ne0`
recovers the Hermite coefficients of $`f` from $`F_Qf`, these coefficients determine
$`f` in $`L^2(\mu_Q)`, and $`f=\Delta_Q[((\!(\rho,\rho)\!)_\alpha)^{-1}W_\rho^* R_\rho f]`.
:::

See the [proof in Appendix B](appendix-b/B___4-Proof-of-Theorem-4___3_LPAR_iii_RPAR_-and-_LPAR_iv_RPAR_/#--informal-preview-_FLQQ_thm___4___3_FLQQ_--proof).

:::corollary "cor:4.4" (lean := "OperatorRidgelet.Paper.cor_4_4_i, OperatorRidgelet.Paper.cor_4_4_ii, OperatorRidgelet.Paper.cor_4_4_iii, OperatorRidgelet.Paper.cor_4_4_iv") (uses := "aux:frame-operator")
Let $`\rho` be $`\alpha`-admissible, put $`C=(\!(\rho,\rho)\!)_\alpha>0`, and define
$`D_\rho=C^{-1}T_\alpha^{-1}S_\rho`. Then $`D_\rho R_\rho=\mathrm{Id}` and
$`\|D_\rho\|\le C^{-1/2}`. If $`f\in\mathcal E_\alpha`,
$`\gamma_\delta\in L^2(\lambda_\alpha)`, and $`\|\gamma_\delta-R_\rho f\|_2\le\delta`, then
$`\|D_\rho\gamma_\delta-f\|_{\mathcal E_\alpha}\le\delta/\sqrt C`.
This is an estimate in the completion norm, not an ambient $`L^2(\mu_Q)` or pointwise estimate.
:::

:::proof "cor:4.4" (uses := "thm:4.3, lem:B.1")
The left-inverse identity is {bpref "thm:4.3"}[] (ii). Since the transpose $`S_\rho` has norm
at most $`\sqrt C` and $`T_\alpha^{-1}` is an isometry, the decoder has norm at most
$`C^{-1}\sqrt C=C^{-1/2}`. Apply this bound to $`\gamma_\delta-R_\rho f`.
:::

*Remark 4.5 (Which inverse is bounded).*

The inverse $`T_\alpha^{-1}:\mathcal E_\alpha'\to\mathcal E_\alpha` is bounded
with norm one. This is the Hilbert-space norm of the construction; no bounded inverse in
the ambient $`L^2(\mu_Q)` norm is asserted. On the core, inversion factors through
$`F_Qf`, Fourier uniqueness of $`f\mu_Q`, and the Radon–Nikodym derivative. The Hermite
expansion makes the last two steps constructive.

# Vector-valued targets

:::definition "aux:vector-valued" (lean := "OperatorRidgelet.gaussFourierVec, OperatorRidgelet.ridgeletVec, OperatorRidgelet.coefficientFormulaVec, OperatorRidgelet.biasFourierVec, OperatorRidgelet.HasBiasFourierVec, OperatorRidgelet.spectralCoefficientVec, OperatorRidgelet.spectralInnerVec, OperatorRidgelet.spectralCoreVec, OperatorRidgelet.gaussFourierLpVec, OperatorRidgelet.spectralRangeVec, OperatorRidgelet.spectralEmbedVec, OperatorRidgelet.ridgeletExtensionVec, OperatorRidgelet.ridgeletRangeVec, OperatorRidgelet.SpectralAntiDualVec, OperatorRidgelet.rieszMapVec, OperatorRidgelet.rieszInvVec, OperatorRidgelet.transposeEmbedVec, OperatorRidgelet.frameOperatorVec, OperatorRidgelet.synthesisVec, OperatorRidgelet.backprojectionOfVec, OperatorRidgelet.backprojectionVec, OperatorRidgelet.backprojectionLpVec, OperatorRidgelet.coefficientProjectionVec, OperatorRidgelet.gaussFourierLineVec, OperatorRidgelet.hermiteExtensionVec, OperatorRidgelet.hermiteCoefficientVec, OperatorRidgelet.gaussFourierInvVec") (uses := "def:3.3, def:3.5, def:3.7, aux:frame-operator, aux:backprojection, aux:hermite")
Let $`Y` be a separable complex Hilbert space. All objects above have $`Y`-valued versions:
$`L^2(\mu_Q;Y)`, the Bochner integral
$`F_Qf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\mu_Q(\mathrm dx)\in Y`, the core
$`\mathcal D_\alpha(Y)`, the completion $`\mathcal E_\alpha(Y)` with inner product
$`\int\langle F_Qf,F_Qg\rangle_Y\mathrm d\nu_\alpha`, the transform
$`R_\rho f\in L^2(\lambda_\alpha;Y)`, the coefficient $`W_\rho G` of a density
$`G\in L^2(\nu_\alpha;Y)`, the anti-dual, Riesz map, frame and synthesis operators, the
backprojection, and the Hermite extension. The target $`g_G` and the condition in
{bpref "def:4.1"}[] are
already polymorphic in the target.
:::

:::theorem "thm:4.6" (lean := "OperatorRidgelet.Paper.thm_4_6_representation_i_a, OperatorRidgelet.Paper.thm_4_6_representation_i_b, OperatorRidgelet.Paper.thm_4_6_representation_i_c, OperatorRidgelet.Paper.thm_4_6_representation_ii_a, OperatorRidgelet.Paper.thm_4_6_representation_ii_b, OperatorRidgelet.Paper.thm_4_6_representation_ii_c, OperatorRidgelet.Paper.thm_4_6_representation_iii_a, OperatorRidgelet.Paper.thm_4_6_representation_iii_b, OperatorRidgelet.Paper.thm_4_6_representation_iii_c, OperatorRidgelet.Paper.thm_4_6_plancherel_i_a, OperatorRidgelet.Paper.thm_4_6_plancherel_i_b, OperatorRidgelet.Paper.thm_4_6_plancherel_ii_a, OperatorRidgelet.Paper.thm_4_6_plancherel_ii_b, OperatorRidgelet.Paper.thm_4_6_plancherel_ii_c, OperatorRidgelet.Paper.thm_4_6_plancherel_ii_d, OperatorRidgelet.Paper.thm_4_6_plancherel_iii, OperatorRidgelet.Paper.thm_4_6_frame_i_a, OperatorRidgelet.Paper.thm_4_6_frame_i_b, OperatorRidgelet.Paper.thm_4_6_frame_i_c, OperatorRidgelet.Paper.thm_4_6_frame_i_d, OperatorRidgelet.Paper.thm_4_6_frame_ii_a, OperatorRidgelet.Paper.thm_4_6_frame_ii_b, OperatorRidgelet.Paper.thm_4_6_frame_iii_a, OperatorRidgelet.Paper.thm_4_6_frame_iii_b, OperatorRidgelet.Paper.thm_4_6_frame_iii_c, OperatorRidgelet.Paper.thm_4_6_frame_iii_d, OperatorRidgelet.Paper.thm_4_6_frame_iii_e, OperatorRidgelet.Paper.thm_4_6_frame_iv_a, OperatorRidgelet.Paper.thm_4_6_frame_iv_b, OperatorRidgelet.Paper.thm_4_6_frame_iv_c, OperatorRidgelet.Paper.thm_4_6_frame_iv_d, OperatorRidgelet.Paper.thm_4_6_frame_iv_e, OperatorRidgelet.Paper.thm_4_6_frame_iv_f, OperatorRidgelet.Paper.thm_4_6_representation_iii_e, OperatorRidgelet.Paper.thm_4_6_frame_iv_completion") (uses := "aux:vector-valued, thm:4.2, thm:3.11, thm:4.3")
{bpref "thm:4.2"}[], {bpref "thm:3.11"}[], and {bpref "thm:4.3"}[] hold for $`Y`-valued targets,
with the same constants, with absolute values replaced by norms in $`Y`, scalar integrals by
Bochner integrals, and $`L^2` spaces by their $`Y`-valued counterparts. The Riesz map and its
inverse are isometries; their operator norms are one for $`Y\ne\{0\}` and zero for
$`Y=\{0\}`. The $`L^1` input injectivity statement, admissible Schwartz synthesis and frame
identities, completed $`L^2` backprojection, and jointly absolutely integrable tempered
synthesis all retain the corresponding scalar assumptions. The Lean statements
are one theorem per part of the three scalar theorems, with general input and
homogeneous direction measures where appropriate; the scalar existence claim of
{bpref "thm:4.2"}[] (iii)
is not repeated.
:::

:::proof "thm:4.6" (uses := "lem:A.1, lem:B.2, lem:B.3, lem:3.6")
Use {bpref "lem:A.1"}[] for jointly measurable Fourier representatives and
Hilbert-valued Plancherel, {bpref "lem:B.2"}[] for spectral synthesis and
uniqueness, and {bpref "lem:B.3"}[] for coefficient moments and joint
absolute integrability. The vector adjoint identity and integral formula are
{bpref "lem:3.6"}[]. These common lemmas justify the Fubini and Parseval
steps with the same constants. Completing the vector core and applying Riesz representation
proves the frame and reconstruction statements; the Gaussian Hermite expansion is applied
componentwise. If $`Y\ne\{0\}`, a nonzero constant vector belongs to the Gaussian core by
{bpref "lem:3.9"}[], so its Riesz isometries have norm one; when $`Y=\{0\}`, both
spaces and norms are zero. The integral representation with a continuous activation of
polynomial growth uses the fixed-support $`C^m` Bochner argument and the distributional
pairing tensored with the identity of $`Y`.
:::
