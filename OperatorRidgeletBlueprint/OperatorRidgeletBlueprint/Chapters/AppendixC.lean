import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Tempered
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

#doc (Manual) "Appendix C. Proofs for Section 5 and weighted Sobolev duality" =>
%%%
file := "appendix-c"
number := false
%%%

We prove tempered reconstruction through regularization, then establish weighted Sobolev
duality and the estimates needed for absolute synthesis. Membership in a weighted Sobolev
activation class controls the distributional Fourier pairing; it does not by itself select
a continuous pointwise representative.

# C.1 Proof of Theorem 5.2
%%%
number := false
%%%

We prove {bpref "thm:5.2"}[].

:::proof "thm:5.2" (uses := "thm:3.11, thm:4.3, thm:4.2")
Each $`\beta_\varepsilon` is an admissible real filter, so the Plancherel identity gives
$`S_{\beta_\varepsilon}R_\rho f=C_{\beta_\varepsilon,\rho}^{(\alpha)}T_\alpha f`;
distributional convergence of $`\widehat\beta*\eta_\varepsilon` against the fixed test
function $`\widehat\rho(-\omega)|\omega|^{-\alpha}` gives convergence of the constants, and
$`T_\alpha` is an isometry, so the functionals converge in $`\mathcal E_\alpha'`. The
existence of $`\rho` with nonzero constant is the last step of the proof of
{bpref "thm:4.2"}[].
:::

# C.2 Weighted Sobolev activation spaces
%%%
number := false
%%%

:::lemma_ "lem:C.1" (lean := "OperatorRidgelet.activationFourierCoordinate, OperatorRidgelet.activationCoordinate, OperatorRidgelet.activationNorm, OperatorRidgelet.testFilterCoordinate, OperatorRidgelet.testFilterNorm, OperatorRidgelet.Paper.lem_C_1_i, OperatorRidgelet.Paper.lem_C_1_ii, OperatorRidgelet.Paper.lem_C_1_iii, OperatorRidgelet.Paper.lem_C_1_iv, OperatorRidgelet.Paper.lem_C_1_v") (uses := "aux:conventions, aux:tempered-distributions")
The map $`\beta\mapsto\langle\omega\rangle^sB^{-t}\widehat\beta` is an isometric isomorphism
$`\mathcal A_{s,t}\to L^2(\mathbb R)`: the coordinate is represented by an $`L^2` function
(i), the map is injective (ii) and onto (iii). Moreover
$`|\frac1{2\pi}\langle\widehat\beta,r\rangle|\le\frac1{2\pi}\|\beta\|_{\mathcal A_{s,t}}\|r\|_{\mathcal H^\sharp_{s,t}}`
(iv), so the pairing extends to the completion of the test filters in
$`\mathcal H^\sharp_{s,t}` (v).
:::

:::proof "lem:C.1"
$`\beta=\langle\cdot\rangle^t\mathcal F^{-1}[\langle\omega\rangle^{-s}g]` is a preimage of
$`g\in L^2`; the multiplier $`\langle u\rangle^t` is real and even, so $`B^t` is symmetric
for the bilinear pairing, the identity
$`\langle\widehat\beta,r\rangle=\int(\langle\omega\rangle^sB^{-t}\widehat\beta)(\langle\omega\rangle^{-s}B^tr)\,\mathrm d\omega`
extends by density, and Cauchy–Schwarz proves the bound.
:::

:::lemma_ "lem:C.2" (lean := "OperatorRidgelet.MemActivationSpaceFun, OperatorRidgelet.gaussianCdf, OperatorRidgelet.gaussianFun, OperatorRidgelet.weightedDistribution, OperatorRidgelet.Paper.lem_C_2_relu_mem, OperatorRidgelet.Paper.lem_C_2_relu_lipschitz, OperatorRidgelet.Paper.lem_C_2_relu_not_polynomial, OperatorRidgelet.Paper.lem_C_2_tanh_mem, OperatorRidgelet.Paper.lem_C_2_tanh_lipschitz, OperatorRidgelet.Paper.lem_C_2_tanh_not_polynomial, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_mem, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_lipschitz, OperatorRidgelet.Paper.lem_C_2_gaussianCdf_not_polynomial, OperatorRidgelet.Paper.lem_C_2_gaussian_mem, OperatorRidgelet.Paper.lem_C_2_gaussian_lipschitz, OperatorRidgelet.Paper.lem_C_2_gaussian_not_polynomial, OperatorRidgelet.Paper.lem_C_2_exists_filter") (uses := "aux:tempered-distributions")
ReLU, $`\tanh`, the Gaussian distribution function
$`\Phi(u)=\int_{-\infty}^u(2\pi)^{-1/2}e^{-v^2/2}\,\mathrm dv`, and $`e^{-u^2/2}` belong to
$`\mathcal A_{0,2}=\langle\cdot\rangle^2L^2(\mathbb R)`, are globally Lipschitz, and are not
polynomials (twelve claims). For every non-polynomial real $`\beta\in\mathcal S'` there is a
real band-pass $`\rho` with $`C_{\beta,\rho}^{(\alpha)}=1`.
:::

:::proof "lem:C.2" (uses := "lem:C.1, thm:4.2")
Membership in $`\mathcal A_{0,2}` means $`\langle u\rangle^{-2}\beta\in L^2`; three of the
functions are bounded and ReLU satisfies $`\int_0^\infty u^2(1+u^2)^{-2}\mathrm du<\infty`.
Their derivatives are bounded wherever defined, the bounded functions are nonconstant and ReLU
is not smooth at zero, and the last statement is the final part of the proof of
{bpref "thm:4.2"}[] followed by rescaling $`\rho`.
:::

# C.3 Sobolev estimates for absolute synthesis
%%%
number := false
%%%

:::lemma_ "lem:C.3" (lean := "OperatorRidgelet.bracket, OperatorRidgelet.MemRaySobolev, OperatorRidgelet.raySobolevNorm, OperatorRidgelet.rayProfile, OperatorRidgelet.sobolevMomentConst, OperatorRidgelet.Paper.lem_C_3_i, OperatorRidgelet.Paper.lem_C_3_ii, OperatorRidgelet.Paper.lem_C_3_iii, OperatorRidgelet.Paper.lem_C_3_iv") (uses := "aux:conventions")
Use $`\|h\|_{H^s_\omega}` for the norm of a profile $`h` whose inverse Fourier transform
$`\gamma=\check h` satisfies $`\|h\|_{H^s_\omega}^2=2\pi\int\langle
t\rangle^{2s}\|\gamma(t)\|^2\,\mathrm dt<\infty`. For $`s>1/2` and $`0\le r<s-1/2`,
$`\int\langle t\rangle^r\|\gamma(t)\|\,\mathrm dt\le A_{s,r}\|h\|_{H^s_\omega}` with
$`A_{s,r}=(2\pi)^{-1/2}(\int(1+t^2)^{-(s-r)}\mathrm dt)^{1/2}`. Reflection $`Rh(\omega)=h(-\omega)`
is an isometry, $`\|M_uh\|_{H^s_\omega}\le(1+|u|)^s\|h\|_{H^s_\omega}` for the modulation
$`M_uh(\omega)=e^{iu\omega}h(\omega)`, and $`(u,h)\mapsto M_uh` is jointly continuous.
:::

:::proof "lem:C.3"
The weighted $`L^1` bound is Cauchy--Schwarz applied to $`\langle t\rangle^{-(s-r)}` and
$`\langle t\rangle^{s}\|\gamma(t)\|`, the scalar factor being integrable exactly when
$`s-r>1/2`. Reflection and modulation correspond to $`\gamma(-\cdot)` and $`\gamma(\cdot+u)` on
the coefficient side, and $`\langle t-u\rangle\le(1+|u|)\langle t\rangle` gives the modulation
bound. Joint continuity reduces, by that bound and the triangle inequality, to the strong
continuity of translation, which follows from the strong continuity of translation in $`L^2`
and dominated convergence for the multiplier
$`(\langle t\rangle/\langle t+u\rangle)^s`. Only the weighted $`L^1` bound and the reflection
isometry are used for {bpref "thm:5.6"}[]; the modulation bound and the
joint continuity are the mapping properties of the alternative route through an
$`H^s_\omega`-valued Bochner integral.
:::

:::lemma_ "lem:C.4" (lean := "OperatorRidgelet.sobolevPairing, OperatorRidgelet.sobolevPairingConst, OperatorRidgelet.Paper.lem_C_4_i, OperatorRidgelet.Paper.lem_C_4_ii, OperatorRidgelet.Paper.lem_C_4_iii")
Let $`\sigma` be continuous with $`|\sigma(t)|\le C_\sigma(1+|t|)^p`, $`p\ge0`, and
$`s>p+1/2`, and put $`b_{\sigma,s}=\|\langle\cdot\rangle^{-s}\sigma\|_2`, which is finite. The
pairing $`L_\sigma^Y(h)=\int\sigma(t)\check h(-t)\,\mathrm dt` converges absolutely and
satisfies $`\|L_\sigma^Y(h)\|\le(2\pi)^{-1/2}b_{\sigma,s}\|h\|_{H^s_\omega}`, so it is the
bounded extension of $`(2\pi)^{-1}\langle\widehat\sigma,\cdot\rangle` to $`H^s_\omega`.
Moreover $`\int\sigma(u-b)\gamma(b)\,\mathrm db=L_\sigma^Y(M_uh)`.
:::

:::proof "lem:C.4" (uses := "lem:C.3")
$`1+|t|\le\sqrt2\langle t\rangle` turns the growth bound into
$`\langle t\rangle^{-s}|\sigma(t)|\le C_\sigma2^{p/2}\langle t\rangle^{p-s}`, whose square is
integrable for $`s-p>1/2`. Weighted Cauchy--Schwarz against
{bpref "lem:C.3"}[] gives absolute convergence and the bound, the reflection isometry
turning $`\|\gamma(-\cdot)\|` into $`\|h\|_{H^s_\omega}`. The translation formula is the change
of variables $`b=u-t`.
:::

# C.4 Proof of Theorem 5.6
%%%
number := false
%%%

We prove {bpref "thm:5.6"}[].

:::proof "thm:5.6" (uses := "lem:C.3, lem:C.4")
The moments are the weighted $`L^1` estimate of {bpref "lem:C.3"}[] applied to
$`b\mapsto\gamma_g(a,b)`,
$`1+\|a\|+|b|\le\sqrt2(1+\|a\|)\langle b\rangle`, and Tonelli; the case $`r=0` gives the finite
total variation of the coefficient measure, and the growth bound of $`\sigma` with $`r=p`
gives the absolute convergence and the
majorant. For the identity, Fubini in the two parameters turns the synthesis into
$`\int\sigma(t)\Psi(t)\,\mathrm dt` with
$`\Psi(t)=\int\gamma_g(a,\langle a,x\rangle-t)\,\mathrm d\nu`. Fubini again computes the profile
of the integrable $`\Psi`, which homogeneity identifies with
$`\widehat\rho(\omega)|\omega|^{-\alpha}f_g(x)` off the origin, hence everywhere by continuity;
the $`L^1` uniqueness of the profile then identifies $`\Psi` with
$`\check q_{\alpha,\rho}(-\cdot)f_g(x)`, and the pairing of {bpref "lem:C.4"}[] gives
the constant. Continuity is dominated convergence with the majorant. The final clause of the
manuscript statement, that $`\gamma_g` lies in $`L^2(\nu\otimes\mathrm db;Y)` with
$`\|\gamma_g\|^2=(\!(\rho,\rho)\!)_\alpha\|g\|^2_{L^2(\nu;Y)}` when $`Y` is a separable complex
Hilbert space, $`(\!(\rho,\rho)\!)_\alpha<\infty` and $`g\in L^2(\nu;Y)`, is not part of the
Lean statement.
:::
