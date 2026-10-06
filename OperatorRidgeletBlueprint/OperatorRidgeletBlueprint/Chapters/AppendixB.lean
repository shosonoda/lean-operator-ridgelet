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

#doc (Manual) "Appendix B. Coefficient projections and minimum-norm solutions" =>
%%%
file := "appendix-b"
number := false
%%%

The coefficient adjoint and reconstruction theorem have already been proved in the main text. This appendix derives further range, orthogonal projection, and minimum-norm coefficient formulas from them.

:::proposition "prop:B.1" (lean := "OperatorRidgelet.Paper.prop_B_1_i, OperatorRidgelet.Paper.prop_B_1_ii, OperatorRidgelet.Paper.prop_B_1_iii, OperatorRidgelet.Paper.prop_B_1_iv, OperatorRidgelet.Paper.prop_B_1_v, OperatorRidgelet.Paper.prop_B_1_vi, OperatorRidgelet.Paper.prop_B_1_vii, OperatorRidgelet.Paper.prop_B_1_viii") (uses := "aux:backprojection, aux:frame-operator")
Let $`\rho` be $`\alpha`-admissible with $`C=(\!(\rho,\rho)\!)_\alpha` and
$`\mathcal Y=L^2(\lambda_\alpha)`. The integral defining $`W_\rho^*\gamma`
converges absolutely for $`\nu_\alpha`-almost every $`\xi` (i), is independent as an $`L^2`
class of the jointly measurable Fourier representative (ii), and satisfies
$`\|W_\rho^*\gamma\|_{L^2(\nu_\alpha)}\le\sqrt C\|\gamma\|_{\mathcal Y}` (iii);
$`W_\rho^*` is the Hilbert adjoint of $`W_\rho` (iv) and $`W_\rho^* W_\rho=C\,\mathrm{Id}`
(v). The operator $`C^{-1}W_\rho W_\rho^*` projects onto $`W_\rho L^2(\nu_\alpha)`.
The operator $`\Pi_\rho=C^{-1}W_\rho P_{\mathcal K_\alpha}W_\rho^*` is the orthogonal
projection onto $`\operatorname{Ran}R_\rho` (vi), the minimum-norm solution of
$`S_\rho\gamma=F\in\mathcal E_\alpha'` is $`C^{-1}R_\rho T_\alpha^{-1}F` (vii), and all
solutions differ from it by an element of $`(\operatorname{Ran}R_\rho)^\perp` (viii).
:::

:::proof "prop:B.1" (uses := "lem:3.8, lem:3.2, thm:3.14")
The change of variables $`\xi=-\omega a` gives
$`\frac1{2\pi}\int\int|\omega|^{-\alpha}|\gamma^\sharp(-\xi/\omega,\omega)|^2\mathrm d\omega\,\nu_\alpha(\mathrm d\xi)=\|\gamma\|_{\mathcal Y}^2`,
and weighted Cauchy–Schwarz in $`\omega` proves absolute convergence, representative
independence, the bound, and the adjoint identity. Since $`R_\rho=W_\rho F_Q` with
$`F_Q` unitary onto $`\mathcal K_\alpha`, $`C^{-1/2}W_\rho|_{\mathcal K_\alpha}` is an
isometry with closed image, and $`R_\rho'R_\rho=CT_\alpha` (the frame identity, which is the
Plancherel identity read through the transpose) identifies the kernel of $`R_\rho'` with
$`(\operatorname{Ran}R_\rho)^\perp`.
:::

*Remark B.2 (Range of the analysis operator).*

The closed range is $`R_\rho\mathcal E_\alpha=W_\rho\mathcal K_\alpha`, which is
contained in the closed space $`W_\rho L^2(\nu_\alpha)`. Their orthogonal projections
are respectively $`C^{-1}W_\rho P_{\mathcal K_\alpha}W_\rho^*` and
$`C^{-1}W_\rho W_\rho^*`. Retaining the closed spectral subspace distinguishes
coefficients obtained by analysis from arbitrary synthesis coefficients. The preceding result
also identifies the minimum-norm coefficient and the kernel of synthesis.
