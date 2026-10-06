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

#doc (Manual) "Appendix A. A kernel interpretation of the frame operator" =>
%%%
file := "appendix-a"
number := false
%%%

This appendix computes a regularized characteristic functional of the infinite Gaussian mixture and explains a formal kernel interpretation of the frame operator. These optional observations are not prerequisites for the main proofs.

:::lemma_ "lem:A.1" (lean := "OperatorRidgelet.Paper.lem_A_1_i, OperatorRidgelet.Paper.lem_A_1_ii, OperatorRidgelet.Paper.lem_A_1_iii, OperatorRidgelet.Paper.lem_A_1_iv") (uses := "aux:gaussian-mixture")
For $`z\ne0` put $`q=\langle Pz,z\rangle>0` (i) and
$`\nu_\alpha^{\varepsilon,M}=\int_\varepsilon^M\mathcal N(0,2sP)s^{\alpha/2-1}\mathrm ds`.
Then $`\lim_{\varepsilon\downarrow0,M\uparrow\infty}\int_He^{i\langle z,\xi\rangle}\,\nu_\alpha^{\varepsilon,M}(\mathrm d\xi)=\Gamma(\alpha/2)q^{-\alpha/2}`
(ii), where $`\int_0^\infty e^{-sq}s^{\alpha/2-1}\mathrm ds=\Gamma(\alpha/2)q^{-\alpha/2}`
(iii). In contrast $`\int_H|e^{i\langle z,\xi\rangle}|\,\nu_\alpha(\mathrm d\xi)=\infty`
(iv), so the limit is not a Lebesgue integral against $`\nu_\alpha`.
:::

:::proof "lem:A.1" (uses := "lem:3.1, lem:3.2")
The truncated mixture is finite, so Fubini and the characteristic functional of
$`\mathcal N(0,2sP)` reduce the integral to
$`\int_\varepsilon^Me^{-sq}s^{\alpha/2-1}\mathrm ds`; monotone convergence and the
substitution $`u=sq` finish the proof.
:::

*Remark A.2 (A Riesz-type kernel for the frame operator).*

The regularized characteristic functional in {bpref "lem:A.1"}[] suggests
the kernel $`\Gamma(\alpha/2)\langle P(x-y),x-y\rangle^{-\alpha/2}` for the frame
operator. This is only a formal interchange against an infinite oscillatory measure and is
not used as an identity. In finite dimension, with $`P=I` and $`0<\alpha<m`, it agrees
with the Riesz-potential interpretation of {bpref "cor:D.2"}[].
