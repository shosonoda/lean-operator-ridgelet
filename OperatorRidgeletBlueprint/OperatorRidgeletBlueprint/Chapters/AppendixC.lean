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

#doc (Manual) "Appendix C. Additional approximation bounds" =>
%%%
file := "appendix-c"
number := false
%%%

These consequences supplement the main approximation theorems. The first bounds fluctuations for bounded parameters; the second separates the error of input truncation from finite-width approximation. Neither is used to prove the main universality or approximation rate.

# Concentration for bounded parameters

:::corollary "cor:C.1" (lean := "OperatorRidgelet.Paper.cor_C_1") (uses := "thm:6.5, aux:sampling-data")
Under the hypotheses of {bpref "thm:6.5"}[], suppose $`\|a\|^2+|c|^2\le B^2`
almost surely and put $`M_K=|\beta(0)|+\operatorname{Lip}(\beta)R_KB`. With probability at
least $`1-\delta`,
$`\|f_N-f\|_{C(K)}\le\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)+VM_K\sqrt{2\log(1/\delta)/N}`.
:::

:::proof "cor:C.1"
Each atom has norm at most $`M_K`, so replacing one sample changes $`\|f_N-f\|_{C(K)}` by at
most $`2VM_K/N`; the bounded-difference inequality bounds the excess over the expectation.
:::

# Input truncation and finite-width approximation

:::corollary "cor:C.2" (lean := "OperatorRidgelet.Paper.cor_C_2_i, OperatorRidgelet.Paper.cor_C_2_ii") (uses := "thm:6.5, aux:sampling-data")
Let $`\Pi_m` be finite-rank orthogonal projections converging strongly to the identity. For
$`f\in C(H)` and compact $`K`, $`\|f-f\circ\Pi_m\|_{C(K)}\to0` (i). If $`f=S_\beta\Gamma`
satisfies the hypotheses of {bpref "thm:6.5"}[] and the same samples are used
with directions $`\Pi_ma_j`, then
$`\mathbb E\|f-f_{m,N}\|_{C(K)}\le\operatorname{Lip}(\beta)\bigl(\int\|a\|\,\mathrm d|\Gamma|\bigr)\sup_K\|x-\Pi_mx\|+\frac{8V}{\sqrt N}(|\beta(0)|+\operatorname{Lip}(\beta)R_KM_2)`
(ii).
:::

:::proof "cor:C.2"
A finite-net argument gives $`\sup_K\|x-\Pi_mx\|\to0`, and uniform convergence of
$`f\circ\Pi_m` on $`K` follows by compactness and continuity of $`f`; the triangle inequality
separates truncation from sampling, and projecting directions does not increase their second
moment.
:::
