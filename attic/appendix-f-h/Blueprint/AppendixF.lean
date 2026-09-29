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

#doc (Manual) "Appendix F. Operator-valued parameters and the finite-dimensional reduction" =>
%%%
file := "appendix-f"
number := false
%%%

Operator-valued parameters can be related exactly to scalar ridge parameters through a
rank-one lift. Strong finite-rank approximation is uniform on compact input sets and gives
the Hilbert–Schmidt reduction. The finite-dimensional universality argument here is a
separate qualitative result; the constructive result of Section 6 uses spectral densities.

:::definition "aux:hilbert-schmidt" (lean := "OperatorRidgelet.hsNormSq, OperatorRidgelet.IsHilbertSchmidt, OperatorRidgelet.hsNorm")
The squared Hilbert–Schmidt norm of a bounded operator $`A` on $`H` is the supremum
$`\|A\|_{\mathcal L_2}^2=\sup\{\sum_{e\in s}\|Ae\|^2\}` over finite orthonormal families $`s`,
and $`\mathcal L_2(H)` is the set of bounded operators with finite Hilbert–Schmidt norm. Mathlib
has no Hilbert–Schmidt class; the definition is intrinsic, and equality with
$`\sum_n\|Ae_n\|^2` along a Hilbert basis follows from the basis-independence theorem
in the formalization infrastructure.
:::

:::definition "aux:operator-neuron" (lean := "OperatorRidgelet.operatorNeuron, OperatorRidgelet.operatorNeuronSet, OperatorRidgelet.ridgeSet, OperatorRidgelet.rankOneActivation, OperatorRidgelet.operatorFiniteNetwork, OperatorRidgelet.operatorSynthesis") (uses := "aux:hilbert-schmidt, def:2.1, def:2.2")
The operator neuron $`\mathrm n_{\ell,A,b}(x)=\langle\ell,\sigma(Ax+b)\rangle`, the sets of
neurons with operator parameter in a given subset of $`\mathcal L(H)` and of scalar ridges
$`x\mapsto\beta(\langle a,x\rangle+c)`, both as subsets of $`C(H;\mathbb R)` with the
compact-open topology, the rank-one activation $`\sigma_\beta(y)=\beta(\langle\psi,y\rangle)z`,
the finite-width operator network $`x\mapsto\sum_jv_j\,\mathrm n_{\ell,A_j,b_j}(x)`, and the
operator synthesis
$`S_{\mathrm{op}}\Gamma_{\mathrm{op}}(x)=\int\mathrm n_{\ell,A,b}(x)\,\Gamma_{\mathrm{op}}(\mathrm dA,\mathrm db)`
of a finite complex measure on $`\mathcal L(H)\times H`.
:::

:::lemma_ "lem:F.1" (lean := "OperatorRidgelet.Paper.lem_F_1") (uses := "aux:hilbert-schmidt, aux:operator-neuron")
Suppose $`\sigma:H\to H` is globally Lipschitz. The finite linear spans of the neurons
$`\mathrm n_{\ell,A,b}` with $`A\in\mathcal L(H)` and with $`A\in\mathcal L_2(H)` have the
same compact-open closure in $`C(H;\mathbb R)`.
:::

:::proof "lem:F.1"
Replace $`A_j` by $`A_j\Pi_n` with $`\Pi_n` the projection onto the first $`n` basis vectors;
each $`A_j\Pi_n` has finite rank, and strong convergence $`\Pi_nx\to x` is uniform on compact
sets by a finite-net argument, so the Lipschitz bound gives convergence in $`C(K)`.
:::

:::lemma_ "lem:F.2" (lean := "OperatorRidgelet.Paper.lem_F_2_i, OperatorRidgelet.Paper.lem_F_2_ii, OperatorRidgelet.Paper.lem_F_2_iii, OperatorRidgelet.Paper.lem_F_2_iv, OperatorRidgelet.Paper.lem_F_2_v, OperatorRidgelet.Paper.lem_F_2_vi, OperatorRidgelet.Paper.lem_F_2_vii") (uses := "aux:hilbert-schmidt, aux:operator-neuron, def:2.1, def:2.2")
For $`\psi\ne0` put $`A_a=\|\psi\|^{-2}\psi\otimes a` and $`b_c=c\|\psi\|^{-2}\psi`. Then
$`A_a\in\mathcal L_2(H)` (i), $`\|A_a\|_{\mathcal L_2}=\|a\|/\|\psi\|` (ii),
$`\|b_c\|=|c|/\|\psi\|` (iii), and $`\pi_\psi(A_a,b_c)=(a,c)` (iv). The section
$`J_\psi(a,c)=(A_a,b_c)` is continuous into $`\mathcal L_2(H)\times H` (v), and every scalar
integral network (vi) or finite-width network (vii) with activation $`\beta` lifts exactly to
the operator architecture with activation $`\sigma_\beta` and readout normalized by
$`\langle\ell,z\rangle=1`.
:::

:::proof "lem:F.2"
$`A_a` has rank at most one and $`A_a^*y=\|\psi\|^{-2}\langle y,\psi\rangle a`, so
$`A_a^*\psi=a`; the norms are computed directly, and pushing a coefficient measure forward by
$`J_\psi` preserves its synthesis because the neuron at $`J_\psi(a,c)` is the scalar ridge at
$`(a,c)`.
:::

:::proposition "prop:F.3" (lean := "OperatorRidgelet.Paper.prop_F_3_i, OperatorRidgelet.Paper.prop_F_3_ii") (uses := "aux:operator-neuron")
Let $`\beta:\mathbb R\to\mathbb R` be continuous and not a polynomial. Finite linear
combinations of $`\beta(\langle a,x\rangle+c)` are dense in $`C(H;\mathbb R)` for uniform
convergence on compact sets (i); the same holds for the rank-one operator activation
$`\sigma_\beta` with Hilbert–Schmidt parameters (ii).
:::

:::proof "prop:F.3" (uses := "lem:F.2, cor:D.8, roadmap:finite-dim-universality")
For finite-rank projections $`\Pi_m\to I`, $`f\circ\Pi_m\to f` uniformly on compact sets; the
finite-dimensional universal approximation theorem approximates $`f` on $`\Pi_mK` by scalar
ridges, which compose with $`\Pi_m` to ridges on $`H`, and the rank-one lift gives (ii). This
reduction gives no information on the parameters; the constructive statement is
{bpref "thm:6.5"}[].
:::

:::lemma_ "lem:F.4" (lean := "OperatorRidgelet.Paper.lem_F_4_i, OperatorRidgelet.Paper.lem_F_4_ii, OperatorRidgelet.Paper.lem_F_4_iii, OperatorRidgelet.Paper.lem_F_4_iv, OperatorRidgelet.Paper.lem_F_4_v") (uses := "aux:operator-neuron, def:2.2")
Each part carries only the hypotheses it needs. For every $`\psi` and every finite complex
Borel measure $`\Gamma_{\mathrm{op}}` on $`\mathcal L_2(H)\times H`,
$`|(\pi_\psi)_\#\Gamma_{\mathrm{op}}|\le(\pi_\psi)_\#|\Gamma_{\mathrm{op}}|` (ii). If moreover
$`\beta` is real and globally Lipschitz, $`\langle\ell,z\rangle=1`, and
$`\int(1+\|A\|_{\mathcal L_2}+\|b\|)\,\mathrm d|\Gamma_{\mathrm{op}}|<\infty`, then
$`S_{\mathrm{op}}\Gamma_{\mathrm{op}}=S_\beta[(\pi_\psi)_\#\Gamma_{\mathrm{op}}]` (i) and, for
compact $`K` with $`r_K=\sup_K\|x\|`,
$`\|S_{\mathrm{op}}\Gamma_{\mathrm{op}}\|_{C(K)}\le\int[|\beta(0)|+\operatorname{Lip}(\beta)\|\psi\|(r_K\|A\|_{\mathcal L_2}+\|b\|)]\,\mathrm d|\Gamma_{\mathrm{op}}|`
(iii); $`\psi\ne0` is not needed for any of these. Conversely, for $`\psi\ne0` and
$`\langle\ell,z\rangle=1`, $`(\pi_\psi)_\#(J_\psi)_\#\Gamma=\Gamma` (iv) and
$`S_{\mathrm{op}}(J_\psi)_\#\Gamma=S_\beta[\Gamma]` (v) for every activation $`\beta` and every
finite complex Borel measure $`\Gamma` on $`H\times\mathbb R`, with no Lipschitz and no moment
condition.
:::

:::proof "lem:F.4" (uses := "lem:F.2")
The variation inequality is the definition of the variation as a supremum over partitions,
applied to the preimages of a partition. The atom identity is the rank-one reduction,
$`\|A^*\psi\|\le\|A\|_{\mathcal L_2}\|\psi\|` supplies the integrable envelope, and the change
of variables for finite complex measures proves the synthesis identity. Finally
$`\pi_\psi\circ J_\psi=\mathrm{id}`, and $`J_\psi` is a homeomorphism onto its closed range, so
the last change of variables holds atomwise.
:::
