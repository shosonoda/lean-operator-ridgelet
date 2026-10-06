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

#doc (Manual) "Appendix D. The finite-dimensional case and the dilation obstruction" =>
%%%
file := "appendix-d"
number := false
%%%

This appendix compares the weighted construction with the finite-dimensional Fourier
calculation. In finite dimension the homogeneous Gaussian mixture has a restricted range
of exponents. We then identify the frame operator and explain why direct dilation of a
Gaussian spectral measure cannot supply the proposed finite coefficient measure.

# D.1 A Fourier calculation for comparison
%%%
number := false
%%%

For Lebesgue input measure on $`\mathbb R^m`, Fourier inversion and a change of
variables give the familiar dilation integral with the factor $`|\omega|^{-m}`.
The infinite-dimensional construction replaces this factor by homogeneity of the
direction measure, with exponent $`\alpha`, rather than assigning a dimension to $`H`.

# D.2 The finite-dimensional reference measure
%%%
number := false
%%%

For $`0<\alpha<m`, the mixture of $`\mathcal N(0,2sI)` with weight
$`s^{\alpha/2-1}\,\mathrm ds` has density $`c_{m,\alpha}|\xi|^{\alpha-m}`.
The constant is $`c_{m,\alpha}=2^{-\alpha}\pi^{-m/2}\Gamma((m-\alpha)/2)`.
The Lebesgue-direction case must be treated separately; it is not obtained by
substituting $`\alpha=m` into this mixture formula.

*Remark D.1 (Comparison with familiar spaces).*

For $`0<\alpha<m`, the squared norm is
$`c_{m,\alpha}\int_{\mathbb R^m}|\widehat{fp_Q}(\xi)|^2|\xi|^{\alpha-m}\,\mathrm d\xi`:
the homogeneous Sobolev norm of order $`(\alpha-m)/2` of the weighted density $`fp_Q`.
In infinite dimension there is no Lebesgue measure with which to remove the weight, and
no identification of $`\mathcal E_\alpha` with a Sobolev space is asserted. The closed
space $`\mathcal K_\alpha\subset L^2(\nu_\alpha)` is not asserted to be a reproducing
kernel Hilbert space.

# D.3 Filtered backprojection
%%%
number := false
%%%

:::definition "aux:finite-dim" (lean := "OperatorRidgelet.FiniteDim.mixtureConst, OperatorRidgelet.FiniteDim.directionMeasure, OperatorRidgelet.FiniteDim.frameConst, OperatorRidgelet.FiniteDim.fourier, OperatorRidgelet.FiniteDim.densityMeasure, OperatorRidgelet.FiniteDim.frameRepresentative, OperatorRidgelet.FiniteDim.fracLaplacian, OperatorRidgelet.strongLawSet") (uses := "aux:centered-gaussian")
On $`H=\mathbb R^m` with $`P=I` and $`0<\alpha<m`, the mixture is
$`\nu_\alpha(\mathrm da)=c_{m,\alpha}\|a\|^{\alpha-m}\,\mathrm da` with
$`c_{m,\alpha}=2^{-\alpha}\pi^{-m/2}\Gamma((m-\alpha)/2)` and $`k_{m,\alpha}=(2\pi)^mc_{m,\alpha}`;
for a Gaussian density $`p` and $`g=fp`, the frame representative is
$`t_f(x)=\int e^{i\langle x,\xi\rangle}\widehat g(\xi)\,\nu_\alpha(\mathrm d\xi)`, and
$`(-\Delta)^s` is the Fourier multiplier $`\|\xi\|^{2s}`. For the dilation obstruction, with
eigenvectors $`e_j` and eigenvalues $`w_j>0` of $`W`, the strong-law sets are
$`E_t=\{x:\lim_n\frac1n\sum_{j\le n}\langle x,e_j\rangle^2/w_j=t\}`.
:::

:::corollary "cor:D.2" (lean := "OperatorRidgelet.Paper.cor_D_2_i, OperatorRidgelet.Paper.cor_D_2_ii, OperatorRidgelet.Paper.cor_D_2_iii, OperatorRidgelet.Paper.cor_D_2_iv, OperatorRidgelet.Paper.cor_D_2_v, OperatorRidgelet.Paper.cor_D_2_vi") (uses := "aux:finite-dim, def:3.10")
Let $`H=\mathbb R^m`, $`0<\alpha<m`, and let $`p` be a nondegenerate Gaussian density. If
$`f\in L^2(p\,\mathrm dx)` with $`g=fp\in\mathcal S(\mathbb R^m)`, then $`f\in\mathcal D_\alpha`
(i) and $`t_f=k_{m,\alpha}(-\Delta)^{-(m-\alpha)/2}g` (ii). For a band-pass $`\rho`, the
synthesis $`S_\rho R_\rho f` is represented against $`p\,\mathrm dx` by
$`(\!(\rho,\rho)\!)_\alpha t_f` (iii), so that, distributionally,
$`f=\frac{p^{-1}}{k_{m,\alpha}(\!(\rho,\rho)\!)_\alpha}(-\Delta)^{(m-\alpha)/2}S_\rho R_\rho f` (iv).
With Lebesgue direction measure and $`\alpha=m`, $`t_f=(2\pi)^mg` (v) and
$`f=(2\pi)^{-m}((\!(\rho,\rho)\!)_m)^{-1}p^{-1}S_\rho R_\rho f` (vi).
:::

:::proof "cor:D.2" (uses := "thm:3.14, thm:4.8")
Here $`F_Qf=\widehat g`, the weight $`\|\xi\|^{\alpha-m}` is locally integrable, and
Fourier inversion gives $`\widehat{t_f}=k_{m,\alpha}\|\xi\|^{\alpha-m}\widehat g`; Fubini
identifies $`\int t_f\overline h\,p\,\mathrm dx` with $`\langle f,h\rangle_{\mathcal E_\alpha}`,
which is the frame-operator representation of {bpref "thm:4.8"}[] (iii).
:::

# D.4 Why the spectral measure cannot be dilated
%%%
number := false
%%%

:::proposition "prop:D.3" (lean := "OperatorRidgelet.Paper.prop_D_3_i_a, OperatorRidgelet.Paper.prop_D_3_i_b, OperatorRidgelet.Paper.prop_D_3_i_c, OperatorRidgelet.Paper.prop_D_3_i_d, OperatorRidgelet.Paper.prop_D_3_ii") (uses := "aux:finite-dim, aux:centered-gaussian")
Let $`\dim H=\infty` and let $`W` be injective, positive, self-adjoint, and trace class with
eigenvectors $`e_j` and eigenvalues $`w_j>0`. The sets $`E_t`, $`t>0`, are Borel (i a) and
pairwise disjoint (i b), $`\mathcal N(0,tW)(E_t)=1` (i c), and consequently a
$`\sigma`-finite measure dominates $`\mathcal N(0,tW)` for at most countably many $`t` (i d).
Hence, for a bounded Borel $`r` with $`\{r\ne0\}` of positive measure, there is no finite
complex Borel measure $`\Gamma` on $`H\times\mathbb R` whose bias slices satisfy
$`\int_{E\times\mathbb R}e^{i\omega c}\,\Gamma(\mathrm da,\mathrm dc)=r(\omega)(D_{1/\omega})_\#\mathcal N(0,W)(E)`
for almost every $`\omega\ne0` (ii).
:::

:::proof "prop:D.3"
The strong law of large numbers for the independent normalized Gaussian coordinates gives
$`\mathcal N(0,tW)(E_t)=1`, a $`\sigma`-finite measure has at most countably many disjoint
sets of positive measure, and a measure $`\Gamma` as in (ii) would give a finite measure
dominating $`\mathcal N(0,W/\omega^2)` for uncountably many $`\omega`.
:::
