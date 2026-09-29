import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgeletBlueprint.Chapters.Transform
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

#doc (Manual) "Appendix G. Details of the analysis filters" =>
%%%
file := "appendix-g"
number := false
%%%

This appendix verifies the explicit filters presented in Sections 3 and 5. It supplies
the admissibility calculations, Sobolev estimates and reconstruction constants used
in those examples.

# G.1 Proof of Example 3.12
%%%
file := "proof-3-12"
number := false
%%%

The statement is {bpref "ex:3.12"}[].

:::proof "ex:3.12"
The bump and all its derivatives vanish at $`|u|=1`, the support stays away from
$`\omega=0`, Fourier inversion maps $`C_c^\infty` into $`\mathcal S`, even real Fourier data
give an even real inverse, and on the compact support $`|\omega|^{-\alpha}` is bounded above
and below.
:::

# G.2 Proof of Example 3.13
%%%
file := "proof-3-13"
number := false
%%%

The statement is {bpref "ex:3.13"}[].

:::proof "ex:3.13"
With $`g(t)=e^{-t^2/2}`, $`\rho_{\mathrm{MH}}=-g''` and the differentiation rule gives the
Fourier transform; then
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\int_{\mathbb R}|\omega|^{4-\alpha}e^{-\omega^2}\mathrm d\omega=\Gamma((5-\alpha)/2)`,
convergent at zero exactly when $`\alpha<5`.
:::

# G.3 Proof of Proposition 5.8
%%%
file := "proof-5-8"
number := false
%%%

The statement is {bpref "prop:5.8"}[].

:::proof "prop:5.8" (uses := "lem:C.3")
The Fourier transform $`\widehat\rho_k` is a polynomial times a Gaussian, hence Schwartz,
and real and even, so its inverse
angular transform is a real Schwartz function. It vanishes only at the origin, which is
therefore in the closed support, so the filter is not band pass, while
$`|\widehat\rho_k|^2|\omega|^{-\alpha}=|\omega|^{4k-\alpha}e^{-2\omega^2}` is integrable exactly
for $`4k-\alpha>-1`. Homogeneity scales balls, $`\nu(B_R)=R^\alpha\nu(B_1)`, and the dyadic
annuli give a geometric series, which is the moment bound. Write
$`h_0(\omega)=\omega^{2k}e^{-\omega^2}` and $`A=(1+\|a\|^2)^{1/2}`.
The function $`h_a(\omega)=\omega^{2k}e^{-A^2\omega^2}v` has inverse transform
$`A^{-2k-1}\rho_k(b/A)v`, a dilate of a Schwartz function, so it lies in every $`H^s_\omega`,
with $`\|h_a\|_{H^s_\omega}\le\|v\|\,\|h_0\|_{H^s_\omega}A^{s-2k-1/2}`;
$`1+\|a\|\le\sqrt2A` and the moment bound give $`\mathfrak B_s<\infty` exactly in the stated
range. For the Sobolev test, the Gamma integral
$`|\omega|^{-\alpha}=\Gamma(\alpha/2)^{-1}\int_0^\infty u^{\alpha/2-1}e^{-u\omega^2}\mathrm du`
writes $`q_{\alpha,\rho_k}` as a superposition of the rescaled functions
$`A^{-2k}h_0(A\,\cdot)` with $`A=(1+u)^{1/2}`; Fubini gives its inverse transform,
and Cauchy--Schwarz against the finite weight
$`u^{\alpha/2-1}(1+u)^{(s-2k-1/2)/2}` together with Tonelli reduces its Sobolev norm to the
norms of the dilated filters.

For the Gaussian activation, substitute
$`\widehat\sigma(\omega)=\sqrt{2\pi}e^{-\omega^2/2}` in the pairing and evaluate
$`\int_{\mathbb R}|\omega|^\delta e^{-3\omega^2/2}\,\mathrm d\omega`
by the Gamma integral. For ReLU, its Fourier transform away from zero is
$`-\omega^{-2}`. When $`s>3/2`, the order condition gives $`\delta>5/2`, so
the origin-supported terms vanish against the Sobolev test and the remaining integral is
$`-(2\pi)^{-1}\int_{\mathbb R}|\omega|^{\delta-2}e^{-\omega^2}\,\mathrm d\omega`.
This is the stated negative, nonzero Gamma constant.
:::
