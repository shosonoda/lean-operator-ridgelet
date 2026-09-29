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

#doc (Manual) "Appendix I. Explicit admissible filters" =>
%%%
file := "appendix-i"
number := false
%%%

A nonzero smooth Fourier filter supported away from zero is admissible for every
positive homogeneity exponent. The Mexican-hat example shows that admissibility alone does
not imply band-pass support. The last result constructs non-band-pass filters for the
integral representation under Sobolev conditions, with explicit moment conditions.

:::definition "aux:explicit-filters" (lean := "OperatorRidgelet.Filters.bump, OperatorRidgelet.Filters.bandPassHat, OperatorRidgelet.Filters.bandPassFun, OperatorRidgelet.Filters.bandPass, OperatorRidgelet.Filters.mexicanHatFun, OperatorRidgelet.Filters.mexicanHat") (uses := "aux:conventions")
With the bump $`\eta(u)=\exp(-1/(1-u^2))` for $`|u|<1` and $`0` otherwise, the band-pass
filter $`\rho_{\mathrm{bp}}` is the real even Schwartz function with
$`\widehat\rho_{\mathrm{bp}}(\omega)=-\eta(2|\omega|-3)`, obtained by Fourier inversion; the
Mexican hat is $`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}`. Both are taken as Schwartz maps by
choice, with junk value $`0` should the explicit function fail to be Schwartz.
:::

:::example_ "ex:I.1" (lean := "OperatorRidgelet.Paper.ex_I_1_i, OperatorRidgelet.Paper.ex_I_1_ii, OperatorRidgelet.Paper.ex_I_1_iii, OperatorRidgelet.Paper.ex_I_1_iv, OperatorRidgelet.Paper.ex_I_1_v, OperatorRidgelet.Paper.ex_I_1_vi, OperatorRidgelet.Paper.ex_I_1_vii, OperatorRidgelet.Paper.ex_I_1_viii, OperatorRidgelet.Paper.ex_I_1_ix, OperatorRidgelet.Paper.ex_I_1_x") (uses := "aux:explicit-filters, def:3.2, aux:conventions")
$`\widehat\rho_{\mathrm{bp}}` is smooth (i), nonpositive (ii), nonzero (iii), and supported in
$`\{1\le|\omega|\le2\}` (iv), so $`\rho_{\mathrm{bp}}\in\mathcal S(\mathbb R)` is real (v)
and even (vi) with the prescribed Fourier transform (vii), satisfies the band-pass condition
(viii), and is $`\alpha`-admissible for every $`\alpha>0` (ix); multiplying by
$`((\!(\rho_{\mathrm{bp}},\rho_{\mathrm{bp}})\!)_\alpha)^{-1/2}` normalizes the admissibility constant to one (x).
The sign makes it admissible for ReLU synthesis in the sense of {bpref "cor:5.3"}[].
:::

:::proof "ex:I.1"
The bump and all its derivatives vanish at $`|u|=1`, the support stays away from
$`\omega=0`, Fourier inversion maps $`C_c^\infty` into $`\mathcal S`, even real Fourier data
give an even real inverse, and on the compact support $`|\omega|^{-\alpha}` is bounded above
and below.
:::

:::example_ "ex:I.2" (lean := "OperatorRidgelet.Paper.ex_I_2_i, OperatorRidgelet.Paper.ex_I_2_ii, OperatorRidgelet.Paper.ex_I_2_iii, OperatorRidgelet.Paper.ex_I_2_iv, OperatorRidgelet.Paper.ex_I_2_v, OperatorRidgelet.Paper.ex_I_2_vi") (uses := "aux:explicit-filters, def:3.2, aux:conventions")
$`\rho_{\mathrm{MH}}(t)=(1-t^2)e^{-t^2/2}` is a Schwartz function (i) with
$`\widehat\rho_{\mathrm{MH}}(\omega)=\sqrt{2\pi}\,\omega^2e^{-\omega^2/2}` (ii). It is
$`\alpha`-admissible exactly for $`0<\alpha<5` (iii), with
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\Gamma((5-\alpha)/2)` (iv) and
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_1=1` (v). It is not band pass (vi).
When $`0<\alpha<5`, {bpref "thm:3.11"}[], {bpref "thm:4.3"}[] and part (ii) of
{bpref "thm:4.2"}[] apply. The band-pass statements in part (iii) of
{bpref "thm:4.2"}[] and in {bpref "thm:5.2"}[] do not apply to this filter.
:::

:::proof "ex:I.2"
With $`g(t)=e^{-t^2/2}`, $`\rho_{\mathrm{MH}}=-g''` and the differentiation rule gives the
Fourier transform; then
$`(\!(\rho_{\mathrm{MH}},\rho_{\mathrm{MH}})\!)_\alpha=\int_{\mathbb R}|\omega|^{4-\alpha}e^{-\omega^2}\mathrm d\omega=\Gamma((5-\alpha)/2)`,
convergent at zero exactly when $`\alpha<5`.
:::

# I.1 Examples of filters for the reconstruction formula
%%%
number := false
%%%

Take $`\widehat\rho(\omega)=\omega^{2k}e^{-\omega^2}` and
$`G(\xi)=e^{-\|\xi\|^2}v`. The condition $`2k>\alpha+2s-1/2` gives the required
ray estimates. The choice $`\alpha=1`, $`s=3`, $`k=4` permits a second parameter
moment and nonzero pairings for both Gaussian and ReLU synthesis.

:::proposition "prop:I.3" (lean := "OperatorRidgelet.gaussDerivFilter, OperatorRidgelet.gaussTarget, OperatorRidgelet.gaussRayCoefficient, OperatorRidgelet.gaussSobolevRay, OperatorRidgelet.Paper.prop_I_3_i, OperatorRidgelet.Paper.prop_I_3_ii, OperatorRidgelet.Paper.prop_I_3_iii, OperatorRidgelet.Paper.prop_I_3_iv, OperatorRidgelet.Paper.prop_I_3_v, OperatorRidgelet.Paper.prop_I_3_vi, OperatorRidgelet.Paper.prop_I_3_vii, OperatorRidgelet.Paper.prop_I_3_viii, OperatorRidgelet.Paper.prop_I_3_ix") (uses := "thm:5.6, def:3.2, aux:conventions")
Under the input-space and sigma-finite Borel measure hypotheses of {bpref "thm:5.6"}[],
let $`\nu` be homogeneous of degree $`\alpha>0` and finite on the unit ball. Fix $`s>1/2` and an
integer $`k\ge1` with $`2k>\alpha+2s-1/2`, and let
$`\widehat\rho_k(\omega)=\omega^{2k}e^{-\omega^2}`, $`g(\xi)=e^{-\|\xi\|^2}v`. Then $`\rho_k` is
a real Schwartz filter (i) that is not band pass (ii) but is $`\alpha`-admissible for
$`\alpha<4k+1` (iii). The homogeneous moments $`\int(1+\|a\|^2)^{-d/2}\mathrm d\nu` are finite
for $`d>\alpha` (iv); the coefficient $`\gamma_g` is jointly measurable (v), each function
$`h_a(\omega)=\widehat\rho_k(-\omega)g(\omega a)` lies in $`H^s_\omega` (vi), and
$`\mathfrak B_s(\rho_k,g)<\infty` (vii). The Sobolev test $`q_{\alpha,\rho_k}` lies in
$`H^s_\omega` (viii). Hence {bpref "thm:5.6"}[] applies to this filter for
every continuous activation of growth order $`p<s-1/2` (ix).

Put $`\delta=2k-\alpha`. For $`\sigma(t)=e^{-t^2/2}`, the reconstruction constant is
$`(\!(\sigma,\rho_k)\!)_\alpha=\Gamma((\delta+1)/2)(3/2)^{-(\delta+1)/2}/\sqrt{2\pi}>0`.
If $`s>3/2`, ReLU also satisfies the hypotheses and
$`(\!(\operatorname{ReLU},\rho_k)\!)_\alpha=-(2\pi)^{-1}\Gamma((\delta-1)/2)\ne0`.
The unit-ball finiteness hypothesis holds for the homogeneous Gaussian mixtures on the
infinite-dimensional Hilbert space used in the main construction.
:::

The two closed-form constants are part of the manuscript statement. The associated
Lean statements retain their Sobolev-pairing formulations; they do not assert these
closed-form evaluations.

:::proof "prop:I.3" (uses := "lem:C.3")
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
