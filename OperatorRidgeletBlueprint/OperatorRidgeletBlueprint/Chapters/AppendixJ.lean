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

#doc (Manual) "Appendix J. Numerical experiments" =>
%%%
file := "appendix-j"
number := false
%%%

Three experiments illustrate the sampling step of {bpref "thm:6.5"}[] and
{bpref "thm:6.4"}[], and the explicit transforms in {bpref "ex:7.1"}[] and
{bpref "ex:7.4"}[]. The input spaces are $`\ell^2` and $`L^2(0,1)`,
represented numerically by finitely many coordinates. Varying that resolution tests
the sensitivity of the observed errors; these finite computations do not prove a
uniform-in-dimension theorem.

The experiments use seed 20260908. Errors are supremum errors over a test set of 100 or
200 points, averaged over independent trials. Slopes are least-squares fits in logarithmic
coordinates over widths $`N=4,8,\ldots,4096`.

# Experiment 1: ReLU with Gaussian random directions

This experiment illustrates {bpref "cor:7.3"}[]. On $`\ell^2`, set
$`Q=\operatorname{diag}(j^{-2})` and truncate to $`d=10,100,1000,10000` coordinates.
The test set consists of 200 points with coordinates $`x_j=u_j/j`, where the $`u_j`
are uniform on $`[-1,1]`. Compare
$`f_{\mathrm{ReLU},Q}(x)=\sqrt{\langle Qx,x\rangle/(2\pi)}` with
$`N^{-1}\sum_{j=1}^N\operatorname{ReLU}(\langle a_j,x\rangle)`, where
$`a_j\sim\mu_Q`, over 20 trials.

The observed mean supremum error decays approximately as $`N^{-1/2}` at every tested
resolution. The bound at $`N=4096` is 0.24, about twenty times the observed error,
so this comparison illustrates the rate rather than sharpness of its constant.

![Experiment 1: mean supremum error against network width, for four truncation dimensions](exp1.svg)

# Experiment 2: synthesis of the weighted Gaussian target

Use {bpref "ex:7.1"}[] with $`\alpha=1`,
$`P=Q=\operatorname{diag}(j^{-2})`, $`W=I`, and
$`\rho(t)=\mathrm{He}_4(t)e^{-t^2/2}`. Its Fourier transform is
$`\sqrt{2\pi}\,\omega^4e^{-\omega^2/2}`, and its admissibility constant is 6.
Although this filter is not band pass, the analyzed-target identity only needs
admissibility. Finite variation and the second parameter moment follow directly from
the explicit coefficient and the Gaussian decay estimate.

The coefficient is
$`\gamma_g(a,b)=D^{-1/2}\sqrt{2\pi}\,\phi_{1+\kappa_W(a)}^{(4)}(b)`, where
$`\phi_u` is the centered Gaussian density of variance $`u` and
$`D=\det(I+Q^{1/2}WQ^{1/2})`. The target $`6f_g`, representing $`6T_\alpha f_W`,
and the total variation $`V` are evaluated by quadrature. Conditional biases are
sampled by rejection from a mixture of Gaussian moment densities. Directions are
obtained by sampling–importance resampling from 200000 Gaussian-mixture proposals,
with effective sample sizes between 2800 and 9700.

For $`d=10,100,1000` and the test set from Experiment 1, ten trials compare
$`f_N=(V/N)\sum_j\operatorname{sgn}(\gamma_g(\theta_j))\rho(\langle a_j,\cdot\rangle-b_j)`
with $`6f_g`, whose supremum on the test set is about 12.5. The error again decays
approximately as $`N^{-1/2}` across the tested resolutions.

![Experiment 2: sampled synthesis error for the Gaussian target at three truncation dimensions](exp2.svg)

# Experiment 3: the Dirichlet operator layer

Use {bpref "ex:7.6"}[] with Gaussian activation and observable $`\varphi=1`.
For the Dirichlet Green's function $`g`, the output weight is
$`w(y)=\int_0^1g(y,t)\,\mathrm dt=1-\cosh(y-1/2)/\cosh(1/2)>0` and
$`V=\int_0^1w(y)\,\mathrm dy=1-2\tanh(1/2)\approx0.0758`.
Use $`d=64,512,4096` midpoint nodes and 100 test inputs
$`x=\sum_{n\le30}(u_n/n)e_n`, with independent uniform $`u_n\in[-1,1]`.

For sampling, compare
$`f_N(x)=(V/N)\sum_j e^{-\langle g(y_j,\cdot),x\rangle^2/2}`, with
$`y_j\sim w/V`, against the integral layer over 20 trials. At resolutions 512 and
4096 the error follows $`N^{-1/2}`. At resolution 64 it levels off near $`10^{-5}`,
the quadrature error of that reference discretization.

![Experiment 3: Dirichlet-layer sampling error, including the coarse-resolution quadrature floor](exp3.svg)

For an independent transform check, use the filter from Experiment 2,
$`a(t)=\sqrt2\sin(\pi t)+(\sqrt2/2)\sin(3\pi t)`, and biases
$`b=0,-1/2,-1`. A Monte Carlo estimate with 200000 Gaussian inputs and
Karhunen–Loève truncations $`d'=8,64,512` agrees with the closed-form values within
about three standard errors:

:::table +header
*
  * Method
  * Bias 0
  * Bias −1/2
  * Bias −1
*
  * Closed form
  * 0.18119
  * 0.09062
  * −0.06298
*
  * Monte Carlo, 8 modes
  * 0.18111
  * 0.09107
  * −0.06258
*
  * Monte Carlo, 64 modes
  * 0.18106
  * 0.09041
  * −0.06303
*
  * Monte Carlo, 512 modes
  * 0.18077
  * 0.09072
  * −0.06258
*
  * Standard error
  * 0.00013
  * 0.00023
  * 0.00018
:::

# Approximation-error summary

The table gives the mean supremum error at widths 4 and 4096, together with the
fitted logarithmic slope. The dashed lines in the figures are proportional to
$`N^{-1/2}`.

:::table +header
*
  * Experiment
  * Resolution
  * Error, width 4
  * Error, width 4096
  * Slope
*
  * 1: ReLU
  * 10
  * 0.41
  * 0.011
  * −0.53
*
  * 1: ReLU
  * 100
  * 0.37
  * 0.012
  * −0.50
*
  * 1: ReLU
  * 1000
  * 0.42
  * 0.011
  * −0.51
*
  * 1: ReLU
  * 10000
  * 0.32
  * 0.010
  * −0.50
*
  * 2: Gaussian target
  * 10
  * 11.9
  * 0.46
  * −0.47
*
  * 2: Gaussian target
  * 100
  * 11.6
  * 0.43
  * −0.48
*
  * 2: Gaussian target
  * 1000
  * 12.8
  * 0.36
  * −0.52
*
  * 3: Dirichlet layer
  * 64
  * 0.00010
  * 0.000012
  * −0.31
*
  * 3: Dirichlet layer
  * 512
  * 0.00014
  * 0.0000036
  * −0.53
*
  * 3: Dirichlet layer
  * 4096
  * 0.000089
  * 0.0000029
  * −0.50
:::

These experiments illustrate approximation rates rather than computational cost, which
grows with the input resolution through the inner products. Similar errors across the
tested resolutions occur only once discretization error is sufficiently small. Finite
test sets, quadrature and importance resampling remain numerical approximations; the
analytic theorems provide the infinite-dimensional guarantees.
