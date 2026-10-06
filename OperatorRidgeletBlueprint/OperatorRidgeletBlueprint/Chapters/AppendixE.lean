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

#doc (Manual) "Appendix E. Numerical methods and additional results" =>
%%%
file := "appendix-e"
number := false
%%%

This appendix describes the numerical procedures behind Section 8. It records how
parameters are drawn, how integrals and function-space inputs are discretized, and how
the reported errors are measured. The figures and result tables are in Section 8.

# E.1 Reproduction and error measurement
%%%
number := false
%%%

All experiments use seed 20260908. Errors are supremum errors over 100 or 200 test
points, averaged over independent trials. Least-squares fits of log error against
log width use $`N=4,8,\ldots,4096`. The dashed reference lines show $`N^{-1/2}`.
These are finite test-set errors; they do not certify the supremum over a compact set.
Within each trial the same sequence of neurons is accumulated as width increases.
The test set is fixed within each experiment and resolution. The supplementary
`experiments.py` script reproduces the reported results with the fixed seed.

# E.2 Gaussian directions and coefficient measures
%%%
number := false
%%%

Experiment 1 uses $`Q=\operatorname{diag}(j^{-2})`, truncated to
$`d=10,100,1000,10000` coordinates. Its 200 test inputs have coordinates $`x_j=u_j/j`
with independent $`u_j` uniform on $`[-1,1]`. Gaussian directions with covariance $`Q`
and zero bias give the ReLU networks. Errors are averaged over 20 trials.

Experiment 2 uses $`\alpha=1`, $`P=Q=\operatorname{diag}(j^{-2})`, $`W=I` and
$`\rho(t)=\mathrm{He}_4(t)e^{-t^2/2}`. Its coefficient is
$`\gamma_g(a,b)=D^{-1/2}\sqrt{2\pi}\,\phi_{1+\kappa_W(a)}^{(4)}(b)`, where
$`\phi_u` is the centered Gaussian density of variance $`u` and
$`D=\det(I+Q^{1/2}WQ^{1/2})`. Quadrature evaluates the total variation and the target
$`6f_g`. Conditional biases are drawn by rejection from a mixture of Gaussian moment
densities. Sampling–importance resampling uses 200000 Gaussian-mixture proposals, with
effective sample sizes between 2800 and 9700. Ten trials at each of
$`d=10,100,1000` use 100 test inputs drawn by the same rule as Experiment 1.
Directions are drawn with replacement from the weighted pool, approximating the
continuous direction law. The pool is reused across trials at each resolution, so
trial variation is conditional on that pool and does not measure its approximation error.
The conditional bias law is exact: with $`u=1+\kappa_W(a)` and $`b=\sqrt u\,z`,
its density is $`|\mathrm{He}_4(z)|\phi_1(z)/m_4`. The proposal density is
$`(z^4+6z^2+3)\phi_1(z)/12`, accepted with probability
$`|\mathrm{He}_4(z)|/(z^4+6z^2+3)`. The code uses $`c=-b`; symmetry of the bias
density and its sign factor preserves the synthesis integral.

# E.3 Dirichlet layer and transform verification
%%%
number := false
%%%

Experiment 3 uses $`d=64,512,4096` midpoint nodes and 100 test inputs
$`x=\sum_{n\le30}(u_n/n)e_n` with independent uniform $`u_n\in[-1,1]`.
With the Dirichlet Green's function $`g` and observable 1, the parameter law is
$`w(y)\,\mathrm dy/V`, where $`w(y)=1-\cosh(y-1/2)/\cosh(1/2)` and
$`V=1-2\tanh(1/2)`. The networks approximate the integral layer over 20 trials.
Midpoint quadrature uses weight $`1/d`. Draws from $`w/V` invert a cumulative
distribution computed by the trapezoidal rule on 20001 uniform grid points with
linear interpolation; each Green direction is then evaluated on the input grid.
The coarsest quadrature produces the error floor reported in Section 8.

For the independent transform check, use the filter from Experiment 2,
$`a(t)=\sqrt2\sin(\pi t)+(\sqrt2/2)\sin(3\pi t)` and biases $`b=0,-1/2,-1`.
Monte Carlo integration over 200000 Gaussian inputs uses Karhunen–Loève truncations
$`d'=8,64,512`. The comparisons and standard errors are reported in Section 8.
The closed-form transform uses 2048 midpoints for inner products and 400 for the
outer integral. Gaussian draws have covariance eigenvalues
$`\lambda_n=(1+\pi^2n^2)^{-1}` and are evaluated on the same 2048-point grid.
The standard error is the empirical standard deviation of the integrand divided by
the square root of the number of draws. This check at the specified direction and
biases does not eliminate quadrature error or Gaussian-input truncation error.
