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

#doc (Manual) "Discussion" =>
%%%
file := "discussion"
%%%

# What has been shown

The results give two complementary chains. For an admissible filter with constant $`C>0`,
analysis and synthesis give
$`f\xrightarrow{R_\rho}R_\rho f\xrightarrow{S_\rho}C T_\alpha f\xrightarrow{C^{-1}T_\alpha^{-1}}f`.
Backprojection gives
$`R_\rho f\xrightarrow{C^{-1}\Lambda_\rho}F_Qf\xrightarrow{\Delta_Q}f`, where
the Hermite inversion step is stated for $`f` in the core $`\mathcal D_\alpha`.

The admissibility constant is a one-dimensional Calderón-type integral with no dimension
parameter. The transform is an injective scaled isometry on $`\mathcal E_\alpha`,
and the frame operator is an isometric isomorphism to its dual. Targets with spectral
densities have explicit network coefficients. Every continuous target is a compact-open
limit of such networks, and regularity along rays together with a globally Lipschitz
activation gives an explicit $`N^{-1/2}` sampling rate.

Tempered reconstruction permits any non-polynomial tempered activation. Absolute
integral-network synthesis requires a continuous representative of suitable growth,
and the explicit uniform sampling estimate adds Lipschitz continuity. ReLU, tanh, the
Gaussian distribution function and the Gaussian activation satisfy the relevant conditions.
Periodic convolution and Dirichlet layers have explicit coefficient measures; Gaussian
activation also gives explicit transforms for these layers.

# Absolute synthesis and computation

{bpref "thm:5.6"}[] allows non-band-pass filters and a finite range
of coefficient moments. When $`s>5/2`, its second-moment conclusion connects to the
Hilbert-valued uniform sampling theorem.

The experiments in Appendix J support the predicted sampling behavior on finite test
sets and check a closed-form transform independently. They also show a discretization
floor. Computing an integral coefficient, sampling a direction and representing that
direction with finitely many numbers remain distinct numerical tasks.

# What remains open

* *An intrinsic description of the Hilbert space.* In finite dimension its norm is
  a homogeneous Sobolev norm of a Gaussian-weighted density. A comparable description
  through a Gaussian Sobolev or Wiener-chaos scale in infinite dimension is open.
* *General operator activations.* The reconstruction theory treats scalar activations
  composed with linear functionals and their rank-one lifts. General nonlinear maps
  $`\Sigma:H\to H` would require an appropriate representation and nondegeneracy condition.
* *Rates for spectral approximation.* The first step of {bpref "thm:6.5"}[] has no
  quantitative rate without regularity assumptions on the target. Function classes
  controlling the coefficient variation would make this step quantitative.
* *Coefficient-space discretization.* Averaged coefficient observations and stronger
  coefficient norms may complement Monte Carlo sampling. A coorbit approach requires
  verification of its observation and discretization hypotheses in this setting.
* *The cost of directions.* Width alone does not measure the cost of storing
  $`a_j\in H`. Kernel translates and Green's functions offer structured direction
  families for operator layers; Gaussian directions require separate tail estimates.
