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

We discuss what the representation and approximation results establish and identify
the remaining limitations in spectral approximation, computation and measure choices.

# Main results

The results give two complementary chains. For an admissible filter with constant $`C>0`,
analysis and synthesis give
$`f\xrightarrow{R_\rho}R_\rho f\xrightarrow{S_\rho}C T_\alpha f\xrightarrow{C^{-1}T_\alpha^{-1}}f`.
Backprojection gives
$`R_\rho f\xrightarrow{C^{-1}W_\rho^*}F_Qf\xrightarrow{\Delta_Q}f`, where
the Hermite inversion step is stated for $`f` in the core $`\mathcal D_\alpha`.

The admissibility constant is a one-dimensional Calderón-type integral with no dimension
parameter. The transform is an injective scaled isometry on $`\mathcal E_\alpha`,
and the frame operator is an isometric isomorphism to its dual. Targets with spectral
densities have explicit network coefficients. Every continuous target is a compact-open
limit of such networks, and regularity along rays together with a globally Lipschitz
activation gives an explicit $`N^{-1/2}` approximation rate.

The reconstruction formula permits any non-polynomial tempered distribution as the activation.
An absolutely convergent network integral requires a continuous representative of suitable
growth, and the explicit uniform approximation rate adds Lipschitz continuity. ReLU, tanh, the
Gaussian distribution function and the Gaussian activation satisfy the relevant conditions.
Periodic convolution and Dirichlet layers have explicit coefficient measures; Gaussian
activation also gives explicit transforms for these layers.

# Approximation rates and numerical implementation

{bpref "thm:5.10"}[] allows non-band-pass filters and a finite range
of coefficient moments. When $`s>5/2`, its second-moment conclusion connects to the
Hilbert-valued uniform approximation theorem.

The experiments in Section 8 support the predicted approximation rates on finite test
sets and check a closed-form transform independently. They also show a discretization
floor. Computing an integral coefficient, sampling a direction and representing that
direction with finitely many numbers remain distinct numerical tasks.

# Open problems

Further work includes an intrinsic description of the analysis space, quantitative
control of spectral approximation and coefficient cost for regular target classes,
and the cost of representing infinite-dimensional directions in finite computations.
Alternative coefficient discretizations may improve numerical implementation.
Extensions to more general operator activations and to input and direction measures
beyond the Gaussian construction are also natural questions.
