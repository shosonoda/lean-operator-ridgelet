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

With a Gaussian input weight and a homogeneous Gaussian mixture on the direction
parameter, the ridgelet transform on an infinite-dimensional Hilbert space keeps the
structure of the finite-dimensional theory. The admissibility constant is a
one-dimensional integral in which no dimension appears, the transform is injective with
a Plancherel identity on $`\mathcal E_\alpha`, and synthesis returns the target up to the
frame operator $`T_\alpha`, the correction induced by the weights, which is undone after
synthesis, before analysis, or on the coefficients. Targets with a spectral density are
integral networks with explicit coefficients; every continuous target is a compact-open
limit of such networks; and sampling the coefficient gives finite-width networks at the
rate $`N^{-1/2}` when the density is regular along rays and the activation is globally
Lipschitz. Weak reconstruction covers every non-polynomial tempered activation, and
ReLU, tanh, the Gaussian distribution function and the Gaussian activation satisfy all of
these conditions. The neural-operator layers of the examples are integral networks with
explicit parameter measures to which the finite-width bounds apply.

# Approximation rates and numerical implementation

{bpref "thm:5.10"}[] allows non-band-pass filters and a finite range
of coefficient moments. When $`s>5/2`, its second-moment conclusion connects to the
Hilbert-valued uniform approximation theorem.

The experiments in Section 8 support the predicted approximation rates on finite test
sets and check a closed-form transform independently. They also show a discretization
floor. Computing an integral coefficient, sampling a direction and representing that
direction with finitely many numbers remain distinct numerical tasks.

# Position among related results

The universality statement is of a type already available as an existence theorem:
compact-open density of networks with scalar ridge neurons holds on locally convex spaces
for every continuous non-polynomial activation, and global density on weighted spaces is
also known. What the ridgelet transform adds is the construction of the approximants: an
explicit coefficient for every target with a spectral density and every admissible
analysis filter, a Plancherel identity with an identified frame operator, and a sampling
argument that yields the finite-width rate and applies to the examples. The rate is a
Barron-type statement for a restricted class, consistent with the lower bounds for
Lipschitz operator classes. The transform differs from the ridgelet transform for Wiener
functionals in its atoms, its parameter measure, and its Plancherel identity on a single
space; the manuscript's Appendix F records these comparisons.

# Open problems

Natural next steps are quantitative control of the spectral approximation for regular
target classes, the cost of representing infinite-dimensional directions in a finite
computation, and extensions to operator activations and to input measures beyond the
Gaussian construction.
