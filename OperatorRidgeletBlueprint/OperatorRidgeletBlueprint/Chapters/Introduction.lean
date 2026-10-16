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

#doc (Manual) "Introduction" =>
%%%
file := "introduction"
%%%

We develop ridgelet analysis for neural networks with infinite-dimensional inputs.
The construction connects explicit integral representations to finite-width approximation
and uniform approximation on compact sets.

# From function inputs to network coefficients

Operator learning approximates nonlinear maps whose inputs, and sometimes outputs, are
functions. A basic model on a real Hilbert space $`H`, with outputs in $`Y`, is
$`f_N(x)=\sum_{j=1}^N v_j\sigma(\langle a_j,x\rangle-b_j)`.
Each direction $`a_j` is a linear measurement of the input. The question here is how to
choose the directions, biases and output coefficients from a target function.

An integral representation replaces the finite sum by
$`f(x)=S_\sigma[\Gamma](x)=\int_{H\times\mathbb R}\sigma(\langle a,x\rangle-b)\,\Gamma(\mathrm da,\mathrm db)`.
The finite scalar or vector measure $`\Gamma` encodes the representation. Its normalized
variation is a probability law for sampling neurons, and its polar density supplies their
output weights. Variation and parameter moments then control the approximation error.

A ridgelet transform sends a target to coefficients indexed by directions and biases.
The construction below is made directly on $`H`; it does not begin by selecting a
finite-dimensional input encoder. Universality of such networks is usually proved by
reduction to a finite-dimensional theorem, and direct infinite-dimensional versions and
Hilbert-input random-feature rates are known; those results establish existence or
sampling bounds without an analysis operator. The construction here supplies that
operator: an explicit coefficient formula, a norm identity and reconstruction, for the
full class of continuous non-polynomial activations of polynomial growth, from which
universality and finite-width rates follow.

# The integration problem and its resolution

An infinite-dimensional Hilbert space has no locally finite translation-invariant
analogue of Lebesgue measure. We use Gaussian input weights and a homogeneous mixture
of Gaussian direction measures to construct the integrals directly on that space.
This also resolves the dimension-dependent weight in the finite-dimensional
admissibility condition. The measure construction and Fourier identities are given
in Section 3, before the reconstruction and approximation theorems use them.

# Main results

The universality statement is of a type already known; the novelty lies in how the
approximants are obtained. The assumptions on filters and activations belong to the
individual statements.

* {bpref "thm:3.14"}[] proves the Plancherel identity, closed range and injectivity on
  the Hilbert space $`\mathcal E_\alpha`.
* {bpref "thm:4.5"}[] gives explicit coefficients for targets with a spectral density,
  including an absolutely convergent network integral under regularity along rays.
* {bpref "thm:4.8"}[] identifies the frame operator as the Riesz isomorphism and gives
  reconstruction, backprojection and inversion formulas.
* {bpref "thm:6.6"}[] proves finite total variation and parameter moments from
  regularity along rays, connecting representation to finite-width approximation.
* {bpref "thm:6.8"}[] gives constructive compact-open universality through spectral
  targets, with approximation rates for the resulting integral networks.

The frame operator $`T_\alpha` is the correction induced by the weights. Analysis
followed by synthesis gives $`C T_\alpha f`; applying $`C^{-1}T_\alpha^{-1}` recovers
$`f`. The correction can equivalently be made before analysis or on the coefficients.
Different admissible analysis filters give different coefficients for the same target, so
the representation is a family indexed by the filter.

# Scope of the construction

The coefficient formula is explicit once a spectral density is given. For an arbitrary
continuous target, the first step chooses a spectral approximation by Stone–Weierstrass
and smooth frequency bumps. Its variation and moments may depend on the approximation
accuracy. No uniform width–accuracy relation for all continuous targets, efficient
coefficient-computation algorithm or statistical learning guarantee follows.
Universality is proved in the compact-open topology, not globally on weighted
non-compact spaces, and the $`N^{-1/2}` rate is a Barron-type statement for targets whose
coefficient has finite variation and moments; it does not contradict the known lower
bounds for Lipschitz operator classes.

Every finite-width network factors through its finite family of input measurements.
The genuinely infinite-dimensional objects in the examples are the exact targets and
integral networks. Finite representations of the directions create a further error.

Reconstruction with a tempered distribution as the activation takes place in a dual space.
Ordinary integral networks use
continuous activations and appropriate moments. The explicit uniform rate additionally
requires global Lipschitz continuity and a second moment. General nonlinear operator
activations are outside this reconstruction theorem.

# Related work

Ridgelet analysis, developed by Murata, Candès and subsequent authors, relates ridge
functions to Fourier, Radon and wavelet analysis; its distributional extension admits
unbounded activations, and weighted Sobolev activation spaces provide continuous
synthesis pairings. Earlier Hilbert-space constructions integrate over a
finite-dimensional subspace.

Integration over an infinite-dimensional space with respect to a Gaussian measure is
classical: Fourier–Wiener transforms, Gaussian Radon transforms, and a ridgelet transform
for Wiener functionals whose atoms are generated by a functional on the Cameron–Martin
space and whose basic identity relates two Gaussian spaces of different variance rather
than reconstructing the target. Here the atoms are neurons, the direction measure is
homogeneous, and the Plancherel identity holds on a single space.

Universal approximation with infinite-dimensional inputs goes back to the approximation
of functionals; compact-open universality is known on Fréchet spaces with operator
activations, in $`L^p` of a Radon measure, for scalar ridge neurons on locally convex
spaces with every continuous non-polynomial activation, and globally on weighted spaces.
These are existence theorems; here the approximants are obtained from an explicit
coefficient, one for each admissible analysis filter.

Finite-width bounds by sampling a parameter distribution follow Barron and the
variation-norm viewpoint, with Hilbert-input, Banach-valued and encoder–decoder
versions. Here the sampling measure is the homogeneous measure $`\nu_\alpha`, the
coefficient is characterized by an analysis operator with a Plancherel identity and a
closed-range projection, and the uniform rate covers Hilbert-valued outputs. Lower bounds
exclude such rates for all Lipschitz operators; the rate here concerns a Barron-type
class. The manuscript's Appendix F expands these comparisons.

# Notation and organization

Unless otherwise stated, $`H` is an infinite-dimensional separable real Hilbert space,
$`Y` is a separable complex Hilbert space, and $`P,Q` are injective positive self-adjoint
trace-class operators. Functions are complex valued unless a real activation or output is
specified. The one-dimensional Fourier convention is
$`h^\sharp(\omega)=\int h(t)e^{-it\omega}\,\mathrm dt` and
$`h(t)=(2\pi)^{-1}\int h^\sharp(\omega)e^{it\omega}\,\mathrm d\omega`.
We use $`\sharp` for one-dimensional and partial bias transforms and
$`\widehat{\phantom f}` for spatial Fourier–Stieltjes transforms and torus
coefficients. Distributional pairings are bilinear.

The manuscript uses $`b` and $`\sigma`; the formal statements and the mathematical
nodes below use $`c=-b` and $`\beta`. They use the same spatial symbol $`F_Q` and often
$`G` for a spectral density $`g`. These are changes of coordinates and notation, not
changes in the network or theorem hypotheses.

Sections 2–7 develop the definitions, analysis, reconstruction, activations, approximation and
examples, with their prerequisites and proofs supplied before use. Section 8 reports
numerical experiments and Section 9 discusses computation and open questions. Appendix A
gives a kernel interpretation, B gives coefficient projections, C gives additional
approximation bounds, D compares finite-dimensional formulas and explains the dilation
obstruction, E gives numerical methods, and F is an extended overview of related work.

Each numbered result links to its Lean declarations. The $`L^2` clause of Theorem 5.10
and the closed-form reconstruction constants of Proposition 5.12 are carried in weaker
forms by the Lean statements. The formalization infrastructure is documented separately
after the manuscript chapters.
