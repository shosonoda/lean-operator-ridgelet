import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.GaussianWeighted

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Gaussian-weighted ridgelet transform" =>
%%%
file := "gaussian-weighted-transform"
%%%

This chapter states the constructions and the main theorems of the manuscript's Gaussian-weighted
ridgelet transform. The input variable carries a Gaussian weight, the parameter variable carries a
$`\sigma`-finite measure that is homogeneous of a degree $`\alpha>0` unrelated to any dimension,
and the bias carries Lebesgue measure. The spectral variable is never dilated.

Every theorem in this chapter is stated in Lean with its proof still `sorry`, so that the
formalization status of the new section is visible in the dependency graph and the summary. The
definitions are complete; the analytic content is the remaining work.

# The two Fourier transforms

:::definition "gauss-ridgelet:character" (lean := "OperatorRidgelet.GaussianWeighted.character")
The analysis character is $`x\mapsto e^{-i\langle x,\xi\rangle}`.
:::

:::definition "gauss-ridgelet:gauss-fourier" (lean := "OperatorRidgelet.GaussianWeighted.gaussFourier") (uses := "gauss-ridgelet:character")
The Gaussian-weighted Fourier transform is
$`\mathcal Gf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu(\mathrm dx)`, that is the
Fourier--Stieltjes transform of the complex measure $`f\mu` evaluated at $`-\xi`.
:::

:::theorem "gauss-ridgelet:gauss-fourier-one" (lean := "OperatorRidgelet.GaussianWeighted.gaussFourier_one") (uses := "gauss-ridgelet:gauss-fourier")
On the constant function the analysis map is the characteristic functional of the weight:
$`\mathcal G\mathbf 1(\xi)=\widehat\mu(-\xi)`.
:::

:::definition "gauss-ridgelet:filter-fourier" (lean := "OperatorRidgelet.GaussianWeighted.filterFourier")
The one-dimensional filter transform is
$`\widehat\rho(\omega)=\int_{\mathbb R}\rho(t)e^{-i\omega t}\,\mathrm dt`.
:::

# Homogeneous reference measures

:::definition "gauss-ridgelet:homogeneous" (lean := "OperatorRidgelet.GaussianWeighted.IsHomogeneous")
A measure on $`H` is homogeneous of degree $`\alpha` when
$`(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu` for every $`\omega\ne0`. On $`\mathbb R^m` Lebesgue
measure is homogeneous of degree $`m`; the exponent $`-\alpha` is exactly the Jacobian factor
$`|\omega|^{-m}` of the classical admissibility constant.
:::

:::theorem "gauss-ridgelet:homogeneous-exists" (lean := "OperatorRidgelet.GaussianWeighted.exists_isHomogeneous_sFinite") (uses := "gauss-ridgelet:homogeneous")
For every $`\alpha>0` there is a nonzero $`\sigma`-finite measure on $`H` homogeneous of degree
$`\alpha`. The manuscript constructs the Gaussian mixture
$`\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)\,s^{\alpha/2-1}\,\mathrm ds` with $`P` injective,
positive and trace class. Finiteness on balls uses the Gaussian small-ball estimate, and it is
there that infinite dimension enters: every $`\alpha>0` is admissible, whereas on
$`\mathbb R^m` the mixture converges only for $`\alpha<m`.
:::

:::theorem "gauss-ridgelet:homogeneous-full-support" (lean := "OperatorRidgelet.GaussianWeighted.exists_isHomogeneous_sFinite_support") (uses := "gauss-ridgelet:homogeneous-exists")
The homogeneous mixture charges every nonempty open set, because the topological support of a
centred Gaussian measure is the closure of its Cameron--Martin space and $`P` is injective.
:::

:::theorem "gauss-ridgelet:homogeneous-change-of-variables" (lean := "OperatorRidgelet.GaussianWeighted.isHomogeneous_map_smul") (uses := "gauss-ridgelet:homogeneous")
Homogeneity gives
$`\int_HF(\omega a)\,\nu(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu`.
This is the only substitution performed in the parameter variable, and it is why no measure is
required to be absolutely continuous with respect to $`\nu`.
:::

# The transform

:::definition "gauss-ridgelet:ridgelet" (lean := "OperatorRidgelet.GaussianWeighted.ridgelet")
The Gaussian-weighted ridgelet transform is
$`R_\rho[f](a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu(\mathrm dx)`. No reference measure on
$`H` other than the Gaussian weight occurs, so the transform is defined for every
$`f\in L^2(H,\mu)` with no further hypothesis.
:::

:::definition "gauss-ridgelet:parameter-measure" (lean := "OperatorRidgelet.GaussianWeighted.parameterMeasure") (uses := "gauss-ridgelet:homogeneous")
The parameter measure is $`\nu\otimes\mathrm dc` on $`H\times\mathbb R`.
:::

:::definition "gauss-ridgelet:admissible-filter" (lean := "OperatorRidgelet.GaussianWeighted.IsAdmissibleFilter") (uses := "gauss-ridgelet:filter-fourier")
A filter is admissible when $`\widehat\rho` is smooth and compactly supported away from the
origin. Support away from zero makes every admissibility constant absolutely convergent and lets
the activation be merely locally integrable on the frequency side, which is what admits ReLU.
:::

:::definition "gauss-ridgelet:admissibility-constant" (lean := "OperatorRidgelet.GaussianWeighted.admissibilityConst") (uses := "gauss-ridgelet:filter-fourier")
The admissibility constant is
$`C^{(\alpha)}_{\rho_1,\rho_2}=(2\pi)^{-1}\int_{\mathbb R}\widehat{\rho_1}(\omega)\overline{\widehat{\rho_2}(\omega)}|\omega|^{-\alpha}\,\mathrm d\omega`.
For $`\alpha=1` it is the Calder\'on condition of the one-dimensional wavelet transform, and no
dimension occurs in it.
:::

:::theorem "gauss-ridgelet:fourier-slice" (lean := "OperatorRidgelet.GaussianWeighted.integral_ridgelet_mul_character") (uses := "gauss-ridgelet:ridgelet, gauss-ridgelet:gauss-fourier, gauss-ridgelet:admissible-filter")
Fourier slice:
$`\int_{\mathbb R}R_\rho[f](a,c)e^{-i\omega c}\,\mathrm dc=\widehat\rho(\omega)\,\mathcal Gf(-\omega a)`.
This single computation carries the Plancherel identity, the null-space theorem and the inversion
formula.
:::

# The energy form and the Plancherel identity

:::definition "gauss-ridgelet:energy-inner" (lean := "OperatorRidgelet.GaussianWeighted.energyInner") (uses := "gauss-ridgelet:gauss-fourier, gauss-ridgelet:homogeneous")
The energy inner product is
$`\langle f,g\rangle_{\mathfrak E}=\int_H\mathcal Gf\,\overline{\mathcal Gg}\,\mathrm d\nu`.
:::

:::definition "gauss-ridgelet:energy-space" (lean := "OperatorRidgelet.GaussianWeighted.MemEnergySpace") (uses := "gauss-ridgelet:energy-inner")
The energy space consists of the $`L^2(H,\mu)` functions whose analysis map is square integrable
against $`\nu`.
:::

:::theorem "gauss-ridgelet:energy-space-gaussian-decay" (lean := "OperatorRidgelet.GaussianWeighted.memEnergySpace_of_gaussian_decay") (uses := "gauss-ridgelet:energy-space, gauss-ridgelet:homogeneous-exists")
Gaussian decay of the analysis map implies membership in the energy space. In the manuscript this
follows from $`\int_He^{-t\langle Q\xi,\xi\rangle}\,\mathrm d\nu_\alpha<\infty`, valid for every
$`t>0` and every $`\alpha>0`.
:::

:::theorem "gauss-ridgelet:plancherel" (lean := "OperatorRidgelet.GaussianWeighted.plancherel") (uses := "gauss-ridgelet:fourier-slice, gauss-ridgelet:homogeneous-change-of-variables, gauss-ridgelet:admissibility-constant, gauss-ridgelet:energy-inner, gauss-ridgelet:parameter-measure")
Plancherel identity:
$`\langle R_{\rho_1}[f],R_{\rho_2}[g]\rangle_{L^2(\lambda_\alpha)}=C^{(\alpha)}_{\rho_1,\rho_2}\langle f,g\rangle_{\mathfrak E}`.
In finite dimension, with $`\nu` Lebesgue and $`\alpha=m`, this reduces to the classical ridgelet
Plancherel formula; the only change in infinite dimension is that the right-hand side is a
weighted energy rather than an $`L^2` inner product.
:::

:::theorem "gauss-ridgelet:ridgelet-memLp" (lean := "OperatorRidgelet.GaussianWeighted.memLp_ridgelet") (uses := "gauss-ridgelet:plancherel")
The transform of an energy-space element is square integrable on the parameter space, with norm
given by the Plancherel identity.
:::

# Null space and inversion

:::theorem "gauss-ridgelet:gauss-fourier-injective" (lean := "OperatorRidgelet.GaussianWeighted.gaussFourier_injective") (uses := "gauss-ridgelet:gauss-fourier")
The analysis map is injective. A finite complex measure on a separable Hilbert space is determined
by its characteristic functional, so $`\mathcal Gf\equiv0` forces $`f=0`.
:::

:::theorem "gauss-ridgelet:ridgelet-injective" (lean := "OperatorRidgelet.GaussianWeighted.injective_ridgelet") (uses := "gauss-ridgelet:fourier-slice, gauss-ridgelet:gauss-fourier-injective, gauss-ridgelet:homogeneous-full-support, gauss-ridgelet:homogeneous-change-of-variables")
The Gaussian-weighted ridgelet transform has trivial null space. Continuity of $`\mathcal Gf` and
full support of $`\nu` upgrade almost-everywhere vanishing to identical vanishing, and uniqueness
of characteristic functionals then gives $`f=0`.
:::

:::theorem "gauss-ridgelet:inversion" (lean := "OperatorRidgelet.GaussianWeighted.gaussFourier_eq_of_ridgelet") (uses := "gauss-ridgelet:fourier-slice")
Inversion: the analysis map is recovered from the ridgelet coefficients along any ray, that is for
any factorization $`\xi=-\omega a`. The non-uniqueness of that factorization is exactly the
redundancy of the transform, and equality of the resulting expressions characterizes the range.
:::

:::definition "gauss-ridgelet:de-gaussianized" (lean := "OperatorRidgelet.GaussianWeighted.deGaussianized") (uses := "gauss-ridgelet:gauss-fourier")
The de-Gaussianized analysis map is
$`G(\xi)=e^{\langle Q\xi,\xi\rangle/2}\mathcal Gf(\xi)`.
:::

:::theorem "gauss-ridgelet:de-gaussianized-determines" (lean := "OperatorRidgelet.GaussianWeighted.deGaussianized_determines") (uses := "gauss-ridgelet:de-gaussianized")
The de-Gaussianized analysis map determines the target. Along every ray it is entire, its Taylor
coefficients are the Wick moments of the target, and the Wick powers are total in $`L^2(H,\mu)`.
This is the inversion of the analysis map.
:::

# The frame operator

:::definition "gauss-ridgelet:frame-operator" (lean := "OperatorRidgelet.GaussianWeighted.frameOperator") (uses := "gauss-ridgelet:gauss-fourier, gauss-ridgelet:homogeneous")
The frame operator is $`T_\alpha f=\mathcal F\bigl((\mathcal Gf)\nu\bigr)`, that is
$`\mathcal G^*\mathcal G`.
:::

:::theorem "gauss-ridgelet:frame-operator-riesz" (lean := "OperatorRidgelet.GaussianWeighted.frameOperator_eq_energyInner") (uses := "gauss-ridgelet:frame-operator, gauss-ridgelet:energy-inner")
The frame operator represents the energy form, hence it is the Riesz isomorphism of the energy
space onto its dual, and reconstruction is the inverse Riesz map. Because $`\nu` is infinite the
operator is unbounded on $`L^2(H,\mu)`, and that gap is the exact location of the ill-posedness.
:::

:::theorem "gauss-ridgelet:synthesis-composition" (lean := "OperatorRidgelet.GaussianWeighted.synthesis_comp_ridgelet") (uses := "gauss-ridgelet:plancherel, gauss-ridgelet:frame-operator-riesz")
Analysis followed by the adjoint of a second analysis is the admissibility constant times the
frame operator. This is the synthesis form of the Plancherel identity.
:::

# The reproducing formula

:::definition "gauss-ridgelet:bias-fourier" (lean := "OperatorRidgelet.GaussianWeighted.biasFourier")
The bias-Fourier transform of a coefficient function.
:::

:::definition "gauss-ridgelet:ray-average" (lean := "OperatorRidgelet.GaussianWeighted.rayAverage") (uses := "gauss-ridgelet:bias-fourier, gauss-ridgelet:filter-fourier, gauss-ridgelet:homogeneous")
The ray average
$`\Lambda^{(\alpha)}_\rho[\gamma](\xi)=(2\pi)^{-1}\int_{\mathbb R}\overline{\widehat\rho(\omega)}|\omega|^{-\alpha}\widehat\gamma(-\xi/\omega,\omega)\,\mathrm d\omega`
averages the inversion over every factorization $`\xi=-\omega a` instead of choosing one ray. It is
the analogue of the filtered backprojection of the Radon inversion formula.
:::

:::theorem "gauss-ridgelet:ray-average-adjoint" (lean := "OperatorRidgelet.GaussianWeighted.inner_rayAverage") (uses := "gauss-ridgelet:ray-average, gauss-ridgelet:fourier-slice, gauss-ridgelet:homogeneous-change-of-variables")
The ray average is the adjoint of the transform: pairing a coefficient function with a transform on
the parameter side equals pairing its ray average with the analysis map on the spectral side.
:::

:::theorem "gauss-ridgelet:reproducing-formula" (lean := "OperatorRidgelet.GaussianWeighted.rayAverage_ridgelet") (uses := "gauss-ridgelet:ray-average-adjoint, gauss-ridgelet:admissibility-constant")
The ray average inverts the transform exactly,
$`\Lambda^{(\alpha)}_\rho[R_\rho[f]]=C^{(\alpha)}_{\rho,\rho}\,\mathcal Gf`. Combined with the
inversion of the analysis map this is the reconstruction formula
$`\Delta\bigl[C^{-1}\Lambda^{(\alpha)}_\rho[R_\rho[f]]\bigr]=f`, with two explicit filters: a
one-dimensional averaging filter on the coefficients and the Gaussian inversion on the spectral
side. It is more stable than reading a single ray, and it is the form to implement.
:::

:::definition "gauss-ridgelet:range-projection" (lean := "OperatorRidgelet.GaussianWeighted.rangeProjection") (uses := "gauss-ridgelet:ray-average")
The orthogonal projection onto the closure of the range of the transform, written on the
bias-Fourier side.
:::

:::theorem "gauss-ridgelet:reproducing-identity" (lean := "OperatorRidgelet.GaussianWeighted.rangeProjection_ridgelet") (uses := "gauss-ridgelet:range-projection, gauss-ridgelet:reproducing-formula")
The transform is a fixed point of the range projection. This reproducing identity characterizes the
range, and it is the redundancy of the continuous frame: the range is a reproducing kernel Hilbert
space inside $`L^2(\lambda_\alpha)` whose kernel is the projection.
:::

# General weights

:::theorem "gauss-ridgelet:energy-space-one-iff" (lean := "OperatorRidgelet.GaussianWeighted.memEnergySpace_one_iff") (uses := "gauss-ridgelet:energy-space, gauss-ridgelet:gauss-fourier-one")
The energy space contains the constants exactly when the characteristic functional of the weight is
square integrable against the reference measure.

This is the only place in the theory where a general weight can fail. The Plancherel identity, the
reproducing formula and the null-space theorem are all stated for an arbitrary probability weight,
and none of them uses Gaussianity; the only statement that does is the inversion of the analysis
map, which goes through the Wiener--Ito chaos decomposition. A Gaussian weight satisfies the
condition for every degree of homogeneity; a weight with an atom does not, since its characteristic
functional does not decay.
:::

# The obstruction to the dilation-based construction

:::theorem "gauss-ridgelet:sigma-finite-countability" (lean := "OperatorRidgelet.GaussianWeighted.countable_of_absolutelyContinuous_of_pairwise_mutuallySingular")
A $`\sigma`-finite measure dominates at most countably many pairwise mutually singular probability
measures. Mutual singularity gives pairwise disjoint carriers of positive measure, and a
$`\sigma`-finite measure admits only countably many such sets.
:::

:::theorem "gauss-ridgelet:dilation-obstruction" (lean := "OperatorRidgelet.GaussianWeighted.not_exists_sFinite_dominating") (uses := "gauss-ridgelet:sigma-finite-countability")
No $`\sigma`-finite measure carries an uncountable pairwise mutually singular family of
probability measures. Applied to the dilated Gaussian spectral measures
$`\mathcal N(0,R/\omega^2)`, which are pairwise mutually singular in infinite dimension by the
Feldman--H\'ajek dichotomy, this shows that the hypothesis of the Fourier-side finite-measure
reconstruction theorem is unsatisfiable. It is the reason the transform of this chapter avoids
dilating the spectral variable.
:::
