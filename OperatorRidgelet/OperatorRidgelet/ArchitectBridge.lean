import Architect
import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical
import OperatorRidgelet.GaussianWeighted
import OperatorRidgelet.OperatorValuedRidgelet
import OperatorRidgelet.RankOneLift
import OperatorRidgelet.ToFoML.ActivationContraction
import OperatorRidgelet.ToFoML.ProbabilisticMethod
import OperatorRidgelet.ToFoML.RidgeFeature

/-!
# LeanArchitect metadata bridge

LeanArchitect and VersoBlueprint both provide an attribute named `blueprint`.  Importing their
attribute implementations into one module is therefore invalid.  The mathematical modules remain
independent of either documentation frontend; this module attaches LeanArchitect metadata after
the declarations have been compiled, while the separate `OperatorRidgeletBlueprint` project links the same declarations
from native Verso chapters.
-/

attribute [blueprint "operator-ridgelet:relu-odd-part"
  (statement := /-- The odd part of ReLU is the identity:
    $\operatorname{ReLU}(x)-\operatorname{ReLU}(-x)=x$. -/)]
  OperatorRidgelet.relu_sub_relu_neg

attribute [blueprint "operator-ridgelet:spectral-relu-network"
  (statement := /-- For a finite spectral index set $s$, define the paired-ReLU network. -/)
  (hasProof := false)] OperatorRidgelet.spectralReLUNetwork

attribute [blueprint "operator-ridgelet:spectral-relu-exact"
  (statement := /-- Every finite spectral truncation is represented exactly by paired ReLU
    neurons. -/)] OperatorRidgelet.spectralReLUNetwork_eq

attribute [blueprint "operator-ridgelet:factors-through"
  (statement := /-- A target $F$ is cylindrical through $P$ when $F=G\circ P$ for some
    readout $G$. -/)
  (hasProof := false)] OperatorRidgelet.FactorsThrough

attribute [blueprint "operator-ridgelet:fibre-separation"
  (statement := /-- If $P(x)=P(y)$ but $F(x)\ne F(y)$, then $F$ cannot factor through $P$. -/)]
  OperatorRidgelet.not_factorsThrough_of_fibre_separation

attribute [blueprint "operator-ridgelet:kernel-obstruction"
  (statement := /-- If a target separates a vector in the kernel of a linear observation from
    zero, then it is not cylindrical through that observation. -/)]
  OperatorRidgelet.not_factorsThrough_linear_of_kernel_separation

attribute [blueprint "operator-ridgelet:rank-one-lift"
  (statement := /-- Define
    $W_{\psi,a}=\|\psi\|^{-2}(\psi\otimes a)$. -/)
  (hasProof := false)] OperatorRidgelet.rankOneLift

attribute [blueprint "operator-ridgelet:rank-one-lift-adjoint"
  (statement := /-- If $\psi\ne0$, then $W_{\psi,a}^*\psi=a$. -/)]
  OperatorRidgelet.adjoint_rankOneLift_apply

attribute [blueprint "operator-ridgelet:operator-parameter-map"
  (statement := /-- The operator-parameter map is
    $T_\psi(A,b)=(A^*\psi,\langle\psi,b\rangle)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorParameterMap

attribute [blueprint "operator-ridgelet:operator-ridgelet-section"
  (statement := /-- The section is
    $J_\psi(a,c)=(\|\psi\|^{-2}\psi\otimes a,c\|\psi\|^{-2}\psi)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorRidgeletSection

attribute [blueprint "operator-ridgelet:bias-lift-readout"
  (statement := /-- For nonzero `ψ`, the readout of its normalized bias lift is `c`. -/)]
  OperatorRidgelet.inner_biasLift

attribute [blueprint "operator-ridgelet:section-right-inverse"
  (statement := /-- If `ψ` is nonzero, then $T_\psi\circ J_\psi$ is the identity. -/)]
  OperatorRidgelet.operatorParameterMap_section

attribute [blueprint "operator-ridgelet:operator-parameter-map-continuous"
  (statement := /-- The operator-parameter map is continuous. -/)]
  OperatorRidgelet.continuous_operatorParameterMap

attribute [blueprint "operator-ridgelet:operator-ridgelet-section-continuous"
  (statement := /-- The normalized rank-one section is continuous. -/)]
  OperatorRidgelet.continuous_operatorRidgeletSection

attribute [blueprint "operator-ridgelet:section-feature-compatible"
  (statement := /-- Pulling an operator ridge feature back along the section gives the
    corresponding scalar ridge feature. -/)] OperatorRidgelet.operatorRidgeFeature_section

attribute [blueprint "operator-ridgelet:operator-parameter-map-measurable"
  (statement := /-- The operator-parameter map is Borel measurable. -/)]
  OperatorRidgelet.measurable_operatorParameterMap

attribute [blueprint "operator-ridgelet:operator-ridgelet-section-measurable"
  (statement := /-- The normalized rank-one section is Borel measurable. -/)]
  OperatorRidgelet.measurable_operatorRidgeletSection

attribute [blueprint "operator-ridgelet:scalar-complex-ridge-synthesis"
  (statement := /-- Scalar complex ridge synthesis is the complex-measure integral of the
    scalar ridge feature. -/)
  (hasProof := false)] OperatorRidgelet.scalarComplexRidgeSynthesis

attribute [blueprint "operator-ridgelet:operator-complex-ridge-synthesis"
  (statement := /-- Operator complex ridge synthesis integrates an operator ridge feature
    against a complex measure. -/)
  (hasProof := false)] OperatorRidgelet.operatorComplexRidgeSynthesis

attribute [blueprint "operator-ridgelet:operator-complex-synthesis-of-lift"
  (statement := /-- Direct operator synthesis of the lifted measure equals scalar synthesis. -/)]
  OperatorRidgelet.operatorComplexRidgeSynthesis_map_section

attribute [blueprint "operator-ridgelet:operator-valued-ridgelet-transform"
  (statement := /-- Define
    $R^{\rm op}[f]=(J_\psi)_\#R[f]$. -/)
  (hasProof := false)] OperatorRidgelet.operatorValuedRidgeletTransform

attribute [blueprint "operator-ridgelet:operator-valued-synthesis"
  (statement := /-- Define
    $S_{\rm op}[\Gamma]=S[(T_\psi)_\#\Gamma]$. -/)
  (hasProof := false)] OperatorRidgelet.operatorValuedSynthesis

attribute [blueprint "operator-ridgelet:operator-valued-transform-pushforward"
  (statement := /-- Pushing the operator-valued transform forward along $T_\psi$ recovers the
    scalar transform. -/)] OperatorRidgelet.operatorValuedRidgeletTransform_pushforward

attribute [blueprint "operator-ridgelet:operator-valued-reconstruction"
  (statement := /-- Every scalar reconstruction theorem lifts exactly to the operator-valued
    ridgelet transform. -/)] OperatorRidgelet.operatorValuedRidgelet_reconstruction

attribute [blueprint "operator-ridgelet:operator-parameter-redundancy"
  (statement := /-- Operator coefficient measures with the same scalar pushforward synthesize
    the same target. -/)] OperatorRidgelet.operatorValuedSynthesis_eq_of_map_eq

/-! ## Gaussian-weighted ridgelet transform

Nodes marked `notReady` carry a statement whose proof is still `sorry`.  They are stated first so
that the formalization status of the manuscript's new section is visible in the blueprint.
-/

attribute [blueprint "gauss-ridgelet:character"
  (statement := /-- The analysis character is $x\mapsto e^{-i\langle x,\xi\rangle}$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.character

attribute [blueprint "gauss-ridgelet:gauss-fourier"
  (statement := /-- The Gaussian-weighted Fourier transform is
    $\mathcal Gf(\xi)=\int_Hf(x)e^{-i\langle x,\xi\rangle}\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.gaussFourier

attribute [blueprint "gauss-ridgelet:gauss-fourier-one"
  (statement := /-- On the constant function the analysis map is the characteristic functional,
    $\mathcal G\mathbf 1(\xi)=\widehat\mu(-\xi)$. -/)]
  OperatorRidgelet.GaussianWeighted.gaussFourier_one

attribute [blueprint "gauss-ridgelet:filter-fourier"
  (statement := /-- The one-dimensional filter transform is
    $\widehat\rho(\omega)=\int_\mathbb R\rho(t)e^{-i\omega t}\,\mathrm dt$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.filterFourier

attribute [blueprint "gauss-ridgelet:homogeneous"
  (statement := /-- A measure is homogeneous of degree $\alpha$ when
    $(D_\omega)_\#\nu=|\omega|^{-\alpha}\nu$ for every $\omega\ne0$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.IsHomogeneous

attribute [blueprint "gauss-ridgelet:homogeneous-exists"
  (statement := /-- For every $\alpha>0$ there is a nonzero $\sigma$-finite measure on $H$ which
    is homogeneous of degree $\alpha$.  The manuscript constructs the Gaussian mixture
    $\nu_\alpha=\int_0^\infty\mathcal N(0,2sP)s^{\alpha/2-1}\mathrm ds$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.exists_isHomogeneous_sFinite

attribute [blueprint "gauss-ridgelet:homogeneous-full-support"
  (statement := /-- The homogeneous mixture charges every nonempty open set, because the support
    of a centred Gaussian measure is the closure of its Cameron--Martin space. -/)
  (notReady := true)]
  OperatorRidgelet.GaussianWeighted.exists_isHomogeneous_sFinite_support

attribute [blueprint "gauss-ridgelet:homogeneous-change-of-variables"
  (statement := /-- Homogeneity gives
    $\int_HF(\omega a)\,\nu(\mathrm da)=|\omega|^{-\alpha}\int_HF\,\mathrm d\nu$.  This is the
    only substitution performed in the parameter variable. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.isHomogeneous_map_smul

attribute [blueprint "gauss-ridgelet:ridgelet"
  (statement := /-- The Gaussian-weighted ridgelet transform is
    $R_\rho[f](a,c)=\int_Hf(x)\rho(\langle a,x\rangle+c)\,\mu(\mathrm dx)$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.ridgelet

attribute [blueprint "gauss-ridgelet:parameter-measure"
  (statement := /-- The parameter measure is $\nu\otimes\mathrm dc$ on $H\times\mathbb R$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.parameterMeasure

attribute [blueprint "gauss-ridgelet:admissible-filter"
  (statement := /-- A filter is admissible when $\widehat\rho$ is smooth and compactly supported
    away from the origin. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.IsAdmissibleFilter

attribute [blueprint "gauss-ridgelet:admissibility-constant"
  (statement := /-- The admissibility constant is
    $C^{(\alpha)}_{\rho_1,\rho_2}
    =(2\pi)^{-1}\int\widehat{\rho_1}\overline{\widehat{\rho_2}}|\omega|^{-\alpha}\mathrm d\omega$;
    for $\alpha=1$ it is the one-dimensional Calder\'on condition and contains no dimension. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.admissibilityConst

attribute [blueprint "gauss-ridgelet:fourier-slice"
  (statement := /-- Fourier slice:
    $\int_\mathbb R R_\rho[f](a,c)e^{-i\omega c}\mathrm dc
    =\widehat\rho(\omega)\,\mathcal Gf(-\omega a)$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.integral_ridgelet_mul_character

attribute [blueprint "gauss-ridgelet:energy-inner"
  (statement := /-- The energy inner product is
    $\langle f,g\rangle_{\mathfrak E}=\int_H\mathcal Gf\overline{\mathcal Gg}\,\mathrm d\nu$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.energyInner

attribute [blueprint "gauss-ridgelet:energy-space"
  (statement := /-- The energy space consists of the $L^2(H,\mu)$ functions whose analysis map is
    square integrable against $\nu$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.MemEnergySpace

attribute [blueprint "gauss-ridgelet:energy-space-gaussian-decay"
  (statement := /-- Gaussian decay of the analysis map implies membership in the energy space. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.memEnergySpace_of_gaussian_decay

attribute [blueprint "gauss-ridgelet:plancherel"
  (statement := /-- Plancherel identity:
    $\langle R_{\rho_1}[f],R_{\rho_2}[g]\rangle
    =C^{(\alpha)}_{\rho_1,\rho_2}\langle f,g\rangle_{\mathfrak E}$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.plancherel

attribute [blueprint "gauss-ridgelet:ridgelet-memLp"
  (statement := /-- The transform of an energy-space element is square integrable on the
    parameter space. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.memLp_ridgelet

attribute [blueprint "gauss-ridgelet:gauss-fourier-injective"
  (statement := /-- The analysis map is injective, by uniqueness of characteristic
    functionals. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.gaussFourier_injective

attribute [blueprint "gauss-ridgelet:ridgelet-injective"
  (statement := /-- The Gaussian-weighted ridgelet transform has trivial null space. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.injective_ridgelet

attribute [blueprint "gauss-ridgelet:inversion"
  (statement := /-- Inversion: the analysis map is recovered from the coefficients along any ray,
    that is for any factorization $\xi=-\omega a$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.gaussFourier_eq_of_ridgelet

attribute [blueprint "gauss-ridgelet:de-gaussianized"
  (statement := /-- The de-Gaussianized analysis map is
    $G(\xi)=e^{\langle Q\xi,\xi\rangle/2}\mathcal Gf(\xi)$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.deGaussianized

attribute [blueprint "gauss-ridgelet:de-gaussianized-determines"
  (statement := /-- The de-Gaussianized analysis map determines the target, since its Taylor
    coefficients along rays are the Wick moments and the Wick powers are total in
    $L^2(H,\mu)$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.deGaussianized_determines

attribute [blueprint "gauss-ridgelet:frame-operator"
  (statement := /-- The frame operator is
    $T_\alpha f=\mathcal F\bigl((\mathcal Gf)\nu\bigr)$. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.frameOperator

attribute [blueprint "gauss-ridgelet:frame-operator-riesz"
  (statement := /-- The frame operator represents the energy form, hence is the Riesz isomorphism
    of the energy space onto its dual. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.frameOperator_eq_energyInner

attribute [blueprint "gauss-ridgelet:synthesis-composition"
  (statement := /-- Analysis followed by the adjoint of a second analysis is the admissibility
    constant times the frame operator. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.synthesis_comp_ridgelet

attribute [blueprint "gauss-ridgelet:bias-fourier"
  (statement := /-- The bias-Fourier transform of a coefficient function. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.biasFourier

attribute [blueprint "gauss-ridgelet:ray-average"
  (statement := /-- The ray average
    $\Lambda^{(\alpha)}_\rho[\gamma](\xi)
    =(2\pi)^{-1}\int\overline{\widehat\rho(\omega)}|\omega|^{-\alpha}
    \widehat\gamma(-\xi/\omega,\omega)\mathrm d\omega$ averages the inversion over every
    factorization $\xi=-\omega a$; it is the analogue of the filtered backprojection of the Radon
    inversion. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.rayAverage

attribute [blueprint "gauss-ridgelet:ray-average-adjoint"
  (statement := /-- The ray average is the adjoint of the transform: pairing on the parameter side
    equals pairing the ray average with the analysis map on the spectral side. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.inner_rayAverage

attribute [blueprint "gauss-ridgelet:reproducing-formula"
  (statement := /-- The ray average inverts the transform exactly:
    $\Lambda^{(\alpha)}_\rho[R_\rho[f]]=C^{(\alpha)}_{\rho,\rho}\mathcal Gf$.  With the inversion of
    the analysis map this is the reconstruction formula
    $\Delta[C^{-1}\Lambda[R_\rho[f]]]=f$. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.rayAverage_ridgelet

attribute [blueprint "gauss-ridgelet:range-projection"
  (statement := /-- The orthogonal projection onto the closure of the range of the transform,
    written on the bias-Fourier side. -/)
  (hasProof := false)] OperatorRidgelet.GaussianWeighted.rangeProjection

attribute [blueprint "gauss-ridgelet:reproducing-identity"
  (statement := /-- The transform is a fixed point of the range projection.  This reproducing
    identity is the range characterization, and it is the redundancy of the continuous frame. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.rangeProjection_ridgelet

attribute [blueprint "gauss-ridgelet:energy-space-one-iff"
  (statement := /-- The energy space contains the constants exactly when the characteristic
    functional of the weight is square integrable against the reference measure.  This is the only
    place where a general weight can fail; a Gaussian weight always satisfies it. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.memEnergySpace_one_iff

attribute [blueprint "gauss-ridgelet:sigma-finite-countability"
  (statement := /-- A $\sigma$-finite measure dominates at most countably many pairwise mutually
    singular probability measures. -/)
  (notReady := true)]
  OperatorRidgelet.GaussianWeighted.countable_of_absolutelyContinuous_of_pairwise_mutuallySingular

attribute [blueprint "gauss-ridgelet:dilation-obstruction"
  (statement := /-- No $\sigma$-finite measure carries an uncountable pairwise mutually singular
    family.  Applied to the dilated Gaussian spectral measures $\mathcal N(0,R/\omega^2)$ this
    shows that the hypothesis of the Fourier-side finite-measure reconstruction theorem is
    unsatisfiable in infinite dimension. -/)
  (notReady := true)] OperatorRidgelet.GaussianWeighted.not_exists_sFinite_dominating

/-! ## Statistical-learning components (intended for FoML) -/

attribute [blueprint "operator-ridgelet:foml-relu"
  (statement := /-- The rectified linear unit is $\operatorname{ReLU}(x)=\max(x,0)$. -/)
  (hasProof := false)] OperatorRidgelet.relu

attribute [blueprint "operator-ridgelet:foml-relu-lipschitz"
  (statement := /-- ReLU is $1$-Lipschitz. -/)] OperatorRidgelet.abs_relu_sub_relu_le

attribute [blueprint "operator-ridgelet:activation-rademacher-contraction"
  (statement := /-- For a finite hypothesis class and a Lipschitz activation $\sigma$ with
    $\sigma(0)=0$, the absolute empirical Rademacher complexity of $\sigma\circ\mathcal F$
    is at most $2L$ times that of $\mathcal F$. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_activation_contraction_finite

attribute [blueprint "operator-ridgelet:relu-rademacher-contraction"
  (statement := /-- For a finite hypothesis class, applying ReLU increases absolute empirical
    Rademacher complexity by at most the convention-dependent factor $2$. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_relu_contraction_finite

attribute [blueprint "operator-ridgelet:first-moment-sample-selection"
  (statement := /-- Under a probability law, every integrable real error admits a realization
    whose error is no larger than its expectation. -/)]
  OperatorRidgelet.exists_realization_le_mean

attribute [blueprint "operator-ridgelet:sampled-ridge-preactivation"
  (statement := /-- For parameters $(a_h,b_h)$ and $x\in K$, the affine ridge preactivation is
    $\langle a_h,x\rangle-b_h$. -/)
  (hasProof := false)] OperatorRidgelet.sampledRidgePreactivation

attribute [blueprint "operator-ridgelet:sampled-ridge-activation-contraction"
  (statement := /-- On every finite sample from $K$, applying an $L$-Lipschitz activation
    vanishing at zero costs at most the factor $2L$ in absolute empirical Rademacher complexity. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_sampledRidge_activation_contraction_finite

attribute [blueprint "operator-ridgelet:sampled-ridge-relu-contraction"
  (statement := /-- ReLU ridge features on a finite sample from $K$ have empirical Rademacher
    complexity at most twice that of their affine preactivations. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_sampledRidge_relu_contraction_finite
