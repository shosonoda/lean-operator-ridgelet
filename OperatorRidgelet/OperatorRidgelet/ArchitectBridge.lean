import Architect
import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical
import OperatorRidgelet.ToFoML.ActivationContraction
import OperatorRidgelet.ToFoML.ProbabilisticMethod
import OperatorRidgelet.ToFoML.RidgeFeature
import OperatorRidgelet.ArchitectBridge.Networks
import OperatorRidgelet.ArchitectBridge.Transform
import OperatorRidgelet.ArchitectBridge.Reconstruction
import OperatorRidgelet.ArchitectBridge.Tempered
import OperatorRidgelet.ArchitectBridge.Sampling
import OperatorRidgelet.ArchitectBridge.Examples
import OperatorRidgelet.ArchitectBridge.Revision
import OperatorRidgelet.ArchitectBridge.SamplingRevision
import OperatorRidgelet.ArchitectBridge.Sobolev

/-!
# LeanArchitect metadata bridge

LeanArchitect and VersoBlueprint both provide an attribute named `blueprint`.  Importing their
attribute implementations into one module is therefore invalid.  The mathematical modules remain
independent of either documentation frontend; this module attaches LeanArchitect metadata after
the declarations have been compiled, while the separate `OperatorRidgeletBlueprint` project links
the same declarations
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

/-! ## Statistical-learning components (intended for FoML) -/

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
    vanishing at zero costs at most the factor $2L$ in absolute empirical Rademacher
    complexity. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_sampledRidge_activation_contraction_finite

attribute [blueprint "operator-ridgelet:sampled-ridge-relu-contraction"
  (statement := /-- ReLU ridge features on a finite sample from $K$ have empirical Rademacher
    complexity at most twice that of their affine preactivations. -/)]
  OperatorRidgelet.empiricalRademacherComplexity_sampledRidge_relu_contraction_finite
