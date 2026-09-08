import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical
import OperatorRidgelet.RankOneLift

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Formal foundations" =>
%%%
file := "foundations"
%%%

This chapter records the elementary ReLU, cylindrical-obstruction, and rank-one operator results
that support the infinite-dimensional examples and the operator-valued transform.

:::theorem "operator-ridgelet:relu-odd-part" (lean := "OperatorRidgelet.relu_sub_relu_neg")
The odd part of ReLU is the identity:
$`\operatorname{ReLU}(x)-\operatorname{ReLU}(-x)=x`.
:::

:::definition "operator-ridgelet:spectral-relu-network" (lean := "OperatorRidgelet.spectralReLUNetwork") (uses := "operator-ridgelet:relu-odd-part")
For a finite spectral index set, pair positive and negative ReLU neurons to define the finite
spectral network.
:::

:::theorem "operator-ridgelet:spectral-relu-exact" (lean := "OperatorRidgelet.spectralReLUNetwork_eq") (uses := "operator-ridgelet:spectral-relu-network, operator-ridgelet:relu-odd-part")
Every finite spectral truncation is represented exactly by the paired-ReLU network.
:::

:::definition "operator-ridgelet:factors-through" (lean := "OperatorRidgelet.FactorsThrough")
A target $`F` is cylindrical through an observation $`P` when $`F=G\circ P` for some readout
$`G`.
:::

:::theorem "operator-ridgelet:fibre-separation" (lean := "OperatorRidgelet.not_factorsThrough_of_fibre_separation") (uses := "operator-ridgelet:factors-through")
If $`P(x)=P(y)` but $`F(x)\ne F(y)`, then $`F` cannot factor through $`P`.
:::

:::theorem "operator-ridgelet:kernel-obstruction" (lean := "OperatorRidgelet.not_factorsThrough_linear_of_kernel_separation") (uses := "operator-ridgelet:fibre-separation")
If a target separates zero from a vector in the kernel of a linear observation, then the target is
not cylindrical through that observation.
:::

:::definition "operator-ridgelet:rank-one-lift" (lean := "OperatorRidgelet.rankOneLift")
For a nonzero readout vector $`\psi`, define the normalized rank-one lift
$`W_{\psi,a}=\|\psi\|^{-2}(\psi\otimes a)`.
:::

:::theorem "operator-ridgelet:rank-one-lift-adjoint" (lean := "OperatorRidgelet.adjoint_rankOneLift_apply") (uses := "operator-ridgelet:rank-one-lift")
The adjoint readout recovers the vector parameter: $`W_{\psi,a}^*\psi=a`.
:::
