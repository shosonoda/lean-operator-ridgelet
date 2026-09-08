import Verso
import VersoManual
import VersoBlueprint
import OperatorRidgelet.OperatorValuedRidgelet

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Operator-valued ridgelet transform" =>
%%%
file := "operator-valued-transform"
%%%

Fix a nonzero readout vector $`\psi`. The parameter map $`T_\psi` reduces operator parameters to
scalar ridge parameters, while the normalized rank-one map $`J_\psi` is a continuous measurable
section. Complex ridgelet measures can therefore be lifted exactly to operator parameters.

:::definition "operator-ridgelet:operator-parameter-map" (lean := "OperatorRidgelet.operatorParameterMap")
Define $`T_\psi(A,b)=(A^*\psi,\langle\psi,b\rangle)`.
:::

:::definition "operator-ridgelet:operator-ridgelet-section" (lean := "OperatorRidgelet.operatorRidgeletSection") (uses := "operator-ridgelet:operator-parameter-map, operator-ridgelet:rank-one-lift")
Define the normalized rank-one section
$`J_\psi(a,c)=(\|\psi\|^{-2}\psi\otimes a,c\|\psi\|^{-2}\psi)`.
:::

:::theorem "operator-ridgelet:bias-lift-readout" (lean := "OperatorRidgelet.inner_biasLift") (uses := "operator-ridgelet:operator-ridgelet-section")
For nonzero $`\psi`, the scalar readout of the normalized bias lift is $`c`.
:::

:::theorem "operator-ridgelet:section-right-inverse" (lean := "OperatorRidgelet.operatorParameterMap_section") (uses := "operator-ridgelet:operator-parameter-map, operator-ridgelet:operator-ridgelet-section, operator-ridgelet:rank-one-lift-adjoint, operator-ridgelet:bias-lift-readout")
For nonzero $`\psi`, $`T_\psi\circ J_\psi=\mathrm{id}`.
:::

:::theorem "operator-ridgelet:operator-parameter-map-continuous" (lean := "OperatorRidgelet.continuous_operatorParameterMap") (uses := "operator-ridgelet:operator-parameter-map")
The operator-parameter map is continuous.
:::

:::theorem "operator-ridgelet:operator-ridgelet-section-continuous" (lean := "OperatorRidgelet.continuous_operatorRidgeletSection") (uses := "operator-ridgelet:operator-ridgelet-section")
The normalized rank-one section is continuous.
:::

:::theorem "operator-ridgelet:section-feature-compatible" (lean := "OperatorRidgelet.operatorRidgeFeature_section") (uses := "operator-ridgelet:section-right-inverse")
Pulling an operator ridge feature back along $`J_\psi` gives the corresponding scalar ridge
feature.
:::

:::theorem "operator-ridgelet:operator-parameter-map-measurable" (lean := "OperatorRidgelet.measurable_operatorParameterMap") (uses := "operator-ridgelet:operator-parameter-map-continuous")
The operator-parameter map is Borel measurable.
:::

:::theorem "operator-ridgelet:operator-ridgelet-section-measurable" (lean := "OperatorRidgelet.measurable_operatorRidgeletSection") (uses := "operator-ridgelet:operator-ridgelet-section-continuous")
The normalized rank-one section is Borel measurable.
:::

:::definition "operator-ridgelet:scalar-complex-ridge-synthesis" (lean := "OperatorRidgelet.scalarComplexRidgeSynthesis")
Scalar complex ridge synthesis is the integral of the scalar ridge feature against a complex
measure.
:::

:::definition "operator-ridgelet:operator-complex-ridge-synthesis" (lean := "OperatorRidgelet.operatorComplexRidgeSynthesis") (uses := "operator-ridgelet:operator-parameter-map")
Operator synthesis integrates
$`\beta(\langle A^*\psi,x\rangle+\langle\psi,b\rangle)` against a complex measure on operator
parameters.
:::

:::theorem "operator-ridgelet:operator-complex-synthesis-of-lift" (lean := "OperatorRidgelet.operatorComplexRidgeSynthesis_map_section") (uses := "operator-ridgelet:operator-complex-ridge-synthesis, operator-ridgelet:scalar-complex-ridge-synthesis, operator-ridgelet:section-feature-compatible, operator-ridgelet:operator-ridgelet-section-measurable")
Under the standard measurability and integrability hypotheses, direct operator synthesis of the
lifted measure equals scalar synthesis.
:::

:::definition "operator-ridgelet:operator-valued-ridgelet-transform" (lean := "OperatorRidgelet.operatorValuedRidgeletTransform") (uses := "operator-ridgelet:operator-ridgelet-section, operator-ridgelet:operator-ridgelet-section-measurable")
For a scalar complex ridgelet measure $`R[f]`, define
$`R^{\mathrm{op}}[f]=(J_\psi)_\#R[f]`.
:::

:::definition "operator-ridgelet:operator-valued-synthesis" (lean := "OperatorRidgelet.operatorValuedSynthesis") (uses := "operator-ridgelet:operator-parameter-map, operator-ridgelet:operator-parameter-map-measurable")
Operator synthesis factors through scalar synthesis:
$`S_{\mathrm{op}}[\Gamma]=S[(T_\psi)_\#\Gamma]`.
:::

:::theorem "operator-ridgelet:operator-valued-transform-pushforward" (lean := "OperatorRidgelet.operatorValuedRidgeletTransform_pushforward") (uses := "operator-ridgelet:operator-valued-ridgelet-transform, operator-ridgelet:section-right-inverse")
Pushing the operator-valued transform forward along $`T_\psi` recovers the scalar transform.
:::

:::theorem "operator-ridgelet:operator-valued-reconstruction" (lean := "OperatorRidgelet.operatorValuedRidgelet_reconstruction") (uses := "operator-ridgelet:operator-valued-transform-pushforward, operator-ridgelet:operator-valued-synthesis")
Every scalar reconstruction theorem lifts exactly to the operator-valued ridgelet transform.
:::

:::theorem "operator-ridgelet:operator-parameter-redundancy" (lean := "OperatorRidgelet.operatorValuedSynthesis_eq_of_map_eq") (uses := "operator-ridgelet:operator-valued-synthesis")
Operator coefficient measures with the same scalar pushforward synthesize the same target.
:::
