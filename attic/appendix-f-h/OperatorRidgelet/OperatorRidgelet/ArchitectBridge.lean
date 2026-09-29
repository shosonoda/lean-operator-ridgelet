/-! Historical fragments; see the archive README for their original context. -/

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
