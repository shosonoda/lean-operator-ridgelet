import Architect
import OperatorRidgelet.Paper.Revision

/-! # Metadata for the strengthened spectral, Fourier, and finite-order statements -/

attribute [blueprint "lem:spectral-target-basic-i"
  (statement := /-- Lemma lem:spectral-target-basic The spectral target has the uniform L¹ norm
    bound. -/)]
  OperatorRidgelet.Paper.lem_spectral_target_basic_i

attribute [blueprint "lem:spectral-target-basic-ii"
  (statement := /-- Lemma lem:spectral-target-basic An integrable spectral density has a
    continuous target. -/)]
  OperatorRidgelet.Paper.lem_spectral_target_basic_ii

attribute [blueprint "lem:spectral-target-basic-iii"
  (statement := /-- Lemma lem:spectral-target-basic A spectral density is determined by its
    target. -/)]
  OperatorRidgelet.Paper.lem_spectral_target_basic_iii

attribute [blueprint "lem:coefficient-finite-order-i"
  (statement := /-- Lemma lem:coefficient-finite-order A bounded density with a finite ray
    moment is L¹∩L². -/)]
  OperatorRidgelet.Paper.lem_coefficient_finite_order_i

attribute [blueprint "lem:coefficient-finite-order-ii"
  (statement := /-- Lemma lem:coefficient-finite-order The inverse integral represents the
    coefficient. -/)]
  OperatorRidgelet.Paper.lem_coefficient_finite_order_ii

attribute [blueprint "lem:coefficient-finite-order-iii"
  (statement := /-- Lemma lem:coefficient-finite-order Finitely many ray derivatives give
    pointwise decay. -/)]
  OperatorRidgelet.Paper.lem_coefficient_finite_order_iii

attribute [blueprint "lem:coefficient-finite-order-iv"
  (statement := /-- Lemma lem:coefficient-finite-order The parameter moment is bounded by
    A_{r+2,r}. -/)]
  OperatorRidgelet.Paper.lem_coefficient_finite_order_iv

attribute [blueprint "lem:coefficient-finite-order-v"
  (statement := /-- Lemma lem:coefficient-finite-order Finite ray data imply a finite parameter
    moment. -/)]
  OperatorRidgelet.Paper.lem_coefficient_finite_order_v

attribute [blueprint "thm:E-moments"
  (statement := /-- Theorem thm:E All parameter moments are bounded, also for vector-valued
    densities. -/)]
  OperatorRidgelet.Paper.thm_E_moments

attribute [blueprint "thm:A-iii-e"
  (statement := /-- Theorem thm:A Tempered synthesis is jointly absolutely integrable. -/)]
  OperatorRidgelet.Paper.thm_A_iii_e

attribute [blueprint "thm:vector-valued-A-iii-e"
  (statement := /-- Theorem thm:vector-valued Tempered synthesis is Bochner integrable on the
    product. -/)]
  OperatorRidgelet.Paper.thm_vector_valued_A_iii_e

attribute [blueprint "lem:partial-fourier-l2-i"
  (statement := /-- Lemma lem:partial-fourier-l2 Bias Fourier transformation is a genuine unitary
with jointly measurable representatives and the angular normalization. -/)]
  OperatorRidgelet.Paper.lem_partial_fourier_l2

attribute [blueprint "cor:coefficient-stability-i"
  (statement := /-- Corollary cor:coefficient-stability The decoder is C⁻¹ T⁻¹ S. -/)]
  OperatorRidgelet.Paper.cor_coefficient_stability_i

attribute [blueprint "cor:coefficient-stability-ii"
  (statement := /-- Corollary cor:coefficient-stability The bounded decoder is a left inverse. -/)]
  OperatorRidgelet.Paper.cor_coefficient_stability_ii

attribute [blueprint "cor:coefficient-stability-iii"
  (statement := /-- Corollary cor:coefficient-stability The decoder norm is at most 1/√C. -/)]
  OperatorRidgelet.Paper.cor_coefficient_stability_iii

attribute [blueprint "cor:coefficient-stability-iv"
  (statement := /-- Corollary cor:coefficient-stability Coefficient error δ gives spectral
    error δ/√C. -/)]
  OperatorRidgelet.Paper.cor_coefficient_stability_iv

attribute [blueprint "thm:C-iv-completion"
  (statement := /-- Theorem thm:C Backprojection after analysis recovers the completed spectral
    density. -/)]
  OperatorRidgelet.Paper.thm_C_iv_completion

attribute [blueprint "thm:vector-valued-C-iv-completion"
  (statement := /-- Theorem thm:vector-valued The completed vector spectral density is
    recovered in L². -/)]
  OperatorRidgelet.Paper.thm_vector_valued_C_iv_completion

attribute [blueprint "thm:general-weights-dense"
  (statement := /-- Theorem thm:general-weights Bounded-set finite direction weights retain
    universality. -/)]
  OperatorRidgelet.Paper.thm_general_weights_dense

attribute [blueprint "lem:coefficient-isometry-v"
  (statement := /-- Lemma lem:coefficient-isometry The L² inverse formula is absolutely integrable
on almost every ray, for every bias value. -/)]
  OperatorRidgelet.Paper.lem_coefficient_isometry_v

attribute [blueprint "lem:partial-fourier-l2-ii"
  (statement := /-- Lemma lem:partial-fourier-l2 The Fourier representatives agree on almost
    every section. -/)]
  OperatorRidgelet.Paper.lem_partial_fourier_l2_uniqueness

attribute [blueprint "thm:general-weights-backprojection"
  (statement := /-- Theorem thm:general-weights Abstract input weights retain completed
    backprojection. -/)]
  OperatorRidgelet.Paper.thm_general_weights_backprojection

attribute [blueprint "thm:general-weights-stability"
  (statement := /-- Theorem thm:general-weights Stability holds for an arbitrary probability
    input weight. -/)]
  OperatorRidgelet.Paper.thm_general_weights_stability

attribute [blueprint "lem:coefficient-adjoint-i"
  (statement := /-- Lemma lem:coefficient-adjoint The coefficient operator has the bounded
    ray-average
adjoint and the scaled left-inverse identity. -/)]
  OperatorRidgelet.Paper.lem_coefficient_adjoint_i

attribute [blueprint "lem:coefficient-adjoint-ii"
  (statement := /-- Lemma lem:coefficient-adjoint The ray-average integral is absolutely
    convergent a.e. -/)]
  OperatorRidgelet.Paper.lem_coefficient_adjoint_ii

attribute [blueprint "lem:coefficient-adjoint-iii"
  (statement := /-- Lemma lem:coefficient-adjoint Every measurable Fourier representative gives
    Λ. -/)]
  OperatorRidgelet.Paper.lem_coefficient_adjoint_iii
