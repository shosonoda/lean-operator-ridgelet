import Architect
import OperatorRidgelet.Paper.Revision

/-! # Metadata for the strengthened spectral and finite-order statements -/

attribute [blueprint "lem:spectral-target-basic-i"
  (statement := /-- Lemma lem:spectral-target-basic The spectral target has the uniform L^1
    norm bound. -/)]
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
    moment is L^1∩L^2. -/)]
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
