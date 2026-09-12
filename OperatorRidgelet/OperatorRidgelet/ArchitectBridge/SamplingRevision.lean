import Architect
import OperatorRidgelet.Paper.SamplingRevision

/-! # Banach sampling and exact Hilbert variance metadata -/

attribute [blueprint "lem:banach-rademacher-vanishing-i"
  (statement := /-- Signed empirical means of an integrable Banach-valued atom converge to zero
    in expected norm. -/)]
  OperatorRidgelet.Paper.lem_banach_rademacher_vanishing_i

attribute [blueprint "lem:banach-rademacher-vanishing-ii"
  (statement := /-- Symmetrization bounds the expected empirical-mean error by twice the
    expected norm of the signed empirical mean. -/)]
  OperatorRidgelet.Paper.lem_banach_rademacher_vanishing_ii

attribute [blueprint "cor:vector-rates-i-exact"
  (statement := /-- The expected squared Hilbert error is the exact variance divided by the
    sample width, including zero total variation. -/)]
  OperatorRidgelet.Paper.cor_vector_rates_i_exact
