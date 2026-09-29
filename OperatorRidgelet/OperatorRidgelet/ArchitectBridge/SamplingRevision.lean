import Architect
import OperatorRidgelet.Paper.SamplingRevision

/-! # Banach sampling and exact Hilbert variance metadata -/

attribute [blueprint "lem:D.1-i"
  (statement := /-- Signed empirical means of an integrable Banach-valued atom converge to zero
    in expected norm. -/)]
  OperatorRidgelet.Paper.lem_D_1_i

attribute [blueprint "lem:D.1-ii"
  (statement := /-- Symmetrization bounds the expected empirical-mean error by twice the
    expected norm of the signed empirical mean. -/)]
  OperatorRidgelet.Paper.lem_D_1_ii

attribute [blueprint "cor:6.6-i-exact"
  (statement := /-- The expected squared Hilbert error is the exact variance divided by the
    sample width, including zero total variation. -/)]
  OperatorRidgelet.Paper.cor_6_6_i_exact

attribute [blueprint "lem:D.2"
  (statement := /-- The Rademacher average of a supremum of signed sums whose increments are
    dominated by two coordinates is at most twice the two-coordinate average. -/)]
  OperatorRidgelet.Paper.lem_D_2
