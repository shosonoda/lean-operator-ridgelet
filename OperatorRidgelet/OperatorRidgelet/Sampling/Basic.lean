import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Architecture.Basic
import OperatorRidgelet.ToMathlib.MeasurePi
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Auxiliary lemmas for Section 6 (finite-width approximation) and Appendix D

Elementary facts used by the proofs of `OperatorRidgelet.Paper.Sampling`: the compact sup norm
is a nonnegative supremum, orthogonal projections are contractions, and the product law
`sampleLaw N p = p^{⊗N}` is a probability measure.  The Hilbert-valued variance identity of
Lemma D.3 is the general `integral_norm_sq_sampleMean` of `OperatorRidgelet.ToMathlib.MeasurePi`.
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

/-! ### The compact sup norm -/

section SupNorm

variable {X : Type*} {Y : Type*} [NormedAddCommGroup Y]

theorem compactSupNorm_nonneg (K : Set X) (f : X → Y) : 0 ≤ compactSupNorm K f :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ norm_nonneg _

theorem compactSupNorm_le {K : Set X} {f : X → Y} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ K, ‖f x‖ ≤ a) : compactSupNorm K f ≤ a :=
  Real.sSup_le (fun _ ⟨x, hx, hfx⟩ => hfx ▸ h x hx) ha

end SupNorm

/-! ### Finite-rank orthogonal projections -/

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An orthogonal projection is a contraction. -/
theorem IsFiniteRankProjection.norm_apply_le {P : H →L[ℝ] H} (hP : IsFiniteRankProjection P)
    (x : H) : ‖P x‖ ≤ ‖x‖ :=
  (P.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x)
    (IsStarProjection.norm_le P hP.isStarProjection))

end Projection

/-! ### The product law is a probability measure -/

instance instIsProbabilityMeasureSampleLaw {Θ : Type*} [MeasurableSpace Θ] (N : ℕ)
    (p : Measure Θ) [IsProbabilityMeasure p] : IsProbabilityMeasure (sampleLaw N p) := by
  unfold sampleLaw
  infer_instance

end OperatorRidgelet
