import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Extension by zero from measurable subtypes -/

noncomputable section
open MeasureTheory Set

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

def subtypeZeroExtend (s : Set α) (f : s → E) : α → E :=
  s.indicator (Function.extend Subtype.val f (fun _ => 0))

omit [MeasurableSpace α] in
theorem subtypeZeroExtend_coe (s : Set α) (f : s → E) (x : s) :
    subtypeZeroExtend s f x = f x := by
  rw [subtypeZeroExtend, Set.indicator_of_mem x.property]
  exact Subtype.val_injective.extend_apply _ _ x

omit [MeasurableSpace α] in
theorem subtypeZeroExtend_of_not_mem (s : Set α) (f : s → E) {x : α} (hx : x ∉ s) :
    subtypeZeroExtend s f x = 0 := Set.indicator_of_notMem hx _

theorem memLp_subtypeZeroExtend_iff {s : Set α} (hs : MeasurableSet s) (f : s → E)
    (p : ENNReal) (μ : Measure α) :
    MemLp (subtypeZeroExtend s f) p μ ↔ MemLp f p (μ.comap Subtype.val) := by
  rw [subtypeZeroExtend, memLp_indicator_iff_restrict hs, ← map_comap_subtype_coe hs μ,
    (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff,
    Function.extend_comp Subtype.val_injective]

theorem integral_subtypeZeroExtend [NormedSpace ℝ E] {s : Set α} (hs : MeasurableSet s) (f : s → E)
    (μ : Measure α) :
    ∫ x, subtypeZeroExtend s f x ∂μ = ∫ x : s, f x ∂μ.comap Subtype.val := by
  rw [subtypeZeroExtend, integral_indicator hs,
    ← integral_subtype_comap hs (Function.extend Subtype.val f (fun _ => 0))]
  congr 1
  funext x
  exact Subtype.val_injective.extend_apply _ _ x
end MeasureTheory
