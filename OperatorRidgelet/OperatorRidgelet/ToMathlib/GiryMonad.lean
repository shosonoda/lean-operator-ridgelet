import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Pushforwards and Bochner integrals of a Giry-monad bind

Three elementary facts about `MeasureTheory.Measure.bind` that are missing from Mathlib:

* `Measure.map_bind_eq`: a pushforward commutes with a bind,
  `(m.bind f).map g = m.bind (map g ∘ f)`;
* `Measure.bind_map_eq`: a bind after a pushforward is a bind of the composite family;
* `Measure.integral_bind_eq`: the Bochner integral against `m.bind f` for a measurable family of
  probability measures, through the composition-product of `m` with the kernel `f`.
-/

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Pushing a bind forward: `(m.bind f).map g = m.bind (fun a => (f a).map g)`. -/
theorem map_bind_eq {m : Measure α} {f : α → Measure β} (hf : Measurable f) {g : β → γ}
    (hg : Measurable g) : (m.bind f).map g = m.bind fun a => (f a).map g := by
  ext E hE
  rw [Measure.map_apply hg hE, Measure.bind_apply (hg hE) hf.aemeasurable,
    Measure.bind_apply hE (f := fun a => (f a).map g)
      (show Measurable fun a => (f a).map g from
        (Measure.measurable_map g hg).comp hf).aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [Measure.map_apply hg hE]

/-- Binding after a pushforward: `(m.map h).bind f = m.bind (f ∘ h)`. -/
theorem bind_map_eq {m : Measure α} {h : α → β} (hh : Measurable h) {f : β → Measure γ}
    (hf : Measurable f) : (m.map h).bind f = m.bind (f ∘ h) := by
  ext E hE
  rw [Measure.bind_apply hE hf.aemeasurable, Measure.bind_apply hE (hf.comp hh).aemeasurable,
    lintegral_map (f := fun b => f b E)
      (show Measurable fun b => f b E from (Measure.measurable_coe hE).comp hf) hh]
  rfl

/-- The Bochner integral against a bind of a measurable family of probability measures:
`∫ F d(m.bind f) = ∫ (∫ F d(f a)) dm(a)` for `F` integrable against the bind. -/
theorem integral_bind_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} [SFinite m] {f : α → Measure β} (hf : Measurable f)
    [∀ a, IsProbabilityMeasure (f a)] {F : β → E} (hF : Integrable F (m.bind f)) :
    ∫ x, F x ∂(m.bind f) = ∫ a, ∫ x, F x ∂(f a) ∂m := by
  let κ : Kernel α β := ⟨f, hf⟩
  haveI : IsMarkovKernel κ := ⟨fun a => inferInstanceAs (IsProbabilityMeasure (f a))⟩
  have hbind : m.bind f = (m.compProd κ).snd := (Measure.snd_compProd m κ).symm
  have hF' : Integrable F (m.compProd κ).snd := hbind ▸ hF
  have hFm : AEStronglyMeasurable F (m.compProd κ).snd := hF'.aestronglyMeasurable
  rw [hbind, Measure.snd, integral_map measurable_snd.aemeasurable hFm]
  rw [Measure.integral_compProd (f := fun x => F x.2)
    (show Integrable (fun x : α × β => F x.2) (m.compProd κ) from
      (integrable_map_measure hFm measurable_snd.aemeasurable).mp hF')]
  rfl

end MeasureTheory.Measure
