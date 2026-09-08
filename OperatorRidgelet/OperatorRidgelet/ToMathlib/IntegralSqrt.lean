import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Jensen's inequality for the square root

* `integral_sqrt_le_sqrt_integral`: `∫ √f dμ ≤ √(∫ f dμ)` for a nonnegative integrable `f` on
  a probability space (Jensen's inequality for the concave function `√`);
* `Finset.sum_mul_sqrt_le_sqrt_sum`: the discrete form `∑ᵢ wᵢ √yᵢ ≤ √(∑ᵢ wᵢ yᵢ)` for weights
  `wᵢ ≥ 0` summing to one, by the Cauchy–Schwarz inequality.
-/

open MeasureTheory

/-- The square root is bounded by an affine function: `√y ≤ |y| + 1`. -/
theorem Real.sqrt_le_abs_add_one (y : ℝ) : Real.sqrt y ≤ |y| + 1 := by
  calc Real.sqrt y ≤ Real.sqrt ((|y| + 1) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [abs_nonneg y, le_abs_self y])
    _ = |y| + 1 := Real.sqrt_sq (by positivity)

/-- The square root of an integrable function is integrable. -/
theorem MeasureTheory.Integrable.sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => Real.sqrt (f x)) μ :=
  (hf.norm.add (integrable_const 1)).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_abs_add_one _)

/-- **Jensen's inequality for the square root**: `∫ √f dμ ≤ √(∫ f dμ)` for a nonnegative
integrable `f` on a probability space. -/
theorem integral_sqrt_le_sqrt_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    ∫ x, Real.sqrt (f x) ∂μ ≤ Real.sqrt (∫ x, f x ∂μ) :=
  ConcaveOn.le_map_integral Real.strictConcaveOn_sqrt.concaveOn Real.continuous_sqrt.continuousOn
    isClosed_Ici hf0 hf hf.sqrt

/-- The discrete Jensen inequality for the square root: `∑ᵢ wᵢ √yᵢ ≤ √(∑ᵢ wᵢ yᵢ)` for
nonnegative weights summing to one and nonnegative `yᵢ`. -/
theorem Finset.sum_mul_sqrt_le_sqrt_sum {ι : Type*} (s : Finset ι) {w y : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, w i * Real.sqrt (y i) ≤ Real.sqrt (∑ i ∈ s, w i * y i) := by
  have h0 : 0 ≤ ∑ i ∈ s, w i * Real.sqrt (y i) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.sqrt_nonneg _)
  have h1 : 0 ≤ ∑ i ∈ s, w i * y i := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hy i hi)
  rw [Real.le_sqrt h0 h1]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * Real.sqrt (y i))
  have e1 : ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * Real.sqrt (y i)) =
      ∑ i ∈ s, w i * Real.sqrt (y i) :=
    Finset.sum_congr rfl fun i hi => by rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = 1 := by
    rw [← hw1]
    exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (y i)) ^ 2 = ∑ i ∈ s, w i * y i :=
    Finset.sum_congr rfl fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hy i hi)]
  rw [e1, e2, e3, one_mul] at hcs
  exact hcs
