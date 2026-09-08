import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Measurability of iterated derivatives in a parameter

For a family `f : α → ℝ → ℂ` such that `a ↦ f a t` is measurable for every `t`, the iterated
derivatives `a ↦ iteratedDeriv k (f a) x` are measurable at every point `x` around which all
the functions `f a` are smooth — with the neighbourhood of smoothness allowed to depend on `a`.
Mathlib's `measurable_deriv_with_param` needs joint continuity of the family; here only
measurability in the parameter is available, so the derivative is replaced by the `limsup` of
the difference quotients along `t_n = 1/(n+1)` (`limsupDeriv`), which is measurable in the
parameter without any convergence assumption, agrees with the derivative wherever the function
is differentiable, and depends only on the germ of the function.  Its iterate `limsupIterDeriv`
agrees with `iteratedDeriv k` on every open set of smoothness.

The last section records that the supremum of a continuous `ℝ≥0∞`-valued function over a set
equals its supremum over a dense subset, which reduces uncountable suprema of continuous
functions to countable ones.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

/-! ### The upper difference-quotient derivative -/

/-- The `limsup` of the difference quotients of `f` at `x` along the steps `1/(n+1)`. -/
def limsupDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  limsup (fun n : ℕ => ((n : ℝ) + 1) * (f (x + ((n : ℝ) + 1)⁻¹) - f x)) atTop

/-- The steps `1/(n+1)` tend to `0` within `ℝ ∖ {0}`. -/
theorem tendsto_inv_natCast_add_one_nhdsWithin :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
  · simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · exact inv_ne_zero (by positivity)

/-- The steps `x + 1/(n+1)` tend to `x`. -/
theorem tendsto_add_inv_natCast_add_one (x : ℝ) :
    Tendsto (fun n : ℕ => x + ((n : ℝ) + 1)⁻¹) atTop (𝓝 x) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add x
  simpa only [one_div, add_zero] using h

/-- Where `f` is differentiable, `limsupDeriv` is the derivative. -/
theorem limsupDeriv_eq_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    limsupDeriv f x = f' := by
  refine Filter.Tendsto.limsup_eq ?_
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp hf).comp tendsto_inv_natCast_add_one_nhdsWithin
  refine h.congr fun n => ?_
  simp only [Function.comp, smul_eq_mul, inv_inv]

/-- `limsupDeriv` depends only on the germ of the function at the point. -/
theorem limsupDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    limsupDeriv f x = limsupDeriv g x := by
  unfold limsupDeriv
  refine limsup_congr ?_
  filter_upwards [(tendsto_add_inv_natCast_add_one x).eventually h] with n hn
  rw [hn, h.eq_of_nhds]

/-- `limsupDeriv` is measurable in a parameter as soon as the family is measurable in the
parameter at every point. -/
theorem measurable_limsupDeriv {α : Type*} [MeasurableSpace α] {f : α → ℝ → ℝ}
    (hf : ∀ t, Measurable fun a => f a t) (x : ℝ) :
    Measurable fun a => limsupDeriv (f a) x := by
  unfold limsupDeriv
  exact Measurable.limsup fun n => ((hf _).sub (hf x)).const_mul _

/-! ### The complex-valued version -/

/-- The complex upper difference-quotient derivative, taken on the real and imaginary parts. -/
def limsupDerivC (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (limsupDeriv (fun t => (f t).re) x : ℂ) + (limsupDeriv (fun t => (f t).im) x : ℂ) * Complex.I

/-- Where `f` is differentiable, `limsupDerivC` is the derivative. -/
theorem limsupDerivC_eq_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    limsupDerivC f x = f' := by
  have hre : HasDerivAt (fun t => (f t).re) f'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun t => (f t).im) f'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  unfold limsupDerivC
  rw [limsupDeriv_eq_of_hasDerivAt hre, limsupDeriv_eq_of_hasDerivAt him, Complex.re_add_im]

/-- `limsupDerivC` depends only on the germ of the function at the point. -/
theorem limsupDerivC_congr {f g : ℝ → ℂ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    limsupDerivC f x = limsupDerivC g x := by
  have h1 : (fun t => (f t).re) =ᶠ[𝓝 x] fun t => (g t).re := h.mono fun t ht => by simp only [ht]
  have h2 : (fun t => (f t).im) =ᶠ[𝓝 x] fun t => (g t).im := h.mono fun t ht => by simp only [ht]
  unfold limsupDerivC
  rw [limsupDeriv_congr h1, limsupDeriv_congr h2]

/-- `limsupDerivC` is measurable in a parameter. -/
theorem measurable_limsupDerivC {α : Type*} [MeasurableSpace α] {f : α → ℝ → ℂ}
    (hf : ∀ t, Measurable fun a => f a t) (x : ℝ) :
    Measurable fun a => limsupDerivC (f a) x := by
  unfold limsupDerivC
  have hre := measurable_limsupDeriv (f := fun a t => (f a t).re)
    (fun t => Complex.continuous_re.measurable.comp (hf t)) x
  have him := measurable_limsupDeriv (f := fun a t => (f a t).im)
    (fun t => Complex.continuous_im.measurable.comp (hf t)) x
  exact (Complex.continuous_ofReal.measurable.comp hre).add
    ((Complex.continuous_ofReal.measurable.comp him).mul_const Complex.I)

/-! ### Iterates -/

/-- The `k`-fold iterate of `limsupDerivC`. -/
def limsupIterDeriv (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  limsupDerivC^[k] f

@[simp]
theorem limsupIterDeriv_zero (f : ℝ → ℂ) : limsupIterDeriv 0 f = f := rfl

theorem limsupIterDeriv_succ (k : ℕ) (f : ℝ → ℂ) :
    limsupIterDeriv (k + 1) f = limsupDerivC (limsupIterDeriv k f) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterates are measurable in a parameter at every point. -/
theorem measurable_limsupIterDeriv {α : Type*} [MeasurableSpace α] {f : α → ℝ → ℂ}
    (hf : ∀ t, Measurable fun a => f a t) (k : ℕ) (x : ℝ) :
    Measurable fun a => limsupIterDeriv k (f a) x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    simp_rw [limsupIterDeriv_succ]
    exact measurable_limsupDerivC (f := fun a => limsupIterDeriv k (f a)) ih x

/-- On an open set of smoothness, the iterated derivatives are smooth. -/
theorem ContDiffOn.iteratedDeriv_of_isOpen {f : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) U := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    exact hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (le_of_eq ENat.coe_top_add_one)

/-- On an open set of smoothness, the iterates of `limsupDerivC` are the iterated
derivatives. -/
theorem limsupIterDeriv_eq_iteratedDeriv {f : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (k : ℕ) {x : ℝ} (hx : x ∈ U) :
    limsupIterDeriv k f x = iteratedDeriv k f x := by
  induction k generalizing x with
  | zero =>
    rw [iteratedDeriv_zero]
    rfl
  | succ k ih =>
    rw [limsupIterDeriv_succ, iteratedDeriv_succ]
    have hev : limsupIterDeriv k f =ᶠ[𝓝 x] iteratedDeriv k f := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    rw [limsupDerivC_congr hev]
    have hdiff : DifferentiableAt ℝ (iteratedDeriv k f) x :=
      ((hf.iteratedDeriv_of_isOpen hU k).contDiffAt (hU.mem_nhds hx)).differentiableAt
        (WithTop.coe_ne_zero.mpr ENat.top_ne_zero)
    exact limsupDerivC_eq_of_hasDerivAt hdiff.hasDerivAt

/-- **Measurability of iterated derivatives in a parameter.**  If `a ↦ f a t` is measurable for
every `t` and every `f a` is smooth on an open set `U a` containing `x`, then
`a ↦ iteratedDeriv k (f a) x` is measurable. -/
theorem measurable_iteratedDeriv_of_forall_contDiffOn {α : Type*} [MeasurableSpace α]
    {f : α → ℝ → ℂ} (hf : ∀ t, Measurable fun a => f a t) {x : ℝ}
    (hsmooth : ∀ a, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (f a) U) (k : ℕ) :
    Measurable fun a => iteratedDeriv k (f a) x := by
  have heq : (fun a => iteratedDeriv k (f a) x) = fun a => limsupIterDeriv k (f a) x := by
    funext a
    obtain ⟨U, hU, hxU, hfa⟩ := hsmooth a
    exact (limsupIterDeriv_eq_iteratedDeriv hU hfa k hxU).symm
  rw [heq]
  exact measurable_limsupIterDeriv hf k x

/-! ### Suprema of continuous functions over dense subsets -/

/-- The supremum of a continuous `ℝ≥0∞`-valued function over a set is its supremum over any
subset that is dense in it. -/
theorem biSup_eq_biSup_of_subset_closure {X : Type*} [TopologicalSpace X] {h : X → ℝ≥0∞}
    {s t : Set X} (hts : t ⊆ s) (hst : s ⊆ closure t) (hc : ContinuousOn h s) :
    ⨆ x ∈ s, h x = ⨆ x ∈ t, h x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (biSup_mono hts)
  have hne : (𝓝[t] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hst hx)
  have hlim : Tendsto h (𝓝[t] x) (𝓝 (h x)) := (hc x hx).mono_left (nhdsWithin_mono x hts)
  exact le_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun y hy => le_iSup₂ (f := fun y _ => h y) y hy)

end
