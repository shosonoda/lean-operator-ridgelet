import OperatorRidgelet.ToMathlib.HermiteGaussian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Hermite expansion of the Gaussian generating function in `L²`

Let `Y` be a *standard Gaussian coordinate* on a measure space `(Ω, μ)`: a measurable function
whose law is `𝒩(0,1)`.  The generating function `G_z(Y) = e^{zY - z²/2}` of the probabilists'
Hermite polynomials expands in `L²(μ)` as `∑ₙ zⁿ/n! Heₙ(Y)`, because the `Heₙ(Y)` are
orthogonal with squared norms `n!` and `‖G_z(Y)‖²_{L²} = e^{|z|²} = ∑ₙ |z|^{2n}/n!`.

Pairing with `f ∈ L²(μ)` gives, for the coefficients `cₙ = ∫ f Heₙ(Y) dμ`:

* `hasSum_integral_mul_gaussGen`: `∫ f e^{zY - z²/2} dμ = ∑ₙ zⁿ/n! cₙ` (an unconditional sum);
* `norm_integral_mul_gaussGen_le`: `|∫ f e^{zY-z²/2} dμ| ≤ ‖f‖_{L²} e^{|z|²/2}`;
* `norm_integral_mul_hermiteC_le`: `|cₙ| ≤ ‖f‖_{L²} √(n!)`;
* `summable_pow_div_sqrt_factorial`: `∑ rⁿ/√(n!) < ∞`, the Weierstrass majorant that makes the
  expansion converge uniformly on bounded sets of `z`.

The key computation is `integral_norm_gaussGen_sub_hermitePartial_sq`: for a finite set `s` of
indices, `∫ |G_z(y) - ∑_{n ∈ s} zⁿ/n! Heₙ(y)|² dγ = e^{|z|²} - ∑_{n ∈ s} |z|^{2n}/n!`.
-/

open MeasureTheory ProbabilityTheory Polynomial Filter Complex
open scoped Real ComplexConjugate ENNReal Topology

noncomputable section

namespace ProbabilityTheory

/-! ### Two elementary `L²` facts -/

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
  rw [Complex.sq_norm, Complex.mul_conj]

theorem integrable_mul_conj_of_memLp {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hv' : MemLp (fun x => conj (v x)) 2 μ :=
    hv.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp)
  exact memLp_one_iff_integrable.mp (MemLp.mul' (r := 1) hv' hu)

theorem integral_mul_conj_self {u : α → ℂ} :
    ∫ x, u x * conj (u x) ∂μ = ((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun x => (ofReal_norm_sq (u x)).symm)

/-- The expansion of `∫ ‖u - v‖²` into the four `L²` products. -/
theorem ofReal_integral_norm_sub_sq {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ((∫ x, ‖u x - v x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      (∫ x, u x * conj (u x) ∂μ) - (∫ x, u x * conj (v x) ∂μ) -
        (∫ x, v x * conj (u x) ∂μ) + ∫ x, v x * conj (v x) ∂μ := by
  have huu := integrable_mul_conj_of_memLp hu hu
  have hvv := integrable_mul_conj_of_memLp hv hv
  have huv := integrable_mul_conj_of_memLp hu hv
  have hvu := integrable_mul_conj_of_memLp hv hu
  have hpt : ∀ x, ((‖u x - v x‖ ^ 2 : ℝ) : ℂ) =
      ((u x * conj (u x) - u x * conj (v x)) - v x * conj (u x)) + v x * conj (v x) := by
    intro x
    rw [ofReal_norm_sq, map_sub]
    ring
  have h1 : Integrable (fun x => u x * conj (u x) - u x * conj (v x)) μ := huu.sub huv
  have h2 : Integrable
      (fun x => u x * conj (u x) - u x * conj (v x) - v x * conj (u x)) μ := h1.sub hvu
  rw [← integral_complex_ofReal, integral_congr_ae (Eventually.of_forall hpt),
    integral_add h2 hvv, integral_sub h1 hvu, integral_sub huu huv]

/-- Cauchy–Schwarz for the integral of a product of two `L²` functions. -/
theorem norm_integral_mul_le_sqrt {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ‖∫ x, u x * v x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) := by
  have h1 : ‖∫ x, u x * v x ∂μ‖ ≤ ∫ x, ‖u x‖ * ‖v x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [norm_mul]
  have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (by simpa using hu) (by simpa using hv)
  simp_rw [Real.rpow_two] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end L2

/-! ### The generating function against the standard Gaussian -/

/-- The generating function `G_z(y) = e^{zy - z²/2}` of the Hermite polynomials. -/
def gaussGen (z : ℂ) (y : ℝ) : ℂ := Complex.exp (z * y - z ^ 2 / 2)

/-- The probabilists' Hermite polynomial `Heₙ` as a complex-valued function on `ℝ`. -/
def hermiteC (n : ℕ) (y : ℝ) : ℂ := (((hermiteR n).eval y : ℝ) : ℂ)

theorem continuous_gaussGen (z : ℂ) : Continuous (gaussGen z) := by
  unfold gaussGen; fun_prop

theorem continuous_hermiteC (n : ℕ) : Continuous (hermiteC n) := by
  unfold hermiteC; fun_prop

theorem conj_hermiteC (n : ℕ) (y : ℝ) : conj (hermiteC n y) = hermiteC n y :=
  Complex.conj_ofReal _

theorem gaussGen_eq (z : ℂ) (y : ℝ) :
    gaussGen z y = Complex.exp (-(z ^ 2 / 2)) * Complex.exp (z * y) := by
  rw [gaussGen, ← Complex.exp_add]
  ring_nf

theorem conj_gaussGen (z : ℂ) (y : ℝ) : conj (gaussGen z y) = gaussGen (conj z) y := by
  rw [gaussGen, gaussGen, ← Complex.exp_conj]
  congr 1
  simp [map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]

theorem gaussGen_mul_gaussGen (z w : ℂ) (y : ℝ) :
    gaussGen z y * gaussGen w y =
      Complex.exp (-((z ^ 2 + w ^ 2) / 2)) * Complex.exp ((z + w) * y) := by
  rw [gaussGen, gaussGen, ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- `conj z * z` is the squared norm. -/
theorem conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-! ### Integrability -/

/-- `P(y) G_z(y)` is integrable against the standard Gaussian. -/
theorem integrable_eval_mul_gaussGen (P : ℝ[X]) (z : ℂ) :
    Integrable (fun y : ℝ => ((P.eval y : ℝ) : ℂ) * gaussGen z y) (gaussianReal 0 1) := by
  refine ((integrable_gaussianReal_eval_mul_cexp P z).const_mul
    (Complex.exp (-(z ^ 2 / 2)))).congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gaussGen_eq]
  ring

theorem integrable_gaussGen_mul_gaussGen (z w : ℂ) :
    Integrable (fun y : ℝ => gaussGen z y * gaussGen w y) (gaussianReal 0 1) := by
  refine ((integrable_gaussianReal_eval_mul_cexp 1 (z + w)).const_mul
    (Complex.exp (-((z ^ 2 + w ^ 2) / 2)))).congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gaussGen_mul_gaussGen]
  simp

theorem integrable_norm_gaussGen_sq (z : ℂ) :
    Integrable (fun y : ℝ => ‖gaussGen z y‖ ^ 2) (gaussianReal 0 1) := by
  have h : Integrable (fun y : ℝ => gaussGen z y * conj (gaussGen z y)) (gaussianReal 0 1) := by
    refine (integrable_gaussGen_mul_gaussGen z (conj z)).congr
      (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [conj_gaussGen]
  refine h.re.congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [← ofReal_norm_sq]
  exact Complex.ofReal_re _

theorem memLp_two_gaussGen (z : ℂ) : MemLp (gaussGen z) 2 (gaussianReal 0 1) :=
  (memLp_two_iff_integrable_sq_norm (continuous_gaussGen z).aestronglyMeasurable).mpr
    (integrable_norm_gaussGen_sq z)

theorem norm_hermiteC_sq (n : ℕ) (y : ℝ) :
    ‖hermiteC n y‖ ^ 2 = (hermiteR n).eval y * (hermiteR n).eval y := by
  rw [hermiteC, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]

theorem memLp_two_hermiteC (n : ℕ) : MemLp (hermiteC n) 2 (gaussianReal 0 1) := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_hermiteC n).aestronglyMeasurable).mpr ?_
  refine (integrable_gaussianReal_eval (hermiteR n * hermiteR n)).congr
    (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [eval_mul, ← norm_hermiteC_sq]

/-! ### The three integrals -/

/-- `∫ |G_z|² dγ = e^{|z|²}`. -/
theorem integral_norm_gaussGen_sq (z : ℂ) :
    ∫ y, ‖gaussGen z y‖ ^ 2 ∂(gaussianReal 0 1) = Real.exp (‖z‖ ^ 2) := by
  have h : ∫ y, gaussGen z y * conj (gaussGen z y) ∂(gaussianReal 0 1) =
      ((Real.exp (‖z‖ ^ 2) : ℝ) : ℂ) := by
    rw [integral_congr_ae (g := fun y : ℝ => Complex.exp (-((z ^ 2 + (conj z) ^ 2) / 2)) *
        Complex.exp ((z + conj z) * y))
      (Eventually.of_forall fun y => by rw [conj_gaussGen, gaussGen_mul_gaussGen]),
      integral_const_mul, integral_gaussianReal_cexp, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    have hzz := conj_mul_self_eq z
    linear_combination hzz
  rw [integral_mul_conj_self] at h
  exact_mod_cast h

/-- `∫ Heₙ G_z dγ = zⁿ`. -/
theorem integral_hermiteC_mul_gaussGen (n : ℕ) (z : ℂ) :
    ∫ y, hermiteC n y * gaussGen z y ∂(gaussianReal 0 1) = z ^ n := by
  have h := integral_gaussianReal_hermiteR_mul_cexp n z
  rw [integral_congr_ae (g := fun y : ℝ => Complex.exp (-(z ^ 2 / 2)) *
      ((((hermiteR n).eval y : ℝ) : ℂ) * Complex.exp (z * y)))
    (Eventually.of_forall fun y => by rw [hermiteC, gaussGen_eq]; ring),
    integral_const_mul, h,
    show Complex.exp (-(z ^ 2 / 2)) * (z ^ n * Complex.exp (z ^ 2 / 2)) =
      z ^ n * (Complex.exp (-(z ^ 2 / 2)) * Complex.exp (z ^ 2 / 2)) by ring,
    ← Complex.exp_add, show -(z ^ 2 / 2) + z ^ 2 / 2 = 0 by ring]
  simp

/-- Orthogonality of the Hermite polynomials, complexified. -/
theorem integral_hermiteC_mul_hermiteC (m n : ℕ) :
    ∫ y, hermiteC m y * hermiteC n y ∂(gaussianReal 0 1) =
      if m = n then ((n.factorial : ℝ) : ℂ) else 0 := by
  have h := integral_gaussianReal_hermiteR_mul_hermiteR m n
  rw [integral_congr_ae (g := fun y : ℝ =>
      (((hermiteR m).eval y * (hermiteR n).eval y : ℝ) : ℂ))
    (Eventually.of_forall fun y => by simp [hermiteC]), integral_complex_ofReal, h]
  split <;> simp

theorem integrable_hermiteC_mul_gaussGen (n : ℕ) (z : ℂ) :
    Integrable (fun y : ℝ => hermiteC n y * gaussGen z y) (gaussianReal 0 1) :=
  integrable_eval_mul_gaussGen (hermiteR n) z

theorem integrable_hermiteC_mul_hermiteC (m n : ℕ) :
    Integrable (fun y : ℝ => hermiteC m y * hermiteC n y) (gaussianReal 0 1) := by
  refine (integrable_gaussianReal_eval (hermiteR m * hermiteR n)).ofReal.congr
    (Eventually.of_forall fun y => ?_)
  dsimp only
  simp [hermiteC, eval_mul]

/-! ### The partial sums of the Hermite expansion -/

/-- The partial sum `∑_{n ∈ s} zⁿ/n! Heₙ(y)` of the Hermite expansion of `G_z`. -/
def hermitePartial (s : Finset ℕ) (z : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * hermiteC n y

/-- The partial sum `∑_{n ∈ s} |z|^{2n}/n!` of the squared norms. -/
def hermiteSq (s : Finset ℕ) (z : ℂ) : ℝ :=
  ∑ n ∈ s, (‖z‖ ^ 2) ^ n / (n.factorial : ℝ)

theorem continuous_hermitePartial (s : Finset ℕ) (z : ℂ) : Continuous (hermitePartial s z) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_hermiteC n)

theorem memLp_two_hermitePartial (s : Finset ℕ) (z : ℂ) :
    MemLp (hermitePartial s z) 2 (gaussianReal 0 1) := by
  have hfun : hermitePartial s z =
      fun y : ℝ => ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * hermiteC n y := rfl
  rw [hfun]
  exact memLp_finsetSum s fun n _ => (memLp_two_hermiteC n).const_mul _

theorem conj_hermitePartial (s : Finset ℕ) (z : ℂ) (y : ℝ) :
    conj (hermitePartial s z y) = ∑ n ∈ s, conj (z ^ n / (n.factorial : ℂ)) * hermiteC n y := by
  rw [hermitePartial, map_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [map_mul, conj_hermiteC]

theorem integral_gaussGen_mul_conj_hermitePartial (s : Finset ℕ) (z : ℂ) :
    ∫ y, gaussGen z y * conj (hermitePartial s z y) ∂(gaussianReal 0 1) =
      ((hermiteSq s z : ℝ) : ℂ) := by
  rw [integral_congr_ae (g := fun y : ℝ =>
      ∑ n ∈ s, conj (z ^ n / (n.factorial : ℂ)) * (hermiteC n y * gaussGen z y))
    (Eventually.of_forall fun y => by
      rw [conj_hermitePartial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring),
    integral_finsetSum _ fun n _ => (integrable_hermiteC_mul_gaussGen n z).const_mul _,
    hermiteSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_hermiteC_mul_gaussGen, map_div₀, map_pow,
    Complex.conj_natCast, div_mul_eq_mul_div, ← mul_pow, conj_mul_self_eq]
  push_cast
  ring

theorem integral_hermitePartial_mul_conj_gaussGen (s : Finset ℕ) (z : ℂ) :
    ∫ y, hermitePartial s z y * conj (gaussGen z y) ∂(gaussianReal 0 1) =
      ((hermiteSq s z : ℝ) : ℂ) := by
  rw [integral_congr_ae (g := fun y : ℝ =>
      ∑ n ∈ s, (z ^ n / (n.factorial : ℂ)) * (hermiteC n y * gaussGen (conj z) y))
    (Eventually.of_forall fun y => by
      rw [conj_gaussGen, hermitePartial, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring),
    integral_finsetSum _ fun n _ => (integrable_hermiteC_mul_gaussGen n (conj z)).const_mul _,
    hermiteSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_hermiteC_mul_gaussGen, div_mul_eq_mul_div, ← mul_pow,
    mul_comm z (conj z), conj_mul_self_eq]
  push_cast
  ring

theorem integral_hermitePartial_mul_conj_hermitePartial (s : Finset ℕ) (z : ℂ) :
    ∫ y, hermitePartial s z y * conj (hermitePartial s z y) ∂(gaussianReal 0 1) =
      ((hermiteSq s z : ℝ) : ℂ) := by
  rw [integral_congr_ae (g := fun y : ℝ =>
      ∑ n ∈ s, ∑ m ∈ s, (z ^ n / (n.factorial : ℂ)) * conj (z ^ m / (m.factorial : ℂ)) *
        (hermiteC n y * hermiteC m y))
    (Eventually.of_forall fun y => by
      rw [conj_hermitePartial, hermitePartial, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring),
    integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
      (integrable_hermiteC_mul_hermiteC n m).const_mul _,
    hermiteSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun m _ => (integrable_hermiteC_mul_hermiteC n m).const_mul _]
  have hterm : ∀ m ∈ s,
      (∫ y, (z ^ n / (n.factorial : ℂ)) * conj (z ^ m / (m.factorial : ℂ)) *
        (hermiteC n y * hermiteC m y) ∂(gaussianReal 0 1)) =
      if n = m then (((‖z‖ ^ 2) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) else 0 := by
    intro m _
    rw [integral_const_mul, integral_hermiteC_mul_hermiteC]
    split_ifs with h
    · subst h
      have hfac : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      have hz : z ^ n * (conj z) ^ n = ((‖z‖ ^ 2 : ℝ) : ℂ) ^ n := by
        rw [← mul_pow, mul_comm z (conj z), conj_mul_self_eq]
      rw [map_div₀, map_pow, Complex.conj_natCast, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_natCast]
      field_simp
      linear_combination hz
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq s n, if_pos hn]

/-- The exact `L²` error of the Hermite partial sum:
`∫ |G_z - ∑_{n ∈ s} zⁿ/n! Heₙ|² dγ = e^{|z|²} - ∑_{n ∈ s} |z|^{2n}/n!`. -/
theorem integral_norm_gaussGen_sub_hermitePartial_sq (s : Finset ℕ) (z : ℂ) :
    ∫ y, ‖gaussGen z y - hermitePartial s z y‖ ^ 2 ∂(gaussianReal 0 1) =
      Real.exp (‖z‖ ^ 2) - hermiteSq s z := by
  have h := ofReal_integral_norm_sub_sq (memLp_two_gaussGen z) (memLp_two_hermitePartial s z)
  rw [integral_mul_conj_self, integral_norm_gaussGen_sq,
    integral_gaussGen_mul_conj_hermitePartial, integral_hermitePartial_mul_conj_gaussGen,
    integral_hermitePartial_mul_conj_hermitePartial] at h
  have h2 : ((∫ y, ‖gaussGen z y - hermitePartial s z y‖ ^ 2 ∂(gaussianReal 0 1) : ℝ) : ℂ) =
      ((Real.exp (‖z‖ ^ 2) - hermiteSq s z : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h2

/-- `∑ₙ |z|^{2n}/n! = e^{|z|²}`. -/
theorem hasSum_hermiteSq (z : ℂ) :
    HasSum (fun n : ℕ => (‖z‖ ^ 2) ^ n / (n.factorial : ℝ)) (Real.exp (‖z‖ ^ 2)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp _

/-! ### The Weierstrass majorant -/

/-- `∑ rⁿ/√(n!)` converges: by the arithmetic–geometric mean inequality
`rⁿ/√(n!) = √((2r²)ⁿ/n! · 2⁻ⁿ) ≤ ((2r²)ⁿ/n! + 2⁻ⁿ)/2`. -/
theorem summable_pow_div_sqrt_factorial {r : ℝ} (hr : 0 ≤ r) :
    Summable fun n : ℕ => r ^ n / Real.sqrt (n.factorial : ℝ) := by
  have hgeom : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hexp : Summable fun n : ℕ => (2 * r ^ 2) ^ n / (n.factorial : ℝ) :=
    Real.summable_pow_div_factorial _
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((hexp.add hgeom).div_const 2)
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hna : (0 : ℝ) ≤ (2 * r ^ 2) ^ n / (n.factorial : ℝ) := by positivity
  have hnb : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
  have hab : (2 * r ^ 2) ^ n / (n.factorial : ℝ) * ((1 : ℝ) / 2) ^ n
      = (r ^ n / Real.sqrt (n.factorial : ℝ)) ^ 2 := by
    have h1 : Real.sqrt (n.factorial : ℝ) ^ 2 = (n.factorial : ℝ) := Real.sq_sqrt hfac.le
    have h2 : (r ^ n / Real.sqrt (n.factorial : ℝ)) ^ 2 = (r ^ n) ^ 2 / (n.factorial : ℝ) := by
      rw [div_pow, h1]
    have h3 : (2 * r ^ 2) ^ n * ((1 : ℝ) / 2) ^ n = (r ^ 2) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    rw [h2, div_mul_eq_mul_div, h3]
    congr 1
    ring
  have hkey : Real.sqrt ((2 * r ^ 2) ^ n / (n.factorial : ℝ) * ((1 : ℝ) / 2) ^ n) ≤
      ((2 * r ^ 2) ^ n / (n.factorial : ℝ) + ((1 : ℝ) / 2) ^ n) / 2 := by
    have h2 := two_mul_le_add_sq (Real.sqrt ((2 * r ^ 2) ^ n / (n.factorial : ℝ)))
      (Real.sqrt (((1 : ℝ) / 2) ^ n))
    rw [Real.sq_sqrt hna, Real.sq_sqrt hnb] at h2
    rw [Real.sqrt_mul hna]
    linarith
  rw [hab, Real.sqrt_sq (by positivity)] at hkey
  exact hkey

/-! ### A standard Gaussian coordinate on a measure space -/

section Coordinate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}

/-- `Y` is a standard Gaussian coordinate for `μ`: measurable with law `𝒩(0,1)`. -/
structure IsStdGaussianCoord (μ : Measure Ω) (Y : Ω → ℝ) : Prop where
  /-- `Y` is measurable. -/
  measurable : Measurable Y
  /-- The law of `Y` is `𝒩(0,1)`. -/
  map_eq : μ.map Y = gaussianReal 0 1

theorem IsStdGaussianCoord.integral_comp (hY : IsStdGaussianCoord μ Y) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (hg : AEStronglyMeasurable g (gaussianReal 0 1)) :
    ∫ x, g (Y x) ∂μ = ∫ y, g y ∂(gaussianReal 0 1) := by
  rw [← hY.map_eq, integral_map hY.measurable.aemeasurable (by rwa [hY.map_eq])]

theorem IsStdGaussianCoord.memLp_comp (hY : IsStdGaussianCoord μ Y) {g : ℝ → ℂ}
    (hg : MemLp g 2 (gaussianReal 0 1)) : MemLp (fun x => g (Y x)) 2 μ := by
  have h : MemLp g 2 (μ.map Y) := by rwa [hY.map_eq]
  simpa [Function.comp_def] using h.comp_of_map hY.measurable.aemeasurable

theorem IsStdGaussianCoord.isProbabilityMeasure (hY : IsStdGaussianCoord μ Y) :
    IsProbabilityMeasure μ := by
  constructor
  have h : (μ.map Y) Set.univ = 1 := by rw [hY.map_eq]; simp
  rwa [Measure.map_apply hY.measurable MeasurableSet.univ, Set.preimage_univ] at h

variable (hY : IsStdGaussianCoord μ Y) {f : Ω → ℂ} (hf : MemLp f 2 μ)
include hY hf

theorem integrable_mul_hermiteC_comp (n : ℕ) :
    Integrable (fun x => f x * hermiteC n (Y x)) μ :=
  memLp_one_iff_integrable.mp
    (MemLp.mul' (r := 1) (hY.memLp_comp (memLp_two_hermiteC n)) hf)

theorem integrable_mul_gaussGen_comp (z : ℂ) :
    Integrable (fun x => f x * gaussGen z (Y x)) μ :=
  memLp_one_iff_integrable.mp
    (MemLp.mul' (r := 1) (hY.memLp_comp (memLp_two_gaussGen z)) hf)

/-- The `L²` error of the Hermite partial sum, paired with `f`. -/
theorem norm_integral_mul_gaussGen_sub_le (z : ℂ) (s : Finset ℕ) :
    ‖(∫ x, f x * gaussGen z (Y x) ∂μ) -
        ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (Real.exp (‖z‖ ^ 2) - hermiteSq s z) := by
  have hg : MemLp (fun x => gaussGen z (Y x) - hermitePartial s z (Y x)) 2 μ :=
    hY.memLp_comp ((memLp_two_gaussGen z).sub (memLp_two_hermitePartial s z))
  have hsplit : (∫ x, f x * gaussGen z (Y x) ∂μ) -
      ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ =
      ∫ x, f x * (gaussGen z (Y x) - hermitePartial s z (Y x)) ∂μ := by
    have h1 := integrable_mul_gaussGen_comp hY hf z
    have h2 : Integrable (fun x => f x * hermitePartial s z (Y x)) μ :=
      memLp_one_iff_integrable.mp
        (MemLp.mul' (r := 1) (hY.memLp_comp (memLp_two_hermitePartial s z)) hf)
    have e1 : ∫ x, f x * (gaussGen z (Y x) - hermitePartial s z (Y x)) ∂μ =
        (∫ x, f x * gaussGen z (Y x) ∂μ) - ∫ x, f x * hermitePartial s z (Y x) ∂μ := by
      rw [← integral_sub h1 h2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have e3 : (fun x => f x * hermitePartial s z (Y x)) =
        fun x => ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * (f x * hermiteC n (Y x)) := by
      funext x
      rw [hermitePartial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    have e2 : ∫ x, f x * hermitePartial s z (Y x) ∂μ =
        ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ := by
      rw [e3, integral_finsetSum _ fun n _ => (integrable_mul_hermiteC_comp hY hf n).const_mul _]
      exact Finset.sum_congr rfl fun n _ => by rw [integral_const_mul]
    rw [e1, e2]
  rw [hsplit]
  refine (norm_integral_mul_le_sqrt hf hg).trans (le_of_eq ?_)
  congr 1
  rw [hY.integral_comp (E := ℝ) (fun y => ‖gaussGen z y - hermitePartial s z y‖ ^ 2)
    (((continuous_gaussGen z).sub (continuous_hermitePartial s z)).norm.pow
      2).aestronglyMeasurable,
    integral_norm_gaussGen_sub_hermitePartial_sq]

/-- The Hermite expansion of `∫ f G_z(Y) dμ`, as an unconditional sum. -/
theorem hasSum_integral_mul_gaussGen (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ)
      (∫ x, f x * gaussGen z (Y x) ∂μ) := by
  have hmain : Tendsto
      (fun s : Finset ℕ =>
        ∑ n ∈ s, z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ)
      atTop (𝓝 (∫ x, f x * gaussGen z (Y x) ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ s : Finset ℕ,
        ‖(∑ n ∈ s, z ^ n / (n.factorial : ℂ) * ∫ x, f x * hermiteC n (Y x) ∂μ) -
            ∫ x, f x * gaussGen z (Y x) ∂μ‖ ≤
          Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) *
            Real.sqrt (Real.exp (‖z‖ ^ 2) - hermiteSq s z) := by
      intro s
      rw [norm_sub_rev]
      exact norm_integral_mul_gaussGen_sub_le hY hf z s
    refine squeeze_zero (fun s => norm_nonneg _) hbound ?_
    have h1 : Tendsto (fun s : Finset ℕ => hermiteSq s z) atTop (𝓝 (Real.exp (‖z‖ ^ 2))) :=
      hasSum_hermiteSq z
    have h2 : Tendsto (fun s : Finset ℕ => Real.exp (‖z‖ ^ 2) - hermiteSq s z) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : Finset ℕ => Real.exp (‖z‖ ^ 2)) atTop
          (𝓝 (Real.exp (‖z‖ ^ 2))) := tendsto_const_nhds
      simpa using hc.sub h1
    have h3 : Tendsto (fun s : Finset ℕ =>
        Real.sqrt (Real.exp (‖z‖ ^ 2) - hermiteSq s z)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h2
    simpa using h3.const_mul (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ))
  exact hmain

/-- The bound `|∫ f G_z(Y) dμ| ≤ ‖f‖_{L²} e^{|z|²/2}`. -/
theorem norm_integral_mul_gaussGen_le (z : ℂ) :
    ‖∫ x, f x * gaussGen z (Y x) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.exp (‖z‖ ^ 2 / 2) := by
  have h := norm_integral_mul_le_sqrt hf (hY.memLp_comp (memLp_two_gaussGen z))
  rw [hY.integral_comp (E := ℝ) (fun y => ‖gaussGen z y‖ ^ 2)
    ((continuous_gaussGen z).norm.pow 2).aestronglyMeasurable, integral_norm_gaussGen_sq] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  have hsq : Real.exp (‖z‖ ^ 2) = Real.exp (‖z‖ ^ 2 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- The bound `|∫ f Heₙ(Y) dμ| ≤ ‖f‖_{L²} √(n!)`. -/
theorem norm_integral_mul_hermiteC_le (n : ℕ) :
    ‖∫ x, f x * hermiteC n (Y x) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (n.factorial : ℝ) := by
  have h := norm_integral_mul_le_sqrt hf (hY.memLp_comp (memLp_two_hermiteC n))
  rw [hY.integral_comp (E := ℝ) (fun y => ‖hermiteC n y‖ ^ 2)
    ((continuous_hermiteC n).norm.pow 2).aestronglyMeasurable] at h
  have h2 := integral_gaussianReal_hermiteR_mul_hermiteR n n
  rw [if_pos rfl] at h2
  rw [show (∫ y, ‖hermiteC n y‖ ^ 2 ∂(gaussianReal 0 1)) = (n.factorial : ℝ) by
    rw [← h2]; exact integral_congr_ae (Eventually.of_forall fun y => norm_hermiteC_sq n y)] at h
  exact h

end Coordinate

end ProbabilityTheory
