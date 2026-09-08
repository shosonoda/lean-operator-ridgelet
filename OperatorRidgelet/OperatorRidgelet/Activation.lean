import LeanRidgelet.Activation.ReLU

/-!
# ReLU identities for exact spectral representations

The signed pair of ReLU neurons is exactly linear.  This is the algebraic core of the exact
spectral ReLU representation of the elliptic solution operator in the manuscript.
-/

open scoped BigOperators

namespace OperatorRidgelet

open LeanRidgelet

theorem relu_sub_relu_neg (x : ℝ) : relu x - relu (-x) = x := by
  simp only [relu]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right hx, max_eq_left (by linarith)]
    linarith

/-- A finite signed-pair ReLU network with spectral coefficients. -/
noncomputable def spectralReLUNetwork {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [Module ℝ E] (s : Finset ι) (coeff coordinate : ι → ℝ)
    (basis : ι → E) : E :=
  ∑ i ∈ s, (coeff i * (relu (coordinate i) - relu (-coordinate i))) • basis i

theorem spectralReLUNetwork_eq {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [Module ℝ E] (s : Finset ι) (coeff coordinate : ι → ℝ)
    (basis : ι → E) :
    spectralReLUNetwork s coeff coordinate basis =
      ∑ i ∈ s, (coeff i * coordinate i) • basis i := by
  simp only [spectralReLUNetwork, relu_sub_relu_neg]

end OperatorRidgelet
