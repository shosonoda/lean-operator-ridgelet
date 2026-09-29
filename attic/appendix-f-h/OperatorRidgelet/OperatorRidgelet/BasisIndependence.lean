/-! Historical fragments; see the archive README for their original context. -/

/-- **The Hilbert–Schmidt norm is the sum along every Hilbert basis.**  The intrinsic definition
of `hsNormSq` as a supremum over finite orthonormal families is computed by `∑ ‖A e_i‖²` along
any Hilbert basis. -/
theorem hsNormSq_eq_tsum (A : H →L[ℝ] H) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    hsNormSq A = ∑' i, ‖A (b i)‖ₑ ^ 2 :=
  ContinuousLinearMap.iSup_finset_sum_enorm_apply_sq A b

/-- The Hilbert–Schmidt norm as a real number, along any Hilbert basis. -/
theorem hsNorm_eq_sqrt_tsum (A : H →L[ℝ] H) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    hsNorm A = Real.sqrt (∑' i, ‖A (b i)‖ₑ ^ 2).toReal := by
  rw [hsNorm, hsNormSq_eq_tsum A b]
