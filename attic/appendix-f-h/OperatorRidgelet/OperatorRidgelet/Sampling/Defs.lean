/-! Historical fragments; see the archive README for their original context. -/

/-- The sampled operator network `f_{op,N}(x) = (V/N) ∑_j h(A_j, b_j) n_{ℓ,A_j,b_j}(x)` of
Corollary `cor:D.7`: a finite-width operator network with the samples
`(A_j, b_j)` and outer weights `(V/N) h(A_j, b_j)`. -/
def sampledOperatorNetwork {N : ℕ} (σ : H → H) (ℓ : H) (V : ℝ)
    (h : OperatorRidgeParameter H → ℂ) (ω : Fin N → OperatorRidgeParameter H) : H → ℂ :=
  operatorFiniteNetwork σ ℓ (fun j => ((V / N : ℝ) : ℂ) • h (ω j)) (fun j => (ω j).1)
    (fun j => (ω j).2)

/-- The operator second moment `M_op² = ∫ (‖A^*ψ‖² + |⟪ψ, b⟫|²) p_op(dA, db)` of Corollary
`cor:D.7`. -/
def operatorSecondMoment [MeasurableSpace H] (ψ : H)
    (p : Measure (OperatorRidgeParameter H)) : ℝ :=
  ∫ q, (‖ContinuousLinearMap.adjoint q.1 ψ‖ ^ 2 + |⟪ψ, q.2⟫| ^ 2) ∂p
