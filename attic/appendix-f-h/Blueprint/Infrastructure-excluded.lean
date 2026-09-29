:::theorem "roadmap:trace-and-determinant" (lean := "OperatorRidgelet.traceOf_eq_traceAlong, OperatorRidgelet.fredholmDet_eq_fredholmDetAlong, OperatorRidgelet.hsNormSq_eq_tsum") (uses := "aux:centered-gaussian")
For a positive operator the trace $`\sum_i\langle Pe_i,e_i\rangle` has the same value along
every Hilbert basis, the Fredholm determinant $`\prod_i(1+m_i)` of a positive trace-class
operator has the same value along every orthonormal eigenbasis, and the intrinsic
Hilbert–Schmidt norm equals $`\sum_n\|Ae_n\|^2` along every Hilbert basis. These are the
basis-independence obligations left open by the definitions of the trace, the determinant,
and the Hilbert–Schmidt class, and the three theorems above discharge them: the chosen basis
of `traceOf` and of `fredholmDet` is immaterial, and the supremum defining `hsNormSq` is
computed by the sum along any Hilbert basis. Mathlib has no positive square root of an
operator on a real Hilbert space (its continuous functional calculus is stated for complex
C\*-algebras), so the trace is compared along two bases through the orthonormal eigenbasis
that a convergent trace provides, the multiplicity of a nonzero eigenvalue is identified with
the trace of the orthogonal projection onto its eigenspace, and the Hilbert–Schmidt norm is
compared through the adjoint.
:::

:::theorem "roadmap:finite-dim-universality" (lean := "UniversalApproximation.Leshno.leshno_dense")
The finite-dimensional universal approximation theorem: for a continuous non-polynomial
$`\beta:\mathbb R\to\mathbb R`, finite linear combinations of $`\beta(\langle a,x\rangle+c)`
are dense in $`C(\mathbb R^m)` for uniform convergence on compact sets. The reduction argument
of {bpref "prop:F.3"}[] composes it with finite-rank projections. Mathlib does
not have it; the project vendors the formalization of Runje (Apache 2.0) under
`NeuralNetworkProofs/`.
:::
