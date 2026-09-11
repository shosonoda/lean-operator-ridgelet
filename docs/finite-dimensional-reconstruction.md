# Finite-dimensional distributional reconstruction

All six parts of Corollary `cor:finite-backprojection` are proved.

`FiniteDim/Basic.lean` establishes radial homogeneity, integrability of Schwartz
Fourier transforms against the direction measure, the Riesz multiplier formula,
the pivot-measure pairing, and ordinary Fourier inversion with angular normalization.
`FiniteDim/Reconstruction.lean` proves the remaining distributional inversion formula.

The essential analytic input is in `ToMathlib/FractionalSchwartz.lean`: for every
positive `β` and Schwartz function `ψ` on a finite-dimensional Euclidean space,
the Fourier and inverse Fourier transforms of `ξ ↦ ‖ξ‖ ^ β * ψ ξ` are integrable.
A smooth dyadic partition near zero yields annular terms with Fourier `L¹` norms
bounded by a constant times `2 ^ (-j * β)`. Convolution controls multiplication
by the Schwartz test function, and the geometric series is summable. Away from
zero, a smooth positive regularization of the norm has temperate growth.

Fourier inversion therefore identifies the Fourier transform of the fractional
Laplacian of a test function. Fubini pairs it with the integrable spectral density
of the frame representative, and the reciprocal norm powers cancel almost
everywhere. Schwartz Fourier inversion supplies the final pairing and the exact
angular-frequency constants.

The argument does not assume that a fractional norm multiplier is smooth at zero,
or that the Riesz potential belongs to unweighted `L²`.
