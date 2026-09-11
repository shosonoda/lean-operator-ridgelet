# Remaining distributional inversion proof

Corollary `cor:finite-backprojection` parts (i), (ii), (iii), (v), and (vi) are proved.
Part (iv) retains its original statement and remains unverified.

The available lemmas in `FiniteDim/Basic.lean` prove radial homogeneity, integrability of
Schwartz Fourier transforms against the direction measure, the Riesz multiplier formula,
the pivot-measure pairing, and ordinary Fourier inversion with the angular normalization.

The remaining analytic input is the following general Fourier estimate:

- [ ] For every finite-dimensional Euclidean space, Schwartz function `ψ`, and `β > 0`,
  prove that the Fourier transform of `ξ ↦ ‖ξ‖ ^ β * ψ ξ` is integrable.
- [ ] Apply Fourier inversion to identify the Fourier transform of
  `fracLaplacian (β / 2) φ` with `‖ξ‖ ^ β * fourier φ ξ`.
- [ ] Use Fubini with the integrable density
  `mixtureConst m α * ‖ξ‖ ^ (α - m) * fourier g ξ` and the integrable fractional
  Laplacian of `φ`. Cancel the reciprocal powers almost everywhere, apply Schwartz
  Fourier inversion, and cancel the positive frame and admissibility constants.

One route to the first step is a smooth dyadic partition near the Fourier origin. On each
annulus the multiplier is smooth; after rescaling, its Fourier `L¹` norm is bounded by a
fixed constant times `2 ^ (-j * β)`. The resulting summable sequence gives the estimate.
The part away from the origin is Schwartz. An alternative is the heat-semigroup integral
for fractional powers, with the `L¹` bound `min(C * t, 2 * ‖φ‖₁)` when `0 < β < 2`, followed
by reduction of general positive powers using integer Laplacians.

The Fourier multiplier is generally not smooth at zero, so it must not be treated as a
Schwartz function. The Riesz potential is not generally in unweighted `L²` either; an
unqualified use of `L²` Parseval does not cover the full range `0 < α < m`.
