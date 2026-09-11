# Uniformity needed for the integral clause of Lemma 6.5

The corrected, verified statement `lem_ray_regular_examples_c_ii` requires a common smooth
open neighbourhood and finite-valued derivative majorants. The earlier statement allowed
infinite majorants on a set of direction measure zero, which was insufficient for its
pointwise smoothness conclusion. The counterexample below records why the correction is needed.

Take `H = ℝ`, `ν = 0`, `I = {1}`, and the probability measure on `ℕ` with masses
`m({n}) = 2^(-n-1)`. Set

```
G(n, x) = cos(2^n (x - 1)).
```

View these real values in `ℂ`. The family is jointly measurable and bounded by one.
Every member is globally smooth, hence satisfies `IsRegularAlongRays ν I`:
its ray moments are all zero. For every derivative order the proposed uniform
majorant can be `h(a) = ∞`; its weighted integral against `ν = 0` is zero.
Thus every hypothesis of the earlier Lean statement holds.

The integral is the uniformly convergent series

```
F(x) = ∑ n ≥ 0, 2^(-n-1) cos(2^n (x - 1)).
```

It is symmetric around `x = 1`. If differentiable there, its derivative would be zero.
For `h_N = π 2^(-N)`, every summand of `F(1+h_N) - F(1)` is nonpositive, and its
`n = N` summand equals `-2^(-N)`. Consequently

```
(F(1+h_N) - F(1)) / h_N ≤ -1/π.
```

Since `h_N` tends to zero, this contradicts differentiability at one. The ray with
direction `a = 1` therefore fails the required conclusion. The same counterexample
works with any compact window containing one, including a symmetric window away
from zero.

A sufficient repair adds differentiation hypotheses separate from moment
integrability. For each direction `a`, one can require a common open neighbourhood `U_a`
of `I` on which all functions `ω ↦ G(y, ω a)` are smooth, and, locally on `U_a`,
integrable bounds in `y` for every derivative order. For example, for every compact
`K ⊆ U_a` and every `k`, require an `m`-integrable function `B_{a,K,k}(y)` bounding
the norm of the `k`-th derivative uniformly for `ω ∈ K`. This gives differentiation
under the Bochner integral and smoothness on `U_a`. Retain the weighted uniform
ray-moment majorants on `I` to obtain the finite moments by Tonelli and the integral
norm inequality. Joint measurability of the derivative family, or assumptions that
imply it via measurable difference quotients, must also be available.

The corrected Challenge and Paper statements require a common smooth open neighbourhood
`U`, together with a finite-valued cumulative bound `h : H → NNReal` for each order.
The proof differentiates the Bochner integral on `U` and estimates the resulting ray
moments by `m(univ)` times the majorant moments. The counterexample does not affect
the finite-sum clause of the lemma or the already verified main theorems.
