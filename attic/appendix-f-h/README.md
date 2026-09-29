# Archived operator-parameter and general-measure extensions

These project-owned sources were removed from the active development on 2026-09-30.
They cover the former Section 2.2, Appendix F, Corollary D.7, and Theorem H.1.
Complete retired modules retain their source; mixed modules contain only the removed fragments.
Fragments require their original namespace, variables, and imports and are not standalone modules.
This directory is outside both Lake projects and is excluded from builds and source distributions.

The complete previous development is preserved by branch
`snapshot20260929before-pruning-appendix`, commit
`525a54cf4c341fdc5c303b7db93a6e21d101a27e`.
The retired finite-dimensional universality dependency is available in that historical revision;
its third-party sources are not duplicated here.

The scalar Lipschitz envelopes moved from `Architecture/Basic.lean` to `Network/Basic.lean`.
Finite-rank input projections, trace and Fredholm determinant identities, and the general-measure
lemmas needed by the Gaussian construction remain in the active project.
