# attic/lean

Lean files that are no longer part of the build.  They are kept for reference only and are not
imported by any Lake target.

- `HilbertCube.lean`, `HilbertCubeOperator.lean`: an exact countably-wide ReLU target on the
  binary Hilbert cube `[0,1]^ℕ` (compactness, continuity, `2^-N` truncation rate, and
  non-cylindricity), written in August 2026 as a small test case.  The manuscript revised on
  2026-09-08 no longer contains this example.  The files still refer to `OperatorRidgelet.HilbertCube`
  and `LeanRidgelet.relu` and compiled against Lean 4.32.0 / Mathlib v4.32.0 at that time.
