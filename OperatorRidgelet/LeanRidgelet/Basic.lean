-- Vendored from https://github.com/shosonoda/lean-ridgelet
-- revision e9af79a1042c19891a9991addb92b75947886343, path LeanRidgelet/Basic.lean
-- Copied verbatim; do not edit here.
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Basic definitions for the ridgelet formalization

This file fixes the scalar field and the finite-dimensional input space used by the
depth-two theory. Analytic constructions are kept in separate files.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- The input space `ℝᵐ`, represented using Mathlib's Euclidean-space API. -/
abbrev InputSpace (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Complex-valued `L²` on a measured space. -/
abbrev L2 (α : Type*) [MeasurableSpace α] (μ : Measure α) := Lp ℂ 2 μ

/-- Bochner `L²` with values in a normed additive group. -/
abbrev BochnerL2 (α E : Type*) [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) := Lp E 2 μ

/-- The target Hilbert space `L²(ℝᵐ)`. -/
abbrev TargetSpace (m : ℕ) := L2 (InputSpace m) volume

end LeanRidgelet
