import Mathlib.Tactic.TypeStar

/-!
# `Exists.choose` depends only on the predicate
-/

/-- Two witnesses chosen for the same predicate, written in two ways, coincide. -/
theorem Exists.choose_congr {α : Sort*} {p p' : α → Prop} (hp : p = p') (h : ∃ x, p x)
    (h' : ∃ x, p' x) : h.choose = h'.choose := by
  subst hp
  rfl
