import OperatorRidgeletBlueprint.Blueprint

/-!
# Browser blueprint for the operator-ridgelet development

The document is assembled in `OperatorRidgeletBlueprint.Blueprint` from one chapter per
manuscript section (`Chapters/Networks`, `Transform`, `Reconstruction`, `Tempered`, `Sampling`,
`Examples`, with the appendices folded in) and the infrastructure chapter `Chapters/Roadmap`,
and rendered through `OperatorRidgeletBlueprintMain.lean` by `lake exe vbp build`.  The Lean
declarations live in the sibling Lake project `../OperatorRidgelet`, a path dependency of this
project; node labels are the manuscript labels of `OperatorRidgelet/comparator/paper.json`.
-/
