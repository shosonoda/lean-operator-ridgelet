import OperatorRidgeletBlueprint.Blueprint

/-!
# Browser blueprint for the operator-ridgelet development

The document is assembled in `OperatorRidgeletBlueprint.Blueprint` from one chapter per
manuscript section (`Chapters/Networks`, `Transform`, `Reconstruction`, `Tempered`, `Sampling`,
`Examples`, with the appendices folded in), the infrastructure chapter `Chapters/Roadmap`, and
the generated comparator review `Chapters/Comparator` (written by
`scripts/gen-comparator-chapter.py` from the comparator data of `../OperatorRidgelet`; do not
edit it by hand), and rendered through `OperatorRidgeletBlueprintMain.lean` by `lake exe vbp build`.  The Lean
declarations live in the sibling Lake project `../OperatorRidgelet`, a path dependency of this
project; node labels are the manuscript labels of `OperatorRidgelet/comparator/paper.json`.
-/
