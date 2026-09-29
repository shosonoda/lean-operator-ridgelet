import VersoManual
import VersoBlueprint.PreviewManifest
import OperatorRidgeletBlueprint.Blueprint
import OperatorRidgeletBlueprint.ManuscriptLayout

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 := do
  -- Read the index on each render: changes to JSON must not reuse compiled numbering.
  let index ← IO.FS.readFile "../OperatorRidgelet/comparator/paper.json"
  let document ← match OperatorRidgeletBlueprint.ManuscriptLayout.apply index
      (%doc OperatorRidgeletBlueprint.Blueprint) with
    | .ok document => pure document
    | .error message => throw (IO.userError message)
  Informal.PreviewManifest.blueprintMainWithPreviewData
    document
    args
    (extensionImpls := by exact extension_impls%)
    (config := { extraFilesHtml := [
      ("assets/figures/exp1.svg", "exp1.svg"),
      ("assets/figures/exp2.svg", "exp2.svg"),
      ("assets/figures/exp3.svg", "exp3.svg")] })
