import VersoManual
import VersoBlueprint.PreviewManifest
import ProjectTemplate.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ProjectTemplate.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
