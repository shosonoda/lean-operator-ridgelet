import VersoManual
import VersoBlueprint.PreviewManifest
import PreviewRuntimeShowcase.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PreviewRuntimeShowcase.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
