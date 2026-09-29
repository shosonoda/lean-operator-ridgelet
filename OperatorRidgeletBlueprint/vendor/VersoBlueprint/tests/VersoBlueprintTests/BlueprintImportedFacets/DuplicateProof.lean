import VersoBlueprintTests.BlueprintImportedFacets.Proof
import VersoBlueprintTests.BlueprintImportedFacets.OtherProof

open Lean

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let conflicts ← Informal.Environment.importedConflicts
  pure <| conflicts.contains {
    kind := .node, label := Name.mkSimple "imported-facets:result" }

/-- error: Duplicate imported blueprint node label '«imported-facets:result»' -/
#guard_msgs in
run_cmd Informal.Environment.reportImportedConflicts
