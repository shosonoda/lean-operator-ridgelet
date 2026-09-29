import VersoBlueprintTests.BlueprintImportedFacets.Statement
import VersoBlueprintTests.BlueprintImportedFacets.Proof

open Lean
open Verso.Genre
open Verso.Genre.Manual
open Informal

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let conflicts ← Informal.Environment.importedConflicts
  let node ← Informal.Environment.getNode? (Name.mkSimple "imported-facets:result")
  pure <| conflicts.isEmpty && node.any fun n =>
    n.statement.any (·.hasBody) && n.proof.any (·.hasBody)

#doc (Manual) "Combined statement and appendix" =>

{include 0 VersoBlueprintTests.BlueprintImportedFacets.Statement}
{include 0 VersoBlueprintTests.BlueprintImportedFacets.Proof}
{blueprint_graph}
{blueprint_summary}
