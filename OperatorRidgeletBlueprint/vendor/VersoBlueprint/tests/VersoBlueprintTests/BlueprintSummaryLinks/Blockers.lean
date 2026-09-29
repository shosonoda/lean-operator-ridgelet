/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintSummaryLinks.Shared

namespace Verso.VersoBlueprintTests.BlueprintSummaryLinks.Blockers

open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintSummaryLinks.Shared

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString manualImpls summaryBlockersDoc
    pure (
      hasSubstr out "Current blockers (2)" &&
      hasSubstr out "Missing external Lean declaration:" &&
      hasSubstr out "Declaration with sorry:" &&
      !hasSubstr out "Incomplete details ("
    )

end Verso.VersoBlueprintTests.BlueprintSummaryLinks.Blockers
