/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintSummaryLinks.Shared

namespace Verso.VersoBlueprintTests.BlueprintSummaryLinks.Diagnostics

open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintSummaryLinks.Shared

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString manualImpls (summaryDiagnosticsSyntheticDoc false)
    pure (
      !hasSubstr out "Maintainer diagnostics" &&
      !hasSubstr out "Render failures (1)" &&
      !hasSubstr out "synthetic render failure"
    )

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString manualImpls (summaryDiagnosticsSyntheticDoc true)
    pure (
      hasSubstr out "Maintainer diagnostics" &&
      hasSubstr out "Render failures</span><span class=\"bp_summary_value\">1</span>" &&
      hasSubstr out "Render failures (1)" &&
      hasSubstr out "External render failed for " &&
      hasSubstr out "Diag.renderFail" &&
      hasSubstr out "[render failure]" &&
      hasSubstr out "synthetic render failure"
    )

end Verso.VersoBlueprintTests.BlueprintSummaryLinks.Diagnostics
