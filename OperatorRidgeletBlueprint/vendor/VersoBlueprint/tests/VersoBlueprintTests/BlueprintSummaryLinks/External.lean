/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintSummaryLinks.Shared

namespace Verso.VersoBlueprintTests.BlueprintSummaryLinks.External

open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintSummaryLinks.Shared

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString manualImpls externalSummaryLinksDoc
    pure (
      hasSubstr out "class=\"bp_summary_decl_list\"" &&
      hasSubstr out "class=\"bp_inline_preview_ref\" data-bp-preview-id=\"bp-lean-code-Informal-002ELeanCodePreview-002ENat-002Eadd\"" &&
      hasSubstr out "data-bp-preview-key=\"Informal.LeanCodePreview.Nat.add\"" &&
      hasSubstr out "href=\"#--informal-external-decl-" &&
      hasSubstr out "class=\"bp_external_decl_item bp_external_decl_item_rendered\" id=\"--informal-external-decl-" &&
      !hasSubstr out "Lean code:"
    )

end Verso.VersoBlueprintTests.BlueprintSummaryLinks.External
