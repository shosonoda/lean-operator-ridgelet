/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Commands.Summary.Collect

open Lean
open Verso Genre Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintExamples

private def manualImpls : ExtensionImpls := extension_impls%

#docs (Manual) exampleDoc "Example kind" :=
:::::::
:::example_ "example.kind.test"
A separately classified example.
:::
:::::::

/-- info: true -/
#guard_msgs in
#eval
  let proofGap := Data.ProvedStatus.ofRefCounts 0 1
  let statementGap := Data.ProvedStatus.ofRefCounts 1 0
  toString Data.NodeKind.example_ == "Example" &&
    Data.NodeKind.example_.isTheoremLike &&
    !(proofGap.blocksStatementCompletion .example_) &&
    statementGap.blocksStatementCompletion .example_ &&
    Graph.kindShape .example_ == "ellipse" &&
    Graph.actionableStageForStatuses? .example_ .formalized .ready == some "proof"

/-- info: true -/
#guard_msgs in
#eval! do
  let out ← renderManualDocHtmlString manualImpls exampleDoc
  pure <| hasSubstr out "Example" && hasSubstr out "bp_kind_example"

/-- info: true -/
#guard_msgs in
#eval
  show CoreM Bool from do
    let summary ← Commands.buildSummary
    pure <| summary.examples == 1 && summary.theorems == 0 && summary.propositions == 0

end Verso.VersoBlueprintTests.BlueprintExamples
