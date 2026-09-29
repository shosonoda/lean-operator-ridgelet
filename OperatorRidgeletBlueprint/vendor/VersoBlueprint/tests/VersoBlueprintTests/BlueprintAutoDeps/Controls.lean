/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintAutoDeps.Support

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Verso.VersoBlueprintTests.BlueprintAutoDeps.Support

namespace Verso.VersoBlueprintTests.BlueprintAutoDeps.Controls

set_option doc.verso true

@[blueprint "auto.controls.type_source"]
def controlsTypeSource : Prop := True

@[blueprint "auto.controls.proof_source"]
theorem controlsProofSource : True := by
  trivial

@[blueprint "auto.controls.attr.local_true" (autoDeps := true)]
theorem attrLocalTrue : controlsTypeSource := by
  trivial

set_option verso.blueprint.autoDeps true

@[blueprint "auto.controls.attr.global_default"]
theorem attrGlobalDefault : controlsTypeSource := by
  trivial

@[blueprint "auto.controls.attr.local_false" (autoDeps := false)]
theorem attrLocalFalse : controlsTypeSource := by
  trivial

set_option verso.blueprint.autoDeps false

theorem externalLocalTrueDecl : controlsTypeSource := by
  exact controlsProofSource

theorem externalManualSameAxisDecl : controlsTypeSource := by
  exact controlsProofSource

theorem externalUnionStatementDecl : controlsTypeSource := by
  trivial

theorem externalUnionProofDecl : True := by
  exact controlsProofSource

def externalSourceDecl : Prop := True

#docs (Genre.Manual) autoDepsLocalControlsDoc "Auto Dependency Local Controls" :=
:::::::
:::theorem "auto.controls.external.local_true" (lean := "externalLocalTrueDecl") (autoDeps := true)
External declaration inference can be enabled locally.
:::

:::theorem "auto.controls.external.manual_same_axis" (lean := "externalManualSameAxisDecl") (autoDeps := true) (uses := "auto.controls.type_source")
Block-level manual dependencies take precedence over same-axis automatic edges.
:::

:::theorem "auto.controls.external.union" (lean := "externalUnionStatementDecl, externalUnionProofDecl") (autoDeps := true)
External declaration inference unions multiple compiled Lean references.
:::

:::definition "auto.controls.inline.local_true"
Inline Lean inference can be enabled locally.
:::

```lean "auto.controls.inline.local_true" (autoDeps := true)
theorem inlineLocalTrueDecl : controlsTypeSource := by
  exact controlsProofSource
```

:::definition "auto.controls.inline.manual_same_axis" (uses := "auto.controls.type_source")
Statement-level manual dependencies take precedence over inline-code automatic edges.
:::

```lean "auto.controls.inline.manual_same_axis" (autoDeps := true)
theorem inlineManualSameAxisDecl : controlsTypeSource := by
  exact controlsProofSource
```

:::definition "auto.controls.external.source" (lean := "externalSourceDecl")
An ordinary `(lean := ...)` declaration association seeds the Lean-name lookup.
:::

:::definition "auto.controls.inline.source"
An inline Lean declaration association seeds the Lean-name lookup.
:::

```lean "auto.controls.inline.source"
def inlineSourceDecl : Prop := True
```
:::::::

set_option verso.blueprint.autoDeps true

theorem externalGlobalDefaultDecl : controlsTypeSource := by
  exact controlsProofSource

theorem externalLocalFalseDecl : controlsTypeSource := by
  exact controlsProofSource

#docs (Genre.Manual) autoDepsGlobalControlsDoc "Auto Dependency Global Controls" :=
:::::::
:::theorem "auto.controls.external.global_default" (lean := "externalGlobalDefaultDecl")
External declaration inference follows the file option when the local option is omitted.
:::

:::theorem "auto.controls.external.local_false" (lean := "externalLocalFalseDecl") (autoDeps := false)
External declaration inference can be disabled locally.
:::

:::definition "auto.controls.inline.global_default"
Inline Lean inference follows the file option when the local option is omitted.
:::

```lean "auto.controls.inline.global_default"
theorem inlineGlobalDefaultDecl : controlsTypeSource := by
  exact controlsProofSource
```

:::definition "auto.controls.inline.local_false"
Inline Lean inference can be disabled locally.
:::

```lean "auto.controls.inline.local_false" (autoDeps := false)
theorem inlineLocalFalseDecl : controlsTypeSource := by
  exact controlsProofSource
```
:::::::

set_option verso.blueprint.autoDeps false

@[blueprint "auto.controls.external.source_target" (autoDeps := true)]
theorem externalSourceTarget : externalSourceDecl := by
  trivial

@[blueprint "auto.controls.inline.source_target" (autoDeps := true)]
theorem inlineSourceTarget : inlineSourceDecl := by
  trivial

private def expectedControlUses : Array ExpectedUses :=
  #[
    -- Attribute-level controls.
    {
      labelText := "auto.controls.attr.local_true",
      statement := #[useRef "auto.controls.type_source" .automatic]
    },
    {
      labelText := "auto.controls.attr.global_default",
      statement := #[useRef "auto.controls.type_source" .automatic]
    },
    {
      labelText := "auto.controls.attr.local_false"
    },
    -- `(lean := ...)` controls.
    {
      labelText := "auto.controls.external.local_true",
      statement := #[useRef "auto.controls.type_source" .automatic],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    {
      labelText := "auto.controls.external.global_default",
      statement := #[useRef "auto.controls.type_source" .automatic],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    {
      labelText := "auto.controls.external.local_false"
    },
    {
      labelText := "auto.controls.external.manual_same_axis",
      statement := #[useRef "auto.controls.type_source"],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    {
      labelText := "auto.controls.external.union",
      statement := #[useRef "auto.controls.type_source" .automatic],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    -- Inline Lean controls.
    {
      labelText := "auto.controls.inline.local_true",
      statement := #[useRef "auto.controls.type_source" .automatic],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    {
      labelText := "auto.controls.inline.global_default",
      statement := #[useRef "auto.controls.type_source" .automatic],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    {
      labelText := "auto.controls.inline.local_false"
    },
    {
      labelText := "auto.controls.inline.manual_same_axis",
      statement := #[useRef "auto.controls.type_source"],
      proof := #[useRef "auto.controls.proof_source" .automatic]
    },
    -- Lookup seeding from non-attribute Lean associations.
    {
      labelText := "auto.controls.external.source_target",
      statement := #[useRef "auto.controls.external.source" .automatic]
    },
    {
      labelText := "auto.controls.inline.source_target",
      statement := #[useRef "auto.controls.inline.source" .automatic]
    }
  ]

/-- info: #[] -/
#guard_msgs in
#eval
  show CoreM (Array String) from do
    expectedUsesFailures expectedControlUses

/--
error: Expected 'true' or 'false'
-/
#guard_msgs in
#docs (Genre.Manual) invalidBlockAutoDepsDoc "Invalid Block AutoDeps" :=
:::::::
:::definition "auto.controls.invalid.block" (autoDeps := Nat)
Invalid block autoDeps option.
:::
:::::::

/--
error: Expected 'true' or 'false'
-/
#guard_msgs in
#docs (Genre.Manual) invalidInlineAutoDepsDoc "Invalid Inline AutoDeps" :=
:::::::
```lean "auto.controls.invalid.inline" (autoDeps := Nat)
def invalidInlineAutoDepsDecl : Nat := 0
```
:::::::

/-- info: true -/
#guard_msgs in
#eval
  show CoreM Bool from do
    let externalLabels ←
      Environment.labelsForLeanDecl
        `Verso.VersoBlueprintTests.BlueprintAutoDeps.Controls.externalSourceDecl
    let inlineLabels ←
      Environment.labelsForLeanDecl
        `Verso.VersoBlueprintTests.BlueprintAutoDeps.Controls.inlineSourceDecl
    pure <|
      externalLabels == labels #["auto.controls.external.source"] &&
      inlineLabels == labels #["auto.controls.inline.source"]

end Verso.VersoBlueprintTests.BlueprintAutoDeps.Controls
