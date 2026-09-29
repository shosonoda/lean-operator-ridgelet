/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import VersoManual
import VersoBlueprint.Data
import VersoBlueprint.LabelNameParsing

namespace Informal.LabelArg

open Lean

/--
An informal-label argument together with the original syntax location.

Directive and role expanders use the parsed label for environment lookups and
the syntax location for diagnostics that should point back to the user-written
label.
-/
structure Parsed where
  /-- Parsed informal label. -/
  label : Data.Label
  /-- Syntax node of the original label argument. -/
  labelSyntax : Syntax

/-- Parse the common positional informal-label argument used by blocks and roles. -/
def parse (arg : Verso.ArgParse.WithSyntax String) : Parsed := {
  label := LabelNameParsing.parse arg.val
  labelSyntax := arg.syntax
}

end Informal.LabelArg
