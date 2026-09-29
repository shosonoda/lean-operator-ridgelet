/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoSlides
import Verso.Doc.Elab
import VersoBlueprint.Graft.Node

namespace Informal.Slides

open Lean
open Verso Doc Elab

private def blueprintNodeClassName (node : Informal.Graft.BlueprintNode) : String :=
  if node.compact then
    "bp_slide_node bp_slide_node_compact"
  else
    "bp_slide_node"

public def blueprintNodeAttrs (node : Informal.Graft.BlueprintNode) :
    Array (String × String) :=
  Informal.Graft.appendClassAttr node.toAttrs (blueprintNodeClassName node)

public def renderedBlueprintNodeAttrs (node : Informal.Graft.BlueprintNode) :
    Array (String × String) :=
  node.renderedAttrsWithClass (blueprintNodeClassName node)

public def sideBySideAttrs (cfg : Informal.Graft.SideBySideConfig) :
    Array (String × String) :=
  #[("class", cfg.className ++ " bp_slide_graft_side_by_side")]

public meta def blueprintNodeBlock (cfg : Informal.Graft.BlueprintNodeConfig) : DocElabM Term := do
  let node := cfg.toNode
  let attrs := blueprintNodeAttrs node
  let fallback := node.fallbackText
  ``(Verso.Doc.Block.other (VersoSlides.BlockExt.wrap $(quote attrs))
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote fallback)]])

end Informal.Slides
