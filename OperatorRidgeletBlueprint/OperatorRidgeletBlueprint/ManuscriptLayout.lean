import VersoManual
import VersoBlueprint.Informal.Block
import VersoBlueprint.Commands.Graph

/-!
Apply manuscript numbering before Verso's traversal. The index is shared with the
formalization, while prose and proof placement remain authored in the chapters.
-/

namespace OperatorRidgeletBlueprint.ManuscriptLayout

open Lean Verso Doc
open Verso.Genre Manual

/-- A manuscript number independent of the document's local counters. -/
structure Item where
  label : Name
  kind : Informal.Data.NodeKind
  sectionPrefix : String
  count : Nat

/-- The manuscript title for a statement or graph node. -/
def Item.title (item : Item) : String :=
  s!"{item.kind} {item.sectionPrefix}.{item.count}"

/-- Parse the numbered index supplied at rendering time, independently of cached modules. -/
def items (source : String) : Except String (Array Item) := do
  let index ← Json.parse source
  let rows ← (← index.getObjVal? "items").getArr?
  rows.mapM fun row => do
    let label ← row.getObjValAs? String "blueprint_label"
    let number ← row.getObjValAs? String "number"
    let [sectionPrefix, countText] := number.splitOn "."
      | throw s!"Invalid manuscript number: {number}"
    let some count := countText.toNat?
      | throw s!"Invalid manuscript counter: {number}"
    let kind ← row.getObjValAs? String "kind"
    let kind : Informal.Data.NodeKind ← match kind with
      | "definition" => pure .definition
      | "theorem" => pure .«theorem»
      | "lemma" => pure .lemma
      | "proposition" => pure .proposition
      | "corollary" => pure .corollary
      | "example" => pure .example_
      | other => throw s!"Unknown manuscript kind: {other}"
    pure { label := Name.mkSimple label, kind, sectionPrefix, count }

/-- Preserve statements, proofs, and Lean associations while assigning their numbers. -/
def numberBlock (index : Array Item) (data : Informal.BlockData) : Informal.BlockData :=
  match index.find? (·.label == data.label) with
  | some item =>
    { data with
      kind := match data.kind with
        | .statement _ => .statement item.kind
        | .proof => .proof
      count := item.count
      partPrefix := some item.sectionPrefix
      foldCodeBlock := true
      numberingMode := .sub
      subNumberingCounter := .document }
  | none =>
    { data with
      partPrefix := some "Aux"
      foldCodeBlock := true
      numberingMode := .sub
      subNumberingCounter := .prefix }

/-- Group manuscript graph nodes by their actual section or appendix. -/
def numberGraph (index : Array Item) (data : Informal.Commands.GraphBlockData) :
    Informal.Commands.GraphBlockData := Id.run do
  let mut groups := data.graphModel.groupMetadata
  let nodes := data.graphModel.nodes.map fun node =>
    match index.find? (·.label == node.label) with
    | some item =>
      { node with
        displayLabel := item.title
        title := item.title
        kind := some item.kind
        parent := some (Name.mkSimple s!"paper-{item.sectionPrefix}") }
    | none => node
  for item in index do
    let label := Name.mkSimple s!"paper-{item.sectionPrefix}"
    if !(groups.any (·.label == label)) then
      let title := if item.sectionPrefix.toNat?.isSome then
        s!"Section {item.sectionPrefix}" else s!"Appendix {item.sectionPrefix}"
      groups := groups.push { label, title, declared := true }
  return { data with graphModel := { nodes, groupMetadata := groups } }

/-- Adjust informal and graph payloads, leaving other blocks unchanged. -/
partial def rewriteBlock (index : Array Item) (block : Doc.Block Manual) :
    Except String (Doc.Block Manual) := do
  match block with
  | .para _ | .code _ => pure block
  | .ul entries =>
    return .ul (← entries.mapM fun e => do
      return { e with contents := ← e.contents.mapM (rewriteBlock index) })
  | .ol start entries =>
    return .ol start (← entries.mapM fun e => do
      return { e with contents := ← e.contents.mapM (rewriteBlock index) })
  | .dl entries =>
    return .dl (← entries.mapM fun e => do
      return { e with desc := ← e.desc.mapM (rewriteBlock index) })
  | .blockquote children => return .blockquote (← children.mapM (rewriteBlock index))
  | .concat children => return .concat (← children.mapM (rewriteBlock index))
  | .other container children =>
    let children ← children.mapM (rewriteBlock index)
    if container.name.toString == "Informal.Block.informal" then
      let data ← fromJson? (α := Informal.BlockData) container.data
      return .other { container with data := toJson (numberBlock index data) } children
    else if container.name.toString == "Informal.Commands.Block.graph" then
      let data ← fromJson? (α := Informal.Commands.GraphBlockData) container.data
      return .other { container with data := toJson (numberGraph index data) } children
    else
      return .other container children

/-- Apply the manuscript index throughout all chapters and appendices. -/
partial def rewritePart (index : Array Item) (part : Part Manual) :
    Except String (Part Manual) := do
  return { part with
    content := ← part.content.mapM (rewriteBlock index)
    subParts := ← part.subParts.mapM (rewritePart index) }

/-- Prepare an authored Blueprint independently of chapter-local counters. -/
def apply (source : String) (part : Part Manual) : Except String (Part Manual) := do
  rewritePart (← items source) part

end OperatorRidgeletBlueprint.ManuscriptLayout
