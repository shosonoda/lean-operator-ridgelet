/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias, David Thrane Christiansen
-/

module

import Lean.Data.Options
public import Verso.Doc.DocName
public import Verso.Doc.Elab.Monad

open Verso.Doc.Elab

namespace Informal.Profile

register_option verso.blueprint.profile : Bool := {
  defValue := false
  descr := "Enable timing logs for VersoBlueprint directive/code-block elaboration"
}

private def profileEnabled : DocElabM Bool := do
  pure <| verso.blueprint.profile.get (← Lean.getOptions)

private def leftPad (s : String) (width : Nat) : String :=
  if s.length >= width then
    s
  else
    String.ofList (List.replicate (width - s.length) ' ') ++ s

private def fileBasename (path : String) : String :=
  match (System.FilePath.mk path).fileName with
  | some base =>
    if base.isEmpty then path else base
  | none => path

open Lean Elab

private def sourcePosString (stx : Syntax) : DocElabM String := do
  let fileName := fileBasename (← getFileName)
  match stx.getPos? with
  | some pos =>
    let lspPos := (← getFileMap).utf8PosToLspPos pos
    pure s!"{fileName}:{lspPos.line + 1}:{lspPos.character + 1}"
  | none =>
    pure s!"{fileName}:?:?"

public def withDocElab {α}
    (category : String) (name : String) (k : DocElabM α) : DocElabM α := do
  if !(← profileEnabled) then
    return (← k)
  let stx ← getRef
  let startTime ← IO.monoMsNow
  try
    let result ← k
    let endTime ← IO.monoMsNow
    let pos ← sourcePosString stx
    let ms := leftPad (toString (endTime - startTime)) 5
    logInfo s!"[bp_profile] {ms} ms | {category} {name} | {pos}"
    pure result
  catch ex =>
    let endTime ← IO.monoMsNow
    let pos ← sourcePosString stx
    let ms := leftPad (toString (endTime - startTime)) 5
    logInfo s!"[bp_profile] {ms} ms | {category} {name} | {pos} | failed"
    throw ex
