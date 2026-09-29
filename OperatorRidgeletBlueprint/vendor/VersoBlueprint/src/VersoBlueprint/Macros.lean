/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean

namespace Informal.Macros

open Lean Elab Command

private def normalizeChunk (chunk : String) : String :=
  chunk.trimAscii.toString

private def joinChunks (chunks : Array String) : String :=
  chunks.foldl (init := "") fun acc chunk =>
    if acc.isEmpty then
      chunk
    else
      acc ++ "\n" ++ chunk

structure State where
  chunks : Array String := #[]
  localChunks : Array String := #[]
deriving Inhabited, Repr

private def State.insert (state : State) (chunk : String) (exportLocal : Bool) : State :=
  if state.chunks.contains chunk then
    state
  else
    {
      chunks := state.chunks.push chunk
      localChunks := if exportLocal then state.localChunks.push chunk else state.localChunks
    }

initialize texPreludeExt : PersistentEnvExtension String String State ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported => do
      pure <| imported.foldl (init := ({} : State)) fun state chunks =>
        chunks.foldl (init := state) fun state chunk =>
          state.insert chunk false
    addEntryFn := fun state chunk =>
      state.insert chunk true
    exportEntriesFn := fun state =>
      state.localChunks
  }

def getTexPreludeChunks [Monad m] [MonadEnv m] : m (Array String) := do
  pure (texPreludeExt.getState (← getEnv)).chunks

def getTexPrelude [Monad m] [MonadEnv m] : m String := do
  pure <| joinChunks (← getTexPreludeChunks)

def texPreludeTableJs (prelude : String) : String :=
  let payload : Json := Json.mkObj [("default", Json.str prelude)]
  "window.bpTexPreludeTable = Object.assign({}, window.bpTexPreludeTable || {}, " ++
    Json.compress payload ++
    ");"

def blueprintMathJs : String := include_str "../../static-web/math.js"

syntax (name := texPreludeTableJsTerm) "tex_prelude_table_js%" : term

@[term_elab texPreludeTableJsTerm]
def elabTexPreludeTableJsTerm : Lean.Elab.Term.TermElab
  | _stx, _expectedType? => do
    let prelude ← getTexPrelude
    return Lean.ToExpr.toExpr (texPreludeTableJs prelude)

syntax (name := texPreludeCmd) "tex_prelude" str : command

@[command_elab texPreludeCmd]
def elabTexPrelude : CommandElab
  | `(tex_prelude $chunk:str) => do
    let chunk := normalizeChunk chunk.getString
    if !chunk.isEmpty then
      modifyEnv fun env =>
        texPreludeExt.addEntry env chunk
  | _ => throwUnsupportedSyntax

end Informal.Macros
