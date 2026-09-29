/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint.Git
import VersoBlueprint.RuntimeCache

namespace Verso.VersoBlueprintTests.RuntimeCache

open Lean

private def pathText? (path? : Option System.FilePath) : Option String :=
  path?.map (·.toString)

/-- info: true -/
#guard_msgs in
#eval
  show CoreM Bool from do
    liftM (m := CoreM) Informal.RuntimeCache.clear
    let calls ← liftM (m := CoreM) (IO.mkRef (0 : Nat))
    let root := System.FilePath.mk "/tmp/verso-blueprint-runtime-cache-test"
    let firstPath := root / "First.lean"
    let secondPath := root / "Second.lean"
    let first ←
      Informal.RuntimeCache.cachedModuleSourcePath? root `VersoRuntimeCacheTest.Module do
        liftM (m := CoreM) <| (calls.modify (· + 1) : IO Unit)
        pure (some firstPath)
    let second ←
      Informal.RuntimeCache.cachedModuleSourcePath? root `VersoRuntimeCacheTest.Module do
        liftM (m := CoreM) <| (calls.modify (· + 10) : IO Unit)
        pure (some secondPath)
    let callCount ← liftM (m := CoreM) (calls.get : IO Nat)
    pure <|
      callCount == 1 &&
        pathText? first == some firstPath.toString &&
        pathText? second == some firstPath.toString

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    Informal.RuntimeCache.clear
    let calls ← IO.mkRef 0
    let sourceDir := System.FilePath.mk "/tmp/verso-blueprint-runtime-cache-test/git"
    let first ←
      Informal.RuntimeCache.cachedGitRoot? sourceDir do
        calls.modify (· + 1)
        pure none
    let second ←
      Informal.RuntimeCache.cachedGitRoot? sourceDir do
        calls.modify (· + 10)
        pure (some sourceDir)
    let callCount ← calls.get
    pure <| callCount == 1 && first.isNone && second.isNone

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    Informal.RuntimeCache.clear
    let calls ← IO.mkRef 0
    let gitRoot := System.FilePath.mk "/tmp/verso-blueprint-runtime-cache-test/repo"
    let firstInfo : Informal.Git.RepositoryInfo := {
      root := gitRoot
      githubUrl := "https://github.com/example/first"
      commit := "111"
    }
    let secondInfo : Informal.Git.RepositoryInfo := {
      root := gitRoot
      githubUrl := "https://github.com/example/second"
      commit := "222"
    }
    let first ←
      Informal.RuntimeCache.cachedGitRepoInfo? gitRoot do
        calls.modify (· + 1)
        pure (some firstInfo)
    let second ←
      Informal.RuntimeCache.cachedGitRepoInfo? gitRoot do
        calls.modify (· + 10)
        pure (some secondInfo)
    let callCount ← calls.get
    pure <|
      callCount == 1 &&
        first.map (·.githubUrl) == some firstInfo.githubUrl &&
        second.map (·.githubUrl) == some firstInfo.githubUrl

/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    Informal.Git.githubRepositoryUrl? "git@github.com:leanprover/verso-blueprint.git" ==
      some "https://github.com/leanprover/verso-blueprint" &&
    Informal.Git.githubRepositoryUrl? "ssh://git@github.com/leanprover/verso-blueprint.git" ==
      some "https://github.com/leanprover/verso-blueprint" &&
    Informal.Git.commitUrl? (some "https://github.com/leanprover/verso-blueprint") (some "abc123") ==
      some "https://github.com/leanprover/verso-blueprint/commit/abc123"

end Verso.VersoBlueprintTests.RuntimeCache
