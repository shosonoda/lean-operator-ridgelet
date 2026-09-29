/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint
import VersoManual

namespace Verso.VersoBlueprintTests.BlueprintInformal.Shared

open Lean
open Verso Genre Manual
open Informal

def currentState : CoreM Informal.Environment.State := do
  pure <| Informal.Environment.informalExt.getState (← getEnv)

end Verso.VersoBlueprintTests.BlueprintInformal.Shared
