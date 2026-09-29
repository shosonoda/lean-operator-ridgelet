/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintAutoDeps.Provider

namespace Verso.VersoBlueprintTests.BlueprintAutoDeps.Reexport

def importedValue : Nat :=
  Verso.VersoBlueprintTests.BlueprintAutoDeps.Provider.defSource

end Verso.VersoBlueprintTests.BlueprintAutoDeps.Reexport
