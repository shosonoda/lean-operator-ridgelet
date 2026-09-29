/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintImportedDuplicates.ProviderA
import VersoBlueprintTests.BlueprintImportedDuplicates.ProviderB

namespace Verso.VersoBlueprintTests.BlueprintImportedDuplicates.Reexport

def importedValue : Nat :=
  Verso.VersoBlueprintTests.BlueprintImportedDuplicates.ProviderA.importedNodeA +
  Verso.VersoBlueprintTests.BlueprintImportedDuplicates.ProviderB.importedNodeB

end Verso.VersoBlueprintTests.BlueprintImportedDuplicates.Reexport
