/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintAttribute.Provider

namespace Verso.VersoBlueprintTests.BlueprintAttribute.Reexport

def importedValue : Nat := Verso.VersoBlueprintTests.BlueprintAttribute.Provider.exportedDefinition

end Verso.VersoBlueprintTests.BlueprintAttribute.Reexport
