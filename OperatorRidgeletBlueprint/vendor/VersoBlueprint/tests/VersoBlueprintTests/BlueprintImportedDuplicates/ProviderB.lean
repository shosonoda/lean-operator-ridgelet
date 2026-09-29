/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint
import VersoManual

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

namespace Verso.VersoBlueprintTests.BlueprintImportedDuplicates.ProviderB

@[blueprint "dup.imported.node"]
def importedNodeB : Nat := 2

#docs (Manual) importedDuplicatesProviderB "Imported Duplicates Provider B" :=
:::::::
:::group "dup.imported.group"
Imported group from provider B.
:::

:::author "dup.imported.author" (name := "Imported Author B")
:::
:::::::

end Verso.VersoBlueprintTests.BlueprintImportedDuplicates.ProviderB
