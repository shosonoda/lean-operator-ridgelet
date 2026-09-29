import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

open Verso
open Verso.Genre
open Verso.Genre.Manual
open Informal

@[bib "preview.showcase.cite"]
def preview.showcase.cite : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := inlines!"Preview showcase citation"
  , authors := #[inlines!"A. Author", inlines!"B. Author"]
  , year := 2026
  , id := "preview.showcase.cite"
  }

#doc (Manual) "Inline Hover Previews" =>

:::definition "nested_inner"
Nested inner preview definition.
:::

:::theorem "nested_outer"
Outer theorem refers to {uses "nested_inner"}[].
:::

:::lemma_ "nested_user"
This page references {uses "nested_outer"}[] so the inline preview contains a
second hover target.
:::

:::lemma_ "bibliography_hover"
See {Informal.citet preview.showcase.cite (kind := lemma) (index := 1)}[] for a
bibliography-backed inline preview.
:::

{blueprint_bibliography}
