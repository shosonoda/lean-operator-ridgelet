import PreviewRuntimeShowcase.Chapters.CodePanels

open Verso.Genre
open Verso.Genre.Manual
open Informal

namespace PreviewRuntimeShowcase.ExternalDeclHeadingDecls

/-- A base structure used to reproduce inherited-field rendering in external declaration panels. -/
structure HeadingBase where
  /-- A base field that should appear through the extending declaration's parent section. -/
  base : Nat

/-- An extending structure used to exercise the `Extends` subsection label. -/
structure HeadingExtends extends HeadingBase where
  /-- A field owned by the extending structure. -/
  extra : Nat

end PreviewRuntimeShowcase.ExternalDeclHeadingDecls

#doc (Manual) "Nested External Declaration Panels" =>
%%%
tag := "issue-130-external-decl-heading-repro"
%%%

Issue #130 heading-outline reproduction.

These Blueprint nodes live on a nested Manual page so the generated page has
real surrounding headings. The external declaration subsection labels below
should be visible without entering the page heading outline.

:::definition "h1_repro_structure" (lean := "PreviewRuntimeShowcase.CodePanelDecls.PreviewFreyPackage")
Structure panel that renders the `Fields` label inside the declaration body.
:::

:::definition "h1_repro_class" (lean := "PreviewRuntimeShowcase.CodePanelDecls.PreviewFold")
Class panel that renders the `Methods` label inside the declaration body.
:::

:::definition "h1_repro_inductive" (lean := "PreviewRuntimeShowcase.CodePanelDecls.PreviewStage")
Inductive panel that renders the `Constructors` label inside the declaration body.
:::

:::definition "h1_repro_extends" (lean := "PreviewRuntimeShowcase.ExternalDeclHeadingDecls.HeadingExtends")
Extending structure panel that renders the `Extends` label inside the declaration body.
:::
