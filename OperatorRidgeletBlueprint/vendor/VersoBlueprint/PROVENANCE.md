# Vendored Verso Blueprint

Source: <https://github.com/leanprover/verso-blueprint>

Revision: `84fafd488acf60e47d3a7e2b029ee4502e740ba8` (`v4.32.0`).

All upstream tracked files were copied with their copyright notices. The source headers
declare Apache-2.0, but this upstream revision omits the referenced `LICENSE` file; the
standard [license text](LICENSE) is supplied from the pinned Verso dependency at revision
`e09d21a5f7f66c9fc985b73197708298569bf583`. This package is a local path dependency; its build
cache is local to this vendored directory. Other dependency pins remain unchanged.

Local extension: `Informal.Data.NodeKind.example_` and the `:::example_` directive
represent manuscript examples as a distinct kind. Examples have theorem-like proof and
dependency status, their own display label and CSS classes, and separate summary counts.
The extension updates rendering, code summaries, graph descriptions, and proof-status
classification. Tests cover its classification, proof tracking, and display semantics.

Local extension: statement and proof facets may be authored in different modules. An
appendix imports its statement chapter and adds the proof to the existing canonical label.
The environment exports only that new proof facet instead of duplicating the imported
statement snapshot. Imports first validate canonical nodes, then attach proof facets;
independently declared duplicate statements and duplicate proofs remain errors. Regression
tests cover the chapter/appendix combination, conflicting proof modules, and the existing
duplicate-statement diagnostics.
This extension supports proof-only appendix modules: keep Lean code associations and other
node metadata on the canonical statement, rather than changing them in the proof module.

To update, compare against the pinned upstream tree and preserve or upstream these extensions.
