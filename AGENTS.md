# Agent guide for lean-operator-ridgelet

Repository documentation and contributor rules live in the following shared documents.
Read and follow them before making changes:

1. [README.md](README.md): public overview, build, and comparator quick start.
2. [docs/FORMALIZATION.md](docs/FORMALIZATION.md): mathematical source map, statement naming,
   conventions, and verification scope.
3. [CONTRIBUTING.md](CONTRIBUTING.md): dependency and vendoring rules, statement updates,
   validation, Blueprint, and GitHub Pages operations.
4. [STATUS.md](STATUS.md): generated per-item formalization status; never edit it by hand.
5. [OperatorRidgelet/comparator/paper.json](OperatorRidgelet/comparator/paper.json): manuscript
   labels, numbers, Lean names, and formalization notes.

Run `git status --short` before editing and preserve unrelated changes. Never run two
`lake build` commands in the same project concurrently. Complete the validation workflow in
[CONTRIBUTING.md](CONTRIBUTING.md#validation-and-generated-files) before reporting a change
as fully checked; report any checks that could not be run.
