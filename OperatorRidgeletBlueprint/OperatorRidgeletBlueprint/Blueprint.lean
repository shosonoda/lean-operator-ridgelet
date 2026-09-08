import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import OperatorRidgeletBlueprint.Chapters.Networks
import OperatorRidgeletBlueprint.Chapters.Transform
import OperatorRidgeletBlueprint.Chapters.Reconstruction
import OperatorRidgeletBlueprint.Chapters.Tempered
import OperatorRidgeletBlueprint.Chapters.Sampling
import OperatorRidgeletBlueprint.Chapters.Examples
import OperatorRidgeletBlueprint.Chapters.Roadmap
import OperatorRidgeletBlueprint.Chapters.Comparator

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Infinite-dimensional operator ridgelet transform" =>

This Blueprint follows the manuscript on the Gaussian-weighted ridgelet transform on an
infinite-dimensional Hilbert space section by section: networks with Hilbert-space inputs,
the transform and its Plancherel theory, representation and reconstruction, tempered synthesis
activations, finite-width approximation, and the examples with genuinely infinite-dimensional
inputs, each chapter folding in the appendix that carries its proofs. Every theorem,
proposition, lemma, corollary, example, and definition of the manuscript is one node, labeled
by its manuscript label (`thm:B`, `lem:fourier-slice`, `def:ridgelet-analysis`, ...) and linked
to all of its Lean declarations; the manuscript's examples appear as propositions, since the
Blueprint has no example kind. Objects that the manuscript introduces inside prose have
auxiliary definition nodes (`aux:...`), and the infrastructure chapter records the tools that
Mathlib lacks. A node has one of three states: a node with a Lean association and a complete
proof is done; a node with a Lean association whose proof is still `sorry` is stated but not
proved; a node without a Lean association is a roadmap item. None of the three is an
assumption in the formal development, and the status is read from the Lean code, never
written by hand.

The record of what is verified is the comparator scheme of the `OperatorRidgelet` project.
Each manuscript item is a theorem `OperatorRidgelet.Paper.<kind>_<label>[_<part>]`, stated
twice with identical text, once with proof `sorry` in the `Challenge` library and once with
the real proof in `OperatorRidgelet.Paper`; the definitions it uses live in `sorry`-free
definition modules. A statement is verified once it is listed in `comparator/config.json` and
comparator confirms that the proof matches the challenge statement and uses only the axioms
`propext`, `Quot.sound`, and `Classical.choice`. The Blueprint reads the same declarations, so
a node whose parts are all verified shows as complete, and a multi-part node shows as
incomplete while any part is still `sorry`. Dependencies follow the manuscript's proofs; the
graph and the summary below are computed from them. The last chapter is the comparator review,
generated from the same data: for every manuscript item it shows the `Challenge` statement
verbatim next to a link to its node and the comparator status of each declaration, so that the
formal statement can be checked against the informal one without leaving the site.

{include 0 OperatorRidgeletBlueprint.Chapters.Networks}
{include 0 OperatorRidgeletBlueprint.Chapters.Transform}
{include 0 OperatorRidgeletBlueprint.Chapters.Reconstruction}
{include 0 OperatorRidgeletBlueprint.Chapters.Tempered}
{include 0 OperatorRidgeletBlueprint.Chapters.Sampling}
{include 0 OperatorRidgeletBlueprint.Chapters.Examples}
{include 0 OperatorRidgeletBlueprint.Chapters.Roadmap}
{include 0 OperatorRidgeletBlueprint.Chapters.Comparator}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
