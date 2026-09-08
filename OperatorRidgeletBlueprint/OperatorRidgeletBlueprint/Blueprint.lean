import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import OperatorRidgeletBlueprint.Chapters.Foundations
import OperatorRidgeletBlueprint.Chapters.OperatorValued
import OperatorRidgeletBlueprint.Chapters.GaussianWeighted
import OperatorRidgeletBlueprint.Chapters.Roadmap

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Infinite-dimensional operator ridgelet transform" =>

This Blueprint connects the manuscript's operator-valued ridgelet transform and Gaussian-weighted
ridgelet transform to the declarations in the `OperatorRidgelet` Lake project. The final chapter
records the remaining formalization work.

There are three kinds of node. A node with a Lean association and a complete proof is done. A node
with a Lean association whose proof is still `sorry` is stated but not proved; the Gaussian-weighted
chapter consists mostly of these, so that the status of the manuscript's newest section is visible
in the graph and the summary. A node without a Lean association is a roadmap item. None of the
three is an assumption in the formal development.

{include 0 OperatorRidgeletBlueprint.Chapters.Foundations}
{include 0 OperatorRidgeletBlueprint.Chapters.OperatorValued}
{include 0 OperatorRidgeletBlueprint.Chapters.GaussianWeighted}
{include 0 OperatorRidgeletBlueprint.Chapters.Roadmap}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
