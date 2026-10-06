import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import OperatorRidgeletBlueprint.Chapters.Introduction
import OperatorRidgeletBlueprint.Chapters.Networks
import OperatorRidgeletBlueprint.Chapters.Transform
import OperatorRidgeletBlueprint.Chapters.Reconstruction
import OperatorRidgeletBlueprint.Chapters.Tempered
import OperatorRidgeletBlueprint.Chapters.Sampling
import OperatorRidgeletBlueprint.Chapters.Examples
import OperatorRidgeletBlueprint.Chapters.NumericalExperiments
import OperatorRidgeletBlueprint.Chapters.Discussion
import OperatorRidgeletBlueprint.Chapters.AppendixA
import OperatorRidgeletBlueprint.Chapters.AppendixB
import OperatorRidgeletBlueprint.Chapters.AppendixC
import OperatorRidgeletBlueprint.Chapters.AppendixD
import OperatorRidgeletBlueprint.Chapters.AppendixE
import OperatorRidgeletBlueprint.Chapters.Infrastructure

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Infinite-dimensional operator ridgelet transform" =>

This Blueprint follows the manuscript in reading order, from the motivation and the
Gaussian-weighted construction to reconstruction, finite-width approximation and examples.
Sections 1–9 contain the main exposition, numerical experiments and discussion.
Prerequisites and detailed proofs appear in the main exposition before their use.
Appendices A–E give optional kernel and projection formulas, additional approximation
bounds, finite-dimensional comparison and the dilation obstruction, and numerical methods.

Numbered mathematical statements have the manuscript's identifiers and numbers. Their Lean
panels show the precise formal statements and proof status. Descriptive auxiliary nodes
provide definitions and formalization infrastructure without changing manuscript numbering.
The dependency graph links these mathematical ingredients; prose, remarks and numerical
experiments are not marked as machine-checked theorems.

{include 0 OperatorRidgeletBlueprint.Chapters.Introduction}
{include 0 OperatorRidgeletBlueprint.Chapters.Networks}
{include 0 OperatorRidgeletBlueprint.Chapters.Transform}
{include 0 OperatorRidgeletBlueprint.Chapters.Reconstruction}
{include 0 OperatorRidgeletBlueprint.Chapters.Tempered}
{include 0 OperatorRidgeletBlueprint.Chapters.Sampling}
{include 0 OperatorRidgeletBlueprint.Chapters.Examples}
{include 0 OperatorRidgeletBlueprint.Chapters.NumericalExperiments}
{include 0 OperatorRidgeletBlueprint.Chapters.Discussion}
{include 0 OperatorRidgeletBlueprint.Chapters.AppendixA}
{include 0 OperatorRidgeletBlueprint.Chapters.AppendixB}
{include 0 OperatorRidgeletBlueprint.Chapters.AppendixC}
{include 0 OperatorRidgeletBlueprint.Chapters.AppendixD}
{include 0 OperatorRidgeletBlueprint.Chapters.AppendixE}

{include 0 OperatorRidgeletBlueprint.Chapters.Infrastructure}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
