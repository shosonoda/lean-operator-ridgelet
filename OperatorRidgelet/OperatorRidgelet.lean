import OperatorRidgelet.Activation
import OperatorRidgelet.Cylindrical
import OperatorRidgelet.RankOneLift
import OperatorRidgelet.OperatorValuedRidgelet
import OperatorRidgelet.ToFoML.ActivationContraction
import OperatorRidgelet.ToFoML.ProbabilisticMethod
import OperatorRidgelet.ToFoML.RidgeFeature
import OperatorRidgelet.Network.Defs
import OperatorRidgelet.Architecture.Defs
import OperatorRidgelet.Architecture.Basic
import OperatorRidgelet.Transform.Defs
import OperatorRidgelet.Transform.Infra
import OperatorRidgelet.FiniteDim.Defs
import OperatorRidgelet.Filters.Defs
import OperatorRidgelet.Reconstruction.Defs
import OperatorRidgelet.Tempered.Const
import OperatorRidgelet.Tempered.Defs
import OperatorRidgelet.Sampling.Defs
import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Paper
import OperatorRidgelet.ArchitectBridge

/-!
# Operator ridgelet transform on infinite-dimensional Hilbert spaces

Lean formalization of the manuscript on the Gaussian-weighted ridgelet transform with
Hilbert-space inputs.  The statements of the manuscript are collected in `OperatorRidgelet.Paper`
and mirrored, with `sorry`, in the comparator challenge library `Challenge`.
-/
