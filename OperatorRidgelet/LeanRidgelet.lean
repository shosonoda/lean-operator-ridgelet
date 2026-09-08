import LeanRidgelet.Basic
import LeanRidgelet.Fourier.Convention
import LeanRidgelet.Fourier.AngularDistribution
import LeanRidgelet.Fourier.AngularLp
import LeanRidgelet.Space.Activation
import LeanRidgelet.Activation.ReLU
import LeanRidgelet.Activation.Tanh
import LeanRidgelet.Activation.Gaussian
import LeanRidgelet.ToMathlib.GaussianSchwartz
import LeanRidgelet.ToMathlib.FourierPlancherel
import LeanRidgelet.ToMathlib.L2Duality
import LeanRidgelet.ToMathlib.SchwartzAux
import LeanRidgelet.ToMathlib.Lizorkin

/-!
# Vendored subset of `lean-ridgelet`

These thirteen files are copied verbatim from
<https://github.com/shosonoda/lean-ridgelet> at revision
`e9af79a1042c19891a9991addb92b75947886343` (2026-09-08), paths `LeanRidgelet/...`.
They provide the weighted Sobolev activation space `𝒜_{s,t}` and the tempered-distribution
realizations of ReLU, tanh, and the Gaussian.  Do not edit them here; update by diffing against
upstream.
-/
