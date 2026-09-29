import Architect
import OperatorRidgelet.Paper.Networks

/-!
# LeanArchitect metadata for Section 2

`attribute [blueprint ...]` commands for the declarations of `OperatorRidgelet.Paper.Networks`
and the
definitions it uses.  Statements whose proof is still `sorry` carry `(notReady := true)`.
-/

/-! ## Section 2: definitions -/

attribute [blueprint "def:2.1"
  (statement := /-- The width-$N$ network on $H$ with values in $Y$ is
    $f_N(x)=\sum_{j=1}^N v_j\,\beta(\langle a_j,x\rangle+c_j)$ with $v_j\in Y$ and
    $(a_j,c_j)\in H\times\mathbb R$; the scalar case is $Y=\mathbb C$. -/)
  (hasProof := false)] OperatorRidgelet.finiteNetwork

attribute [blueprint "def:2.2"
  (statement := /-- For a $Y$-valued Borel measure $\Gamma$ of bounded variation on
    $\Theta=H\times\mathbb R$, the integral network is
    $S_\beta[\Gamma](x)=\int\beta(\langle a,x\rangle+c)\,\Gamma(\mathrm da,\mathrm dc)$ whenever the
    Bochner integral exists. -/)
  (hasProof := false)] OperatorRidgelet.integralNetwork

attribute [blueprint "def:2.2-total-variation"
  (statement := /-- The total variation $\|\Gamma\|_{\mathrm{TV}}=|\Gamma|(\Theta)$. -/)
  (hasProof := false)] OperatorRidgelet.totalVariation

attribute [blueprint "def:2.2-density"
  (statement := /-- For $\Gamma=\gamma\lambda$ with a density $\gamma$ against a reference
    measure $\lambda$, $S_\beta[\gamma](x)=\int\beta(\langle a,x\rangle+c)\gamma(a,c)\,
    \lambda(\mathrm da,\mathrm dc)$. -/)
  (hasProof := false)] OperatorRidgelet.integralNetworkDensity

attribute [blueprint "def:2.2-i"
  (statement := /-- If $\beta$ is globally Lipschitz and
    $\int(1+\|a\|+|c|)\,\mathrm d|\Gamma|<\infty$, then the Bochner integral defining
    $S_\beta[\Gamma](x)$ exists for every $x$. -/)]
  OperatorRidgelet.Paper.def_2_2_i

attribute [blueprint "def:2.2-ii"
  (statement := /-- For $\Gamma=\gamma\lambda$ with $\lambda$ $\sigma$-finite,
    $S_\beta[\gamma\lambda]=S_\beta[\gamma]$ whenever the Bochner integral exists. -/)]
  OperatorRidgelet.Paper.def_2_2_ii

attribute [blueprint "operator-ridgelet:is-polynomial-fun"
  (statement := /-- $\beta:\mathbb R\to\mathbb R$ is a polynomial. -/)
  (hasProof := false)] OperatorRidgelet.IsPolynomialFun

attribute [blueprint "operator-ridgelet:has-polynomial-growth"
  (statement := /-- $\beta$ has polynomial growth: $|\beta(t)|\le C(1+|t|)^p$. -/)
  (hasProof := false)] OperatorRidgelet.HasPolynomialGrowth
