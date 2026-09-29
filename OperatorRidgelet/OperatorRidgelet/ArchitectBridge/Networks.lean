import Architect
import OperatorRidgelet.Paper.Networks

/-!
# LeanArchitect metadata for Section 2 and Appendix F

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

/-! ## Appendix F: definitions -/

attribute [blueprint "operator-ridgelet:hs-norm-sq"
  (statement := /-- The squared Hilbert--Schmidt norm
    $\|A\|_{\mathcal L_2}^2=\sup\{\sum_{e\in s}\|Ae\|^2 : s\ \text{finite orthonormal}\}$. -/)
  (hasProof := false)] OperatorRidgelet.hsNormSq

attribute [blueprint "operator-ridgelet:is-hilbert-schmidt"
  (statement := /-- $A\in\mathcal L_2(H)$: the operator $A$ is Hilbert--Schmidt. -/)
  (hasProof := false)] OperatorRidgelet.IsHilbertSchmidt

attribute [blueprint "operator-ridgelet:hs-norm"
  (statement := /-- The Hilbert--Schmidt norm $\|A\|_{\mathcal L_2}$. -/)
  (hasProof := false)] OperatorRidgelet.hsNorm

attribute [blueprint "operator-ridgelet:operator-neuron"
  (statement := /-- The operator neuron
    $\mathrm n_{\ell,A,b}(x)=\langle\ell,\sigma(Ax+b)\rangle$. -/)
  (hasProof := false)] OperatorRidgelet.operatorNeuron

attribute [blueprint "operator-ridgelet:operator-neuron-set"
  (statement := /-- The continuous operator neurons with operator parameter in a given set,
    as a subset of $C(H;\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorNeuronSet

attribute [blueprint "operator-ridgelet:ridge-set"
  (statement := /-- The scalar ridges $x\mapsto\beta(\langle a,x\rangle+c)$ as a subset of
    $C(H;\mathbb R)$. -/)
  (hasProof := false)] OperatorRidgelet.ridgeSet

attribute [blueprint "operator-ridgelet:rank-one-activation"
  (statement := /-- The rank-one activation $\sigma_\beta(y)=\beta(\langle\psi,y\rangle)z$. -/)
  (hasProof := false)] OperatorRidgelet.rankOneActivation

attribute [blueprint "operator-ridgelet:operator-finite-network"
  (statement := /-- The finite-width operator network
    $x\mapsto\sum_j v_j\,\mathrm n_{\ell,A_j,b_j}(x)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorFiniteNetwork

attribute [blueprint "operator-ridgelet:operator-synthesis"
  (statement := /-- The operator synthesis
    $S_{\rm op}\Gamma_{\rm op}(x)
    =\int\mathrm n_{\ell,A,b}(x)\,\Gamma_{\rm op}(\mathrm dA,\mathrm db)$. -/)
  (hasProof := false)] OperatorRidgelet.operatorSynthesis

/-! ## Appendix F: statements -/

attribute [blueprint "lem:F.1"
  (statement := /-- For globally Lipschitz $\sigma:H\to H$, the finite linear spans of the
    neurons $\mathrm n_{\ell,A,b}$ with $A\in\mathcal L(H)$ and with $A\in\mathcal L_2(H)$ have
    the same compact-open closure in $C(H;\mathbb R)$. -/)]
  OperatorRidgelet.Paper.lem_F_1

attribute [blueprint "lem:F.2-i"
  (statement := /-- $A_a=\|\psi\|^{-2}\psi\otimes a$ is Hilbert--Schmidt. -/)]
  OperatorRidgelet.Paper.lem_F_2_i

attribute [blueprint "lem:F.2-ii"
  (statement := /-- $\|A_a\|_{\mathcal L_2}=\|a\|/\|\psi\|$. -/)]
  OperatorRidgelet.Paper.lem_F_2_ii

attribute [blueprint "lem:F.2-iii"
  (statement := /-- $\|b_c\|=|c|/\|\psi\|$. -/)]
  OperatorRidgelet.Paper.lem_F_2_iii

attribute [blueprint "lem:F.2-iv"
  (statement := /-- $\pi_\psi(A_a,b_c)=(a,c)$. -/)]
  OperatorRidgelet.Paper.lem_F_2_iv

attribute [blueprint "lem:F.2-v"
  (statement := /-- The section $J_\psi(a,c)=(A_a,b_c)$ is continuous into
    $\mathcal L_2(H)\times H$. -/)]
  OperatorRidgelet.Paper.lem_F_2_v

attribute [blueprint "lem:F.2-vi"
  (statement := /-- Every scalar integral network with activation $\beta$ lifts exactly to the
    operator architecture with activation $\sigma_\beta$ and readout normalized by
    $\langle\ell,z\rangle=1$: $S_{\rm op}(J_\psi)_\#\Gamma=S_\beta[\Gamma]$. -/)]
  OperatorRidgelet.Paper.lem_F_2_vi

attribute [blueprint "lem:F.2-vii"
  (statement := /-- Every scalar finite-width network with activation $\beta$ lifts exactly to
    the operator architecture with activation $\sigma_\beta$, parameters $(A_{a_j},b_{c_j})$, and
    readout normalized by $\langle\ell,z\rangle=1$. -/)]
  OperatorRidgelet.Paper.lem_F_2_vii

attribute [blueprint "prop:F.3-i"
  (statement := /-- For continuous non-polynomial $\beta:\mathbb R\to\mathbb R$, finite linear
    combinations of $\beta(\langle a,x\rangle+c)$ are dense in $C(H;\mathbb R)$ for uniform
    convergence on compact sets. -/)] OperatorRidgelet.Paper.prop_F_3_i

attribute [blueprint "prop:F.3-ii"
  (statement := /-- The same holds for the rank-one operator activation $\sigma_\beta$ with
    Hilbert--Schmidt parameters. -/)] OperatorRidgelet.Paper.prop_F_3_ii

attribute [blueprint "lem:F.4-i"
  (statement := /-- For real globally Lipschitz $\beta$, $\psi\ne0$, and a finite complex Borel
    measure $\Gamma_{\rm op}$ on $\mathcal L_2(H)\times H$ with
    $\int(1+\|A\|_{\mathcal L_2}+\|b\|)\,\mathrm d|\Gamma_{\rm op}|<\infty$,
    $S_{\rm op}\Gamma_{\rm op}=S_\beta[(\pi_\psi)_\#\Gamma_{\rm op}]$. -/)]
  OperatorRidgelet.Paper.lem_F_4_i

attribute [blueprint "lem:F.4-ii"
  (statement := /-- $|(\pi_\psi)_\#\Gamma_{\rm op}|\le(\pi_\psi)_\#|\Gamma_{\rm op}|$. -/)]
  OperatorRidgelet.Paper.lem_F_4_ii

attribute [blueprint "lem:F.4-iii"
  (statement := /-- For compact $K$ with $r_K=\sup_K\|x\|$,
    $\|S_{\rm op}\Gamma_{\rm op}\|_{C(K)}\le\int[|\beta(0)|+\operatorname{Lip}(\beta)\|\psi\|
    (r_K\|A\|_{\mathcal L_2}+\|b\|)]\,\mathrm d|\Gamma_{\rm op}|$. -/)]
  OperatorRidgelet.Paper.lem_F_4_iii

attribute [blueprint "lem:F.4-iv"
  (statement := /-- Conversely, $(\pi_\psi)_\#(J_\psi)_\#\Gamma=\Gamma$. -/)]
  OperatorRidgelet.Paper.lem_F_4_iv

attribute [blueprint "lem:F.4-v"
  (statement := /-- Conversely, $S_{\rm op}(J_\psi)_\#\Gamma=S_\beta\Gamma$. -/)]
  OperatorRidgelet.Paper.lem_F_4_v
