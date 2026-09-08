import OperatorRidgelet.Examples.Defs
import OperatorRidgelet.Examples.OperatorLayer

/-!
# The periodic convolution layer

Elementary facts about the convolution layer of Example `ex:convolution`: the directions
`a_y = k(y - ·)` and outputs `b_y = ψ(· - y)` are translates, so they all have the norm of `k`
and of `ψ` (`norm_convDirection`, `norm_convOutput`), and the pairing `⟪a_y, x⟫` is the
convolution `(k * x)(y)` (`inner_convDirection`).
-/

noncomputable section

namespace OperatorRidgelet

open MeasureTheory
open scoped RealInnerProductSpace

/-- The norm of `L.compLp f` for the isometric embedding `ℝ → ℂ` is the norm of `f`. -/
theorem norm_ofRealCLM_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal}
    (f : Lp ℝ p μ) : ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' f] with t ht
  rw [ht, Complex.ofRealCLM_apply, Complex.norm_real]

variable {d : ℕ}

/-- `‖a_y‖ = ‖k‖₂` for the direction `a_y = k(y - ·)`. -/
theorem norm_convDirection (k : TorusL2 d) (y : Torus d) : ‖convDirection k y‖ = ‖k‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- `‖b_y‖ = ‖ψ‖₂` for the output `b_y = ψ(· - y)`. -/
theorem norm_convOutput (ψ : TorusL2 d) (y : Torus d) : ‖convOutput ψ y‖ = ‖ψ‖ := by
  unfold convOutput
  rw [norm_ofRealCLM_compLp, LinearIsometry.norm_map]

/-- **Example `ex:convolution`**: `‖A‖_∞ = ‖k‖₂`. -/
theorem layerSupNorm_convDirection (k : TorusL2 d) : layerSupNorm (convDirection k) = ‖k‖ := by
  unfold layerSupNorm
  simp_rw [norm_convDirection]
  exact ciSup_const

/-- **Example `ex:convolution`**: `∫ ‖b_y‖ dy = ‖ψ‖₂`. -/
theorem integral_norm_convOutput (ψ : TorusL2 d) :
    ∫ y, ‖convOutput ψ y‖ ∂torusHaar d = ‖ψ‖ := by
  simp_rw [norm_convOutput]
  simp

/-- **Example `ex:convolution`**: `⟪a_y, x⟫ = (k * x)(y)`. -/
theorem inner_convDirection (k x : TorusL2 d) (y : Torus d) :
    ⟪convDirection k y, x⟫ = ∫ t, k (y - t) * x t ∂torusHaar d := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving k
    (Measure.measurePreserving_sub_left (torusHaar d) y)] with t ht
  change ⟪(Lp.compMeasurePreserving (fun t => y - t)
    (Measure.measurePreserving_sub_left (torusHaar d) y) k) t, x t⟫ = _
  rw [ht, Function.comp_apply]
  simp [RCLike.inner_apply]

end OperatorRidgelet
