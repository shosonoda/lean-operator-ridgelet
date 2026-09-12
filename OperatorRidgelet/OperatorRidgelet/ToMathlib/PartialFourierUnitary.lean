import OperatorRidgelet.ToMathlib.PartialFourierL2

/-! # Unitary partial Fourier transformation on product L² spaces -/

noncomputable section
open MeasureTheory Complex Filter Topology FourierTransform
open scoped FourierTransform ENNReal

namespace MeasureTheory
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Inverse Fourier transformation on `L²` is reflection after Fourier transformation. -/
theorem Lp.fourierInv_eq_reflect_fourier (f : Lp Y 2 (volume : Measure ℝ)) :
    𝓕⁻ f = Lp.compMeasurePreserving (fun x : ℝ => -x)
      (Measure.measurePreserving_neg volume) (𝓕 f) := by
  apply DenseRange.induction_on (p := fun g : Lp Y 2 (volume : Measure ℝ) =>
    𝓕⁻ g = Lp.compMeasurePreserving (fun x : ℝ => -x)
      (Measure.measurePreserving_neg volume) (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ Y).symm.continuous
    · exact (Lp.isometry_compMeasurePreserving
        (Measure.measurePreserving_neg volume)).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ Y).continuous
  intro φ
  change 𝓕⁻ (φ.toLp 2) = Lp.compMeasurePreserving (fun x : ℝ => -x)
    (Measure.measurePreserving_neg volume) (𝓕 (φ.toLp 2))
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕⁻ φ).coeFn_toLp 2,
    Lp.coeFn_compMeasurePreserving ((𝓕 φ).toLp 2) (Measure.measurePreserving_neg volume),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 φ).coeFn_toLp 2)] with x hx hy hz
  rw [hx, hy, hz]
  simpa only [Function.comp_apply, SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
    using Real.fourierInv_eq_fourier_neg φ x

variable {H : Type*} [MeasurableSpace H] [SecondCountableTopology Y]
variable (ν : Measure H) [SFinite ν]

local notation "μprod" => ν.prod (volume : Measure ℝ)

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [SecondCountableTopology Y] in
/-- Almost every section of an `L²` product function belongs to `L²`. -/
theorem ae_memLp_prod_section {γ : H × ℝ → Y} (h : MemLp γ 2 (ν.prod volume)) :
    ∀ᵐ a ∂ν, MemLp (fun c : ℝ => γ (a, c)) 2 volume := by
  filter_upwards [h.integrable_norm_sq.prod_right_ae, h.aestronglyMeasurable.prodMk_left]
    with a ha hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ha

/-- A chosen jointly measurable Fourier representative of a product `L²` function. -/
def partialFourierL2Rep (f : Lp Y 2 μprod) : H × ℝ → Y := by
  borelize Y
  exact (exists_measurable_partialFourierL2 (Lp.stronglyMeasurable f).measurable
    (Lp.memLp f)).choose

/-- The chosen representative is square integrable and has the prescribed Fourier sections. -/
theorem partialFourierL2Rep_spec (f : Lp Y 2 μprod) :
    StronglyMeasurable (partialFourierL2Rep ν f) ∧
      MemLp (partialFourierL2Rep ν f) 2 (ν.prod volume) ∧
      ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => f (a, c)) 2 volume,
        (fun ω => partialFourierL2Rep ν f (a, ω)) =ᵐ[volume]
          ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)) := by
  borelize Y
  have h := (exists_measurable_partialFourierL2 (Lp.stronglyMeasurable f).measurable
    (Lp.memLp f)).choose_spec
  exact ⟨h.1.stronglyMeasurable, h.2⟩

/-- Partial Fourier transformation on the product `L²` space. -/
def partialFourierL2 (f : Lp Y 2 μprod) : Lp Y 2 μprod :=
  (partialFourierL2Rep_spec ν f).2.1.toLp _

/-- Almost every section of the partial transform is its one-dimensional Fourier transform. -/
theorem partialFourierL2_section (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, ∀ hu : MemLp (fun c => f (a, c)) 2 volume,
      (fun ω => partialFourierL2 ν f (a, ω)) =ᵐ[volume]
        ⇑(𝓕 (hu.toLp _) : Lp Y 2 (volume : Measure ℝ)) := by
  have heq : (fun p => partialFourierL2 ν f p) =ᵐ[ν.prod volume]
      partialFourierL2Rep ν f := (partialFourierL2Rep_spec ν f).2.1.coeFn_toLp
  have hs := Measure.ae_ae_of_ae_prod heq
  filter_upwards [(partialFourierL2Rep_spec ν f).2.2, hs] with a ha hb
  intro hu
  exact Filter.EventuallyEq.trans hb (ha hu)

/-- The `L²` class of a section, with value zero on exceptional sections. -/
def prodL2Section (f : Lp Y 2 μprod) (a : H) : Lp Y 2 (volume : Measure ℝ) := by
  classical
  exact if h : MemLp (fun c => f (a, c)) 2 volume then h.toLp _ else 0

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [SecondCountableTopology Y] in
/-- Almost every section class is represented by the original section. -/
theorem prodL2Section_coe (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, ⇑(prodL2Section ν f a) =ᵐ[volume] fun c => f (a, c) := by
  filter_upwards [ae_memLp_prod_section ν (Lp.memLp f)] with a ha
  simp only [prodL2Section, dif_pos ha]
  exact ha.coeFn_toLp

omit [InnerProductSpace ℂ Y] in
/-- Product `L²` functions are equal if almost every section class agrees. -/
theorem prodL2Section_ext {f g : Lp Y 2 μprod}
    (h : ∀ᵐ a ∂ν, prodL2Section ν f a = prodL2Section ν g a) : f = g := by
  borelize Y
  apply Lp.ext
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable f).measurable
      (Lp.stronglyMeasurable g).measurable)).mpr
  filter_upwards [h, prodL2Section_coe ν f, prodL2Section_coe ν g] with a ha hf hg
  exact hf.symm.trans (ha ▸ hg)

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [SecondCountableTopology Y] in
/-- Taking a section commutes almost everywhere with addition. -/
theorem prodL2Section_add (f g : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, prodL2Section ν (f + g) a = prodL2Section ν f a + prodL2Section ν g a := by
  filter_upwards [prodL2Section_coe ν (f + g), prodL2Section_coe ν f,
    prodL2Section_coe ν g, Measure.ae_ae_of_ae_prod (Lp.coeFn_add f g)] with a hfg hf hg he
  apply Lp.ext
  exact hfg.trans (Filter.EventuallyEq.trans he
    ((hf.add hg).symm.trans (Lp.coeFn_add _ _).symm))

omit [CompleteSpace Y] [SecondCountableTopology Y] in
/-- Taking a section commutes almost everywhere with scalar multiplication. -/
theorem prodL2Section_smul (z : ℂ) (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, prodL2Section ν (z • f) a = z • prodL2Section ν f a := by
  filter_upwards [prodL2Section_coe ν (z • f), prodL2Section_coe ν f,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_smul z f)] with a hzf hf he
  apply Lp.ext
  exact hzf.trans (Filter.EventuallyEq.trans he
    ((hf.const_smul z).symm.trans (Lp.coeFn_smul _ _).symm))

/-- Partial Fourier transformation commutes almost everywhere with taking sections. -/
theorem prodL2Section_partialFourierL2 (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, prodL2Section ν (partialFourierL2 ν f) a = 𝓕 (prodL2Section ν f a) := by
  filter_upwards [prodL2Section_coe ν (partialFourierL2 ν f), partialFourierL2_section ν f,
    ae_memLp_prod_section ν (Lp.memLp f)] with a ht hF hf
  simp only [prodL2Section, dif_pos hf]
  exact Lp.ext (ht.trans (hF hf))

/-- Partial Fourier transformation preserves the norm. -/
theorem norm_partialFourierL2 (f : Lp Y 2 μprod) : ‖partialFourierL2 ν f‖ = ‖f‖ := by
  have he : (∫⁻ p, ‖partialFourierL2 ν f p‖ₑ ^ 2 ∂μprod) =
      ∫⁻ p, ‖f p‖ₑ ^ 2 ∂μprod := by
    rw [lintegral_prod _ ((Lp.stronglyMeasurable _).enorm.pow_const 2).aemeasurable,
      lintegral_prod _ ((Lp.stronglyMeasurable _).enorm.pow_const 2).aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [prodL2Section_coe ν (partialFourierL2 ν f), prodL2Section_coe ν f,
      prodL2Section_partialFourierL2 ν f] with a hF hf he
    calc
      (∫⁻ c, ‖partialFourierL2 ν f (a, c)‖ₑ ^ 2) =
          ∫⁻ c, ‖prodL2Section ν (partialFourierL2 ν f) a c‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hF] with c hc
        rw [hc]
      _ = ∫⁻ c, ‖prodL2Section ν f a c‖ₑ ^ 2 := by
        rw [he, ← eLpNorm_two_sq_eq_lintegral_enorm_sq',
          ← eLpNorm_two_sq_eq_lintegral_enorm_sq', ← Lp.enorm_def, ← Lp.enorm_def]
        congr 1
        exact (Lp.fourierTransformₗᵢ ℝ Y).enorm_map _
      _ = ∫⁻ c, ‖f (a, c)‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hf] with c hc
        rw [hc]
  simp only [Lp.norm_def, eLpNorm_two_eq_lintegral_enorm_sq, he]

/-- Partial Fourier transformation as a complex linear isometry. -/
def partialFourierL2ₗᵢ : Lp Y 2 μprod →ₗᵢ[ℂ] Lp Y 2 μprod where
  toFun := partialFourierL2 ν
  map_add' f g := by
    apply prodL2Section_ext ν
    filter_upwards [prodL2Section_partialFourierL2 ν (f + g),
      prodL2Section_partialFourierL2 ν f, prodL2Section_partialFourierL2 ν g,
      prodL2Section_add ν f g,
      prodL2Section_add ν (partialFourierL2 ν f) (partialFourierL2 ν g)]
      with a hfg hf hg hs ht
    rw [hfg, hs, FourierTransform.fourier_add, ht, hf, hg]
  map_smul' z f := by
    simp only [RingHom.id_apply]
    apply prodL2Section_ext ν
    filter_upwards [prodL2Section_partialFourierL2 ν (z • f),
      prodL2Section_partialFourierL2 ν f, prodL2Section_smul ν z f,
      prodL2Section_smul ν z (partialFourierL2 ν f)] with a hzf hf hs ht
    rw [hzf, hs, fourier_smul, ht, hf]
  norm_map' := norm_partialFourierL2 ν

/-- Reflection in the second coordinate preserves the product measure. -/
theorem measurePreserving_prodNeg :
    MeasurePreserving (fun p : H × ℝ => (p.1, -p.2)) μprod μprod :=
  (MeasurePreserving.id ν).prod (Measure.measurePreserving_neg volume)

/-- Reflection in the second coordinate as a map of product `L²` spaces. -/
def prodL2Reflect (f : Lp Y 2 μprod) : Lp Y 2 μprod :=
  Lp.compMeasurePreserving _ (measurePreserving_prodNeg ν) f

omit [InnerProductSpace ℂ Y] [CompleteSpace Y] [SecondCountableTopology Y] in
/-- Reflection of a product function acts by reflection on almost every section. -/
theorem prodL2Section_reflect (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, prodL2Section ν (prodL2Reflect ν f) a =
      Lp.compMeasurePreserving (fun c : ℝ => -c)
        (Measure.measurePreserving_neg volume) (prodL2Section ν f a) := by
  filter_upwards [prodL2Section_coe ν (prodL2Reflect ν f), prodL2Section_coe ν f,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_compMeasurePreserving f (measurePreserving_prodNeg ν))]
    with a hr hf he
  apply Lp.ext
  exact hr.trans (Filter.EventuallyEq.trans he
    (((Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp hf).symm.trans
      (Lp.coeFn_compMeasurePreserving _ (Measure.measurePreserving_neg volume)).symm))

/-- The reflected partial transform has inverse-Fourier sections. -/
theorem prodL2Section_inverse (f : Lp Y 2 μprod) :
    ∀ᵐ a ∂ν, prodL2Section ν (prodL2Reflect ν (partialFourierL2 ν f)) a =
      𝓕⁻ (prodL2Section ν f a) := by
  filter_upwards [prodL2Section_reflect ν (partialFourierL2 ν f),
    prodL2Section_partialFourierL2 ν f] with a hr hf
  rw [hr, hf, Lp.fourierInv_eq_reflect_fourier]

/-- Partial Fourier transformation on the product space is surjective. -/
theorem partialFourierL2_surjective : Function.Surjective (partialFourierL2 ν (Y := Y)) := by
  intro f
  refine ⟨prodL2Reflect ν (partialFourierL2 ν f), prodL2Section_ext ν ?_⟩
  filter_upwards [prodL2Section_partialFourierL2 ν (prodL2Reflect ν (partialFourierL2 ν f)),
    prodL2Section_inverse ν f] with a hF hI
  rw [hF, hI, fourier_fourierInv_eq]

/-- The partial Fourier unitary on a product `L²` space in the ordinary frequency convention. -/
def partialFourierL2Equiv : Lp Y 2 μprod ≃ₗᵢ[ℂ] Lp Y 2 μprod :=
  LinearIsometryEquiv.ofSurjective (partialFourierL2ₗᵢ ν) (partialFourierL2_surjective ν)

omit [SecondCountableTopology Y] in
/-- Rescaling angular frequency preserves the appropriately normalized Lebesgue measure. -/
theorem measurePreserving_frequencyScale {k : ℝ} (hk : 0 < k) :
    MeasurePreserving (fun x : ℝ => k⁻¹ * x)
      (ENNReal.ofReal k⁻¹ • volume) volume := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_smul, Real.map_volume_mul_left (inv_ne_zero hk.ne'), inv_inv,
    abs_of_pos hk, smul_smul, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hk)),
    inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one, one_smul]

/-- Rescaling ordinary frequency gives normalized angular Lebesgue measure. -/
theorem measurePreserving_frequencyScaleInv {k : ℝ} (hk : 0 < k) :
    MeasurePreserving (fun x : ℝ => k * x) volume (ENNReal.ofReal k⁻¹ • volume) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Real.map_volume_mul_left hk.ne', abs_of_pos (inv_pos.mpr hk)]

/-- Composition with frequency rescaling is a unitary between normalized product spaces. -/
def frequencyScaleL2Equiv (k : ℝ) (hk : 0 < k) :
    Lp Y 2 μprod ≃ₗᵢ[ℂ] Lp Y 2 (ν.prod (ENNReal.ofReal k⁻¹ • (volume : Measure ℝ))) := by
  let hp := (MeasurePreserving.id ν).prod (measurePreserving_frequencyScale hk)
  let hi := (MeasurePreserving.id ν).prod (measurePreserving_frequencyScaleInv hk)
  apply LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (Prod.map id (fun x : ℝ => k⁻¹ * x)) hp)
  intro f
  refine ⟨Lp.compMeasurePreserving (Prod.map id (fun x : ℝ => k * x)) hi f, ?_⟩
  change Lp.compMeasurePreserving _ hp (Lp.compMeasurePreserving _ hi f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (Prod.map (id : H → H) (fun x : ℝ => k * x)) ∘
      (Prod.map id (fun x : ℝ => k⁻¹ * x)) = id := by
    funext ⟨a, c⟩
    simp [mul_inv_cancel_left₀ hk.ne']
  simp [he]

/-- The partial Fourier unitary using angular frequencies and measure `dω / (2π)`. -/
def angularPartialFourierL2Equiv :
    Lp Y 2 μprod ≃ₗᵢ[ℂ]
      Lp Y 2 (ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • (volume : Measure ℝ))) :=
  (partialFourierL2Equiv ν).trans (frequencyScaleL2Equiv ν (2 * Real.pi) (by positivity))

/-- The angular unitary is represented by frequency rescaling of the partial Fourier transform. -/
theorem angularPartialFourierL2Equiv_coe (f : Lp Y 2 μprod) :
    ⇑(angularPartialFourierL2Equiv ν f) =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)]
      fun p => partialFourierL2 ν f (p.1, (2 * Real.pi)⁻¹ * p.2) :=
  Lp.coeFn_compMeasurePreserving _
    ((MeasurePreserving.id ν).prod (measurePreserving_frequencyScale (by positivity)))

/-- A jointly measurable representative of the angular partial Fourier unitary. -/
theorem angularPartialFourierL2Equiv_coe_rep (f : Lp Y 2 μprod) :
    ⇑(angularPartialFourierL2Equiv ν f) =ᵐ[ν.prod (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume)]
      fun p => partialFourierL2Rep ν f (p.1, (2 * Real.pi)⁻¹ * p.2) := by
  apply (angularPartialFourierL2Equiv_coe ν f).trans
  have hp := ((MeasurePreserving.id ν).prod
    (measurePreserving_frequencyScale (show 0 < 2 * Real.pi by positivity))).quasiMeasurePreserving
  exact hp.ae_eq_comp (partialFourierL2Rep_spec ν f).2.1.coeFn_toLp

end MeasureTheory
