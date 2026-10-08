import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_det
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_map_withDensity_comp
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_e3_coordinate_measurePreserving
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_density_fst_map
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_sq_lintegral
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_source_push (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) :
    (((volume : Measure Pt).restrict (atlasRadialSource C)).withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ (atlasRadial C) x).det|)).map (atlasPair C) =
        (3:ENNReal)⁻¹ • weightedPairMu D := by
  classical
  let I : Set ℝ := atlasInterval C
  let R : Set ℝ := Set.Ioo (0 : ℝ) 1
  let m : Measure ℝ := volume.restrict I
  let ν : Measure ℝ := volume.restrict R
  let μ : Measure (ℝ × ℝ) := m.prod m
  let γ : ℝ → Pt := atlasGamma C
  let Q : (ℝ × ℝ) → Pt × Pt := fun q => (γ q.1, γ q.2)
  let a : ℝ → ENNReal := fun t => ENNReal.ofReal (atlasSpeed C t)
  let d : Pt × Pt → ENNReal := fun q => ENNReal.ofReal (pairDens D q)
  let J : (ℝ × ℝ) → ENNReal := fun q => a q.1 * a q.2 * d (Q q)
  let w : ℝ → ENNReal := fun r => ENNReal.ofReal (r ^ 2)
  let coord : Pt → (ℝ × ℝ) × ℝ := fun x => ((x 0, x 1), x 2)
  let Z : Set ((ℝ × ℝ) × ℝ) := (I ×ˢ I) ×ˢ R
  let broad : Set Pt := coord ⁻¹' Z
  let W : ((ℝ × ℝ) × ℝ) → ENNReal := fun z => J z.1 * w z.2
  have hI : MeasurableSet I := measurableSet_Ioo.union measurableSet_Ioo
  have hR : MeasurableSet R := measurableSet_Ioo
  have hZ : MeasurableSet Z := (hI.prod hI).prod hR
  have hcoord : Measurable coord := e3_coordinate_measurePreserving.measurable
  have hbroad : MeasurableSet broad := hZ.preimage hcoord
  have hγ : Measurable γ := by
    dsimp [γ, atlasGamma]
    apply Measurable.ite measurableSet_Iio
    · dsimp [atlasCircle, circlePt]; fun_prop
    · dsimp [atlasCircle, circlePt]; fun_prop
  have hQ : Measurable Q := (hγ.comp measurable_fst).prodMk (hγ.comp measurable_snd)
  have ha : Measurable a := by
    exact (Measurable.ite measurableSet_Iio measurable_const measurable_const).ennreal_ofReal
  have hd : Measurable d := (pair_measurable D).2.2.2.2.1.ennreal_ofReal
  have hJ : Measurable J := ((ha.comp measurable_fst).mul
    (ha.comp measurable_snd)).mul (hd.comp hQ)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hW : Measurable W := (hJ.comp measurable_fst).mul (hw.comp measurable_snd)
  have hspeed : ∀ t, 0 ≤ atlasSpeed C t := by
    intro t
    unfold atlasSpeed
    split <;> exact (hC.radius_pos _).le
  have hden : ∀ q, 0 ≤ pairDens D q := (pair_measurable D).2.2.2.2.2
  have hsrc : MeasurableSet (atlasRadialSource C) :=
    (circle_atlas_radial_regular D C hC).2.2.2.1
  have hfactor (x : Pt) (hx : x ∈ atlasRadialSource C) :
      ENNReal.ofReal |(fderiv ℝ (atlasRadial C) x).det| = W (coord x) := by
    rw [circle_atlas_radial_det D C hC x hx]
    change ENNReal.ofReal ((x 2)^2 * atlasSpeed C (x 0) * atlasSpeed C (x 1) *
      pairDens D (atlasPair C x)) = _
    have heq : (x 2)^2 * atlasSpeed C (x 0) * atlasSpeed C (x 1) *
        pairDens D (atlasPair C x) =
        (atlasSpeed C (x 0) * atlasSpeed C (x 1) * pairDens D (atlasPair C x)) * (x 2)^2 := by ring
    rw [heq, ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (hspeed _) (hspeed _)) (hden _)),
      ENNReal.ofReal_mul (mul_nonneg (hspeed _) (hspeed _)), ENNReal.ofReal_mul (hspeed _)]
    rfl
  have hremove : ((volume : Measure Pt).restrict (atlasRadialSource C)).withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ (atlasRadial C) x).det|) =
      ((volume : Measure Pt).restrict broad).withDensity (fun x => W (coord x)) := by
    rw [← withDensity_indicator hsrc, ← withDensity_indicator hbroad]
    congr 1
    funext x
    by_cases hb : x ∈ broad
    · have hb' : x 0 ∈ I ∧ x 1 ∈ I ∧ x 2 ∈ R := ⟨hb.1.1, hb.1.2, hb.2⟩
      by_cases hc : cross (γ (x 0)) (γ (x 1)) = 0
      · have hn : x ∉ atlasRadialSource C := fun hx => hx.2.2.2 hc
        rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hb]
        simp [W, J, d, Q, γ, coord, atlasPair, pairDens, santaloDens, hc]
      · have hx : x ∈ atlasRadialSource C := ⟨hb'.1, hb'.2.1, hb'.2.2, hc⟩
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hb]
        exact hfactor x hx
    · have hn : x ∉ atlasRadialSource C := fun hx => hb ⟨⟨hx.1, hx.2.1⟩, hx.2.2.1⟩
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hb]
  have hcoords : ((volume : Measure Pt).restrict broad).map coord = μ.prod ν := by
    change ((volume : Measure Pt).restrict (coord ⁻¹' Z)).map coord = _
    rw [← Measure.restrict_map hcoord hZ, e3_coordinate_measurePreserving.map_eq]
    change (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
      (volume : Measure ℝ)).restrict ((I ×ˢ I) ×ˢ R) = _
    rw [← Measure.prod_restrict, ← Measure.prod_restrict]
  have hweighted : (((volume : Measure Pt).restrict broad).withDensity
      (fun x => W (coord x))).map coord = (μ.prod ν).withDensity W := by
    rw [map_withDensity_comp _ coord W hcoord hW, hcoords]
  let σ : Measure ℝ := m.withDensity a
  letI : SFinite m := by dsimp [m]; infer_instance
  letI : SFinite ν := by dsimp [ν]; infer_instance
  letI : SFinite μ := by dsimp [μ]; infer_instance
  letI : SFinite σ := by dsimp [σ]; infer_instance
  have hsource : σ.map γ = boundaryMu D := hC.source_map
  have hpairbase : (σ.prod σ).map Q = pairMu D := by
    change (σ.prod σ).map (Prod.map γ γ) = _
    rw [← Measure.map_prod_map σ σ hγ hγ, hsource]
    rfl
  have hpairdensity : (μ.withDensity J).map Q = weightedPairMu D := by
    have hab : Measurable (fun q : ℝ × ℝ => a q.1 * a q.2) :=
      (ha.comp measurable_fst).mul (ha.comp measurable_snd)
    have hwd : μ.withDensity J = (σ.prod σ).withDensity (fun q => d (Q q)) := by
      change (m.prod m).withDensity ((fun q : ℝ × ℝ => a q.1 * a q.2) *
        (d ∘ Q)) = _
      rw [withDensity_mul _ hab (hd.comp hQ), ← prod_withDensity ha ha]
      rfl
    rw [hwd, map_withDensity_comp _ Q d hQ hd, hpairbase]
    rfl
  have hradial : ((μ.prod ν).withDensity W).map Prod.fst =
      (3 : ENNReal)⁻¹ • μ.withDensity J := by
    rw [radial_density_fst_map μ ν J w hJ hw]
    change (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r^2)) • _ = _
    rw [radial_sq_lintegral]
  rw [hremove]
  calc
    (((volume : Measure Pt).restrict broad).withDensity (fun x => W (coord x))).map (atlasPair C)
        = ((((volume : Measure Pt).restrict broad).withDensity (fun x => W (coord x))).map coord).map
          (fun z : (ℝ × ℝ) × ℝ => Q z.1) := by
            exact (Measure.map_map (hQ.comp measurable_fst) hcoord).symm
    _ = ((μ.prod ν).withDensity W).map (fun z : (ℝ × ℝ) × ℝ => Q z.1) := by rw [hweighted]
    _ = (((μ.prod ν).withDensity W).map Prod.fst).map Q := by
      rw [Measure.map_map hQ measurable_fst]
      rfl
    _ = ((3 : ENNReal)⁻¹ • μ.withDensity J).map Q := by rw [hradial]
    _ = (3 : ENNReal)⁻¹ • weightedPairMu D := by rw [Measure.map_smul, hpairdensity]
