import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_cap_domains
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_native_source_map
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Topology Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.chord_eq (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    dist (circlePt c (e 0) (e 1) r s) (circlePt c (e 0) (e 1) r t) =
      2 * r * |Real.sin ((s - t) / 2)| := by
  have hi : inner ℝ ((Real.cos s - Real.cos t) • e 0)
      ((Real.sin s - Real.sin t) • e 1) = 0 := by
    simp [inner_smul_left, inner_smul_right, he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
  have hsub : circlePt c (e 0) (e 1) r s - circlePt c (e 0) (e 1) r t =
      r • ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1) := by
    unfold circlePt
    module
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((Real.cos s - Real.cos t) • e 0) ((Real.sin s - Real.sin t) • e 1) hi
  simp only [norm_smul, Real.norm_eq_abs, he.norm_eq_one, mul_one, ← pow_two, sq_abs] at hn
  have htrig : (Real.cos s - Real.cos t) ^ 2 + (Real.sin s - Real.sin t) ^ 2 =
      4 * Real.sin ((s - t) / 2) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq s
    have h2 := Real.sin_sq_add_cos_sq t
    have h3 := Real.cos_sub s t
    have h4 := Real.cos_two_mul ((s - t) / 2)
    have h5 := Real.sin_sq_add_cos_sq ((s - t) / 2)
    rw [show 2 * ((s - t) / 2) = s - t by ring] at h4
    nlinarith
  have hn2 : ‖(Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1‖ =
      2 * |Real.sin ((s - t) / 2)| := by
    nlinarith [sq_abs (Real.sin ((s - t) / 2)),
      norm_nonneg ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1),
      abs_nonneg (Real.sin ((s - t) / 2))]
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn2]
  ring
open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.chord_lower_local (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (k : ℝ) (hk : k < 1) : ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, |s - t| < δ →
      r * k * |s - t| ≤ dist (circlePt c (e 0) (e 1) r s) (circlePt c (e 0) (e 1) r t) := by
  obtain ⟨ε, hε, hεprop⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sinc.continuousAt (1-k) (by linarith)
  refine ⟨2*ε, by positivity, ?_⟩
  intro s t hst
  have hsk : k ≤ Real.sinc ((s-t)/2) := by
    have h := hεprop (x := (s-t)/2) (by
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith)
    rw [Real.dist_eq, Real.sinc_zero] at h
    have hh := (abs_lt.mp h).1
    linarith
  have hsinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  rw [SphereGeom.Aux.ArcLength.chord_eq c e he r hr s t, hsinc ((s-t)/2), abs_mul,
    abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    r * k * |s-t| ≤ r * Real.sinc ((s-t)/2) * |s-t| := by
      gcongr
    _ ≤ r * |Real.sinc ((s-t)/2)| * |s-t| := by
      gcongr
      exact le_abs_self _
    _ = 2 * r * (|s-t| / 2 * |Real.sinc ((s-t)/2)|) := by ring
open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.injOn_Icc (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hb : b - a < 2 * Real.pi) :
    Set.InjOn (circlePt c (e 0) (e 1) r) (Set.Icc a b) := by
  intro s hs t ht heq
  have hd : 2*r*|Real.sin ((s-t)/2)| = 0 := by
    rw [← SphereGeom.Aux.ArcLength.chord_eq c e he r hr s t, heq, dist_self]
  have hz : Real.sin ((s-t)/2) = 0 := by
    have hnr : 2*r ≠ 0 := by positivity
    exact abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hnr)
  have hst := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2] : -Real.pi < (s-t)/2)
    (by linarith [hs.2, ht.1] : (s-t)/2 < Real.pi)).mp hz
  linarith
open MeasureTheory SphereGeom Topology

private theorem SphereGeom.Aux.ArcLength.inverse_modulus_Icc (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hb : b - a < 2 * Real.pi) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      dist (circlePt c (e 0) (e 1) r s) (circlePt c (e 0) (e 1) r t) < ε → |s-t| < δ := by
  let f : Set.Icc a b → E3 := fun s => circlePt c (e 0) (e 1) r s
  have hc : Continuous f := by
    dsimp [f, circlePt]
    fun_prop
  have hi : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact SphereGeom.Aux.ArcLength.injOn_Icc c e he r hr a b hb s.property t.property h
  let h := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorph
  letI : CompactSpace (Set.range f) := h.compactSpace
  have hu : UniformContinuous h.symm := CompactSpace.uniformContinuous_of_continuous h.symm.continuous
  obtain ⟨ε, hε, hprop⟩ := Metric.uniformContinuous_iff.mp hu δ hδ
  refine ⟨ε, hε, ?_⟩
  intro s hs t ht hst
  have hh := hprop (a := h ⟨s,hs⟩) (b := h ⟨t,ht⟩) hst
  simpa only [h.symm_apply_apply, Subtype.dist_eq, Real.dist_eq] using hh
open MeasureTheory SphereGeom Topology Metric

private theorem SphereGeom.Aux.ArcLength.short_arc_measure_lower (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hb : b-a < 2*Real.pi) :
    ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map (circlePt c (e 0) (e 1) r) ≤ arcMeasure := by
  let f : Set.Icc a b → E3 := fun s => circlePt c (e 0) (e 1) r s
  let μ : Measure (Set.Icc a b) := volume.comap Subtype.val
  let ν : Measure E3 := ENNReal.ofReal r • μ.map f
  have hc : Continuous f := by dsimp [f, circlePt]; fun_prop
  have hi : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact SphereGeom.Aux.ArcLength.injOn_Icc c e he r hr a b hb s.property t.property h
  have hf : MeasurableEmbedding f := (hc.isClosedEmbedding hi).measurableEmbedding
  have hv : MeasurableEmbedding (Subtype.val : Set.Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have heq : ν = ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map
      (circlePt c (e 0) (e 1) r) := by
    have hcp : Continuous (circlePt c (e 0) (e 1) r) := by unfold circlePt; fun_prop
    dsimp only [ν, μ]
    change ENNReal.ofReal r • (volume.comap (Subtype.val : Set.Icc a b → ℝ)).map
      ((circlePt c (e 0) (e 1) r) ∘ Subtype.val) = _
    rw [← Measure.map_map hcp.measurable hv.measurable, hv.map_comap, Subtype.range_val]
  rw [← heq]
  apply Measure.le_iff.mpr
  intro S hS
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro k hk
  have hkt : k ≠ ⊤ := ne_top_of_le_ne_top (by simp) hk.le
  have hkr : k.toReal < 1 := by
    have h := (ENNReal.toReal_lt_toReal hkt (by simp : (1:ENNReal) ≠ ⊤)).mpr hk
    simpa using h
  obtain ⟨δ,hδ,hlocal⟩ := SphereGeom.Aux.ArcLength.chord_lower_local c e he r hr k.toReal hkr
  obtain ⟨ε,hε,hmod⟩ := SphereGeom.Aux.ArcLength.inverse_modulus_Icc c e he r hr a b hb δ hδ
  have hH : k • ν ≤ arcMeasure := by
    apply Measure.le_hausdorffMeasure 1 (k • ν) (ENNReal.ofReal (ε/2)) (by positivity)
    intro T hT
    rw [ENNReal.rpow_one, Measure.smul_apply]
    change k * (ν T) ≤ ediam T
    dsimp only [ν]
    rw [Measure.smul_apply, hf.map_apply]
    change k * (ENNReal.ofReal r * μ (f ⁻¹' T)) ≤ ediam T
    have hmass : μ (f ⁻¹' T) ≤ ediam (f ⁻¹' T) := by
      rw [show μ = volume.comap Subtype.val from rfl, hv.comap_apply]
      exact (Real.volume_le_diam _).trans_eq (isometry_subtype_coe.ediam_image _)
    calc
      k * (ENNReal.ofReal r * μ (f ⁻¹' T)) ≤
          (k * ENNReal.ofReal r) * ediam (f ⁻¹' T) := by
        rw [← mul_assoc]
        gcongr
      _ ≤ ediam T := by
        simp only [ediam, ENNReal.mul_iSup, iSup_le_iff]
        intro s hs t ht
        have hed : edist (f s) (f t) ≤ ENNReal.ofReal (ε/2) :=
          (edist_le_ediam_of_mem (show f s ∈ T from hs) (show f t ∈ T from ht)).trans hT
        have hdist : dist (f s) (f t) ≤ ε/2 := by
          apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ε/2)).mp
          simpa only [← edist_dist] using hed
        have hpar := hmod s s.property t t.property (by change dist (f s) (f t) < ε; linarith)
        have hlow := hlocal s t hpar
        have hlowE := ENNReal.ofReal_le_ofReal hlow
        rw [ENNReal.ofReal_mul (mul_nonneg hr.le ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal hkt] at hlowE
        have hdsub : ENNReal.ofReal |(s:ℝ)-(t:ℝ)| = edist s t := by
          rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
        rw [hdsub, ← edist_dist] at hlowE
        have hh : (k * ENNReal.ofReal r) * edist s t ≤ edist (f s) (f t) := by
          simpa only [mul_comm k] using hlowE
        exact hh.trans (edist_le_ediam_of_mem (show f s ∈ T from hs) (show f t ∈ T from ht))
  exact (Measure.le_iff.mp hH S hS)
open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.restrict_short_circle_arc_eq_map (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b : ℝ) (hb : b - a < 2 * Real.pi) :
  arcMeasure.restrict (circlePt c (e 0) (e 1) r '' Set.Icc a b) =
    ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map (circlePt c (e 0) (e 1) r) := by
  let R : NNReal := ⟨r, hr.le⟩
  let R : NNReal := ⟨r, hr.le⟩
  have hc : Continuous (circlePt c (e 0) (e 1) r) := by unfold circlePt; fun_prop
  have his : MeasurableSet (circlePt c (e 0) (e 1) r '' Set.Icc a b) :=
    (isCompact_Icc.image hc).measurableSet
  have hcoe : (↑R : ENNReal) = ENNReal.ofReal r := ENNReal.coe_nnreal_eq R
  have hl : LipschitzWith R (circlePt c (e 0) (e 1) r) := by
    have hd (t : ℝ) : HasDerivAt (circlePt c (e 0) (e 1) r)
        (r • ((-Real.sin t) • e 0 + Real.cos t • e 1)) t := by
      exact (((Real.hasDerivAt_cos t).smul_const (e 0)).add
        ((Real.hasDerivAt_sin t).smul_const (e 1))).const_smul r |>.const_add c
    have hn (t : ℝ) : ‖(-Real.sin t) • e 0 + Real.cos t • e 1‖ = 1 := by
      have hi : inner ℝ ((-Real.sin t) • e 0) (Real.cos t • e 1) = 0 := by
        simp [inner_smul_left, inner_smul_right, he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
      have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((-Real.sin t) • e 0) (Real.cos t • e 1) hi
      simp only [norm_smul, Real.norm_eq_abs, he.norm_eq_one, mul_one, ← pow_two, sq_abs, neg_sq] at hs
      have htrig := Real.sin_sq_add_cos_sq t
      nlinarith [norm_nonneg ((-Real.sin t) • e 0 + Real.cos t • e 1)]
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    apply convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hd t).hasDerivWithinAt) _ (Set.mem_univ _) (Set.mem_univ _)
    intro t _
    change ‖r • ((-Real.sin t) • e 0 + Real.cos t • e 1)‖ ≤ r
    rw [norm_smul, hn t, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply hc.measurable hS,
    Measure.restrict_apply' measurableSet_Icc]
  change arcMeasure (S ∩ (circlePt c (e 0) (e 1) r '' Set.Icc a b)) =
    ENNReal.ofReal r * volume (circlePt c (e 0) (e 1) r ⁻¹' S ∩ Set.Icc a b)
  apply le_antisymm
  · have hset : S ∩ (circlePt c (e 0) (e 1) r '' Set.Icc a b) =
        circlePt c (e 0) (e 1) r '' (circlePt c (e 0) (e 1) r ⁻¹' S ∩ Set.Icc a b) := by
      ext x
      constructor
      · rintro ⟨hx, y,hy,rfl⟩
        exact ⟨y,⟨hx,hy⟩,rfl⟩
      · rintro ⟨y,⟨hyS,hyI⟩,rfl⟩
        exact ⟨hyS,y,hyI,rfl⟩
    rw [hset]
    have hu := hl.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤1)
      (circlePt c (e 0) (e 1) r ⁻¹' S ∩ Set.Icc a b)
    rw [ENNReal.rpow_one, hausdorffMeasure_real, hcoe] at hu
    exact hu
  · have hpre : circlePt c (e 0) (e 1) r ⁻¹'
        (S ∩ (circlePt c (e 0) (e 1) r '' Set.Icc a b)) ∩ Set.Icc a b =
        circlePt c (e 0) (e 1) r ⁻¹' S ∩ Set.Icc a b := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,t,h.2,rfl⟩,h.2⟩
    have hlow := Measure.le_iff'.mp
      (SphereGeom.Aux.ArcLength.short_arc_measure_lower c e he r hr a b hb)
      (S ∩ (circlePt c (e 0) (e 1) r '' Set.Icc a b))
    rw [Measure.smul_apply, Measure.map_apply hc.measurable (hS.inter his),
      Measure.restrict_apply' measurableSet_Icc, hpre] at hlow
    exact hlow
open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.restrict_circle_arc_eq_map (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hab : a ≤ b) (hb : b-a ≤ 2*Real.pi) :
    arcMeasure.restrict (circlePt c (e 0) (e 1) r '' Set.Icc a b) =
      ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map (circlePt c (e 0) (e 1) r) := by
  let m : ℝ := (a+b)/2
  let f : ℝ → E3 := circlePt c (e 0) (e 1) r
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : m-a < 2*Real.pi := by dsimp [m]; linarith [Real.pi_pos]
  have hright : b-m < 2*Real.pi := by dsimp [m]; linarith [Real.pi_pos]
  have hunion := Set.Icc_union_Icc_eq_Icc ham hmb
  have hc : Continuous f := by dsimp only [f]; unfold circlePt; fun_prop
  have hms : MeasurableSet (f '' Set.Icc m b) := (isCompact_Icc.image hc).measurableSet
  have hinter : (f '' Set.Icc a m) ∩ (f '' Set.Icc m b) ⊆ {f a, f m} := by
    intro x hx
    obtain ⟨s,hs,hsx⟩ := hx.1
    obtain ⟨t,ht,htx⟩ := hx.2
    have heq : f s = f t := hsx.trans htx.symm
    by_cases hend : s=a ∧ t=b
    · rw [← hsx, hend.1]
      exact Set.mem_insert _ _
    · have hstlo : -Real.pi < (s-t)/2 := by
        by_cases hsa : s=a
        · have htb : t<b := lt_of_le_of_ne ht.2 (by intro h; exact hend ⟨hsa,h⟩)
          linarith [hs.1]
        · have has : a<s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
          linarith [ht.2]
      have hsthi : (s-t)/2 < Real.pi := by linarith [hs.2, ht.1, Real.pi_pos]
      have hz : Real.sin ((s-t)/2) = 0 := by
        have hd : 2*r*|Real.sin ((s-t)/2)| = 0 := by
          rw [← SphereGeom.Aux.ArcLength.chord_eq c e he r hr s t]
          change dist (f s) (f t) = 0
          rw [heq,dist_self]
        exact abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (by positivity : 2*r ≠ 0))
      have hst : s=t := by
        have h := (Real.sin_eq_zero_iff_of_lt_of_lt hstlo hsthi).mp hz
        linarith
      have hsm : s=m := by linarith [hs.2, ht.1]
      rw [← hsx,hsm]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hnull : arcMeasure ((f '' Set.Icc a m) ∩ (f '' Set.Icc m b)) = 0 := by
    apply le_antisymm _ zero_le
    apply (measure_mono hinter).trans
    haveI := Measure.nullSingletonClass_hausdorff E3 (by norm_num : (0:ℝ)<1)
    change (μH[1] : Measure E3) {f a, f m} ≤ 0
    exact ((Set.toFinite ({f a, f m} : Set E3)).measure_zero (μH[1] : Measure E3)).le
  have hH := Measure.restrict_union_add_inter (μ := arcMeasure)
    (f '' Set.Icc a m) hms
  rw [Measure.restrict_zero_set hnull, add_zero, ← Set.image_union, hunion] at hH
  have hV := Measure.restrict_union_add_inter (μ := (volume : Measure ℝ))
    (Set.Icc a m) (measurableSet_Icc : MeasurableSet (Set.Icc m b))
  rw [hunion, Set.Icc_inter_Icc_eq_singleton ham hmb,
    Measure.restrict_zero_set (measure_singleton m), add_zero] at hV
  change arcMeasure.restrict (f '' Set.Icc a b) = ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map f
  rw [hH, hV, Measure.map_add _ _ hc.measurable, smul_add]
  exact congrArg₂ (· + ·)
    (SphereGeom.Aux.ArcLength.restrict_short_circle_arc_eq_map c e he r hr a m hleft)
    (SphereGeom.Aux.ArcLength.restrict_short_circle_arc_eq_map c e he r hr m b hright)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_source_atlas (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    ∃ C : CircleEndpointAtlas, IsCircleEndpointAtlas D C := by
  classical
  obtain ⟨C,F,hF,hc0,hc1,hr0,hr1,hE,hr,hT0,hT,hparts,hAB,hfront,hder⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_endpoint_cap_domains D hD hK
  let A : ℝ := 2*Real.pi+1
  have hA : 0 < A := by dsimp [A]; linarith [Real.pi_pos]
  have hparts0 : atlasCircle C 0 '' Set.Ioo 0 (C.T 0) = arcA D \ F := by simpa using hparts 0
  have hparts1 : atlasCircle C 1 '' Set.Ioo 0 (C.T 1) = arcB D \ F := by simpa using hparts 1
  have hdisjoint : Disjoint (atlasCircle C 0 '' Set.Ioo 0 (C.T 0))
      (atlasCircle C 1 '' Set.Ioo 0 (C.T 1)) := by
    rw [hparts0,hparts1,Set.disjoint_left]
    intro z hz0 hz1
    exact hz0.2 (hAB ⟨hz0.1,hz1.1⟩)
  have hwindow (t : ℝ) (ht : t ∈ atlasInterval C) :
      (t < 0 ∧ t+A ∈ Set.Ioo 0 (C.T 0)) ∨
        (0 < t ∧ t-1 ∈ Set.Ioo 0 (C.T 1)) := by
    rcases ht with ht | ht
    · left
      change -A < t ∧ t < -A+C.T 0 at ht
      refine ⟨?_,?_,?_⟩ <;> dsimp [A] at * <;> linarith [hT 0]
    · right
      exact ⟨by linarith [ht.1],by linarith [ht.1],by linarith [ht.2]⟩
  have hunitA (z : Pt) (hz : z ∈ arcA D) : ‖z‖ = 1 := by
    by_cases hd : D = 0
    · simp [arcA,hd] at hz
    · exact (by simpa [arcA,hd] using hz : z ∈ SigmaD D ∧ ‖D+z‖ = 1).1.1
  have hunitB (z : Pt) (hz : z ∈ arcB D) : ‖z‖ = 1 := by
    by_cases hd : D = e
    · simp [arcB,hd] at hz
    · exact (by simpa [arcB,hd] using hz : z ∈ SigmaD D ∧ dist (D+z) e = 1).1.1
  have hunit : ∀ t ∈ atlasInterval C, ‖atlasGamma C t‖ = 1 := by
    intro t ht
    rcases hwindow t ht with ⟨htn,hs⟩ | ⟨htp,hs⟩
    · rw [atlasGamma,if_pos htn]
      apply hunitA
      have hh : atlasCircle C 0 (t+A) ∈ arcA D \ F := hparts0 ▸ Set.mem_image_of_mem _ hs
      exact hh.1
    · rw [atlasGamma,if_neg (not_lt.mpr htp.le)]
      apply hunitB
      have hh : atlasCircle C 1 (t-1) ∈ arcB D \ F := hparts1 ▸ Set.mem_image_of_mem _ hs
      exact hh.1
  have hinjCircle (i : Fin 2) : Set.InjOn (atlasCircle C i) (Set.Ioo 0 (C.T i)) := by
    intro s hs t ht heq
    have hd : 2*C.r i*|Real.sin ((s-t)/2)| = 0 := by
      rw [← SphereGeom.Aux.ArcLength.chord_eq (C.c i) (C.frame i) (hE i) (C.r i) (hr i) s t]
      change dist (atlasCircle C i s) (atlasCircle C i t) = 0
      rw [heq,dist_self]
    have hz : Real.sin ((s-t)/2) = 0 :=
      abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (hr i).ne'))
    have hh := (Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [hT i,hs.1,ht.2] : -Real.pi < (s-t)/2)
      (by linarith [hT i,hs.2,ht.1] : (s-t)/2 < Real.pi)).mp hz
    linarith
  have hinj : Set.InjOn (atlasGamma C) (atlasInterval C) := by
    intro s hs t ht heq
    rcases hwindow s hs with ⟨hsn,hss⟩ | ⟨hsp,hss⟩ <;>
      rcases hwindow t ht with ⟨htn,htt⟩ | ⟨htp,htt⟩
    · simp only [atlasGamma,if_pos hsn,if_pos htn] at heq
      have hh := hinjCircle 0 hss htt heq
      linarith
    · simp only [atlasGamma,if_pos hsn,if_neg (not_lt.mpr htp.le)] at heq
      have h0 := Set.mem_image_of_mem (atlasCircle C 0) hss
      have h1 := Set.mem_image_of_mem (atlasCircle C 1) htt
      exact False.elim ((Set.disjoint_left.mp hdisjoint) h0 (heq ▸ h1))
    · simp only [atlasGamma,if_neg (not_lt.mpr hsp.le),if_pos htn] at heq
      have h0 := Set.mem_image_of_mem (atlasCircle C 0) htt
      have h1 := Set.mem_image_of_mem (atlasCircle C 1) hss
      exact False.elim ((Set.disjoint_left.mp hdisjoint) h0 (heq.symm ▸ h1))
    · simp only [atlasGamma,if_neg (not_lt.mpr hsp.le),if_neg (not_lt.mpr htp.le)] at heq
      have hh := hinjCircle 1 hss htt heq
      linarith
  have himage : atlasGamma C '' atlasInterval C =
      (atlasCircle C 0 '' Set.Ioo 0 (C.T 0)) ∪ (atlasCircle C 1 '' Set.Ioo 0 (C.T 1)) := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      rcases hwindow t ht with ⟨htn,hs⟩ | ⟨htp,hs⟩
      · left
        exact ⟨t+A,hs,by simp [atlasGamma,htn,A]⟩
      · right
        exact ⟨t-1,hs,by simp [atlasGamma,not_lt.mpr htp.le]⟩
    · rintro (⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩)
      · refine ⟨s-A,Or.inl ⟨by dsimp [A]; linarith [hs.1],by dsimp [A]; linarith [hs.2]⟩,?_⟩
        have hneg : s-A < 0 := by dsimp [A]; linarith [hT 0,hs.2]
        simp only [atlasGamma,if_pos hneg]
        congr 1
        dsimp [A]
        ring
      · refine ⟨s+1,Or.inr ⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
        have hpos : 0 ≤ s+1 := by linarith [hs.1]
        simp [atlasGamma,not_lt.mpr hpos]
  have htangent : ∀ t ∈ atlasInterval C, ∃ k : ℝ,
      deriv (atlasGamma C) t = k • boundaryTau D (atlasGamma C t) ∧ |k| = atlasSpeed C t := by
    intro t ht
    rcases hwindow t ht with ⟨htn,hs⟩ | ⟨htp,hs⟩
    · have hv : atlasCircle C 0 (t+A) ∈ arcA D \ F := hparts0 ▸ Set.mem_image_of_mem _ hs
      have hraw := (hder 0 (t+A) hs).1
      have hn : ‖cross (nAv D) (atlasCircle C 0 (t+A))‖ = C.r 0 := by simpa using (hder 0 (t+A) hs).2
      have hraw' : HasDerivAt (atlasCircle C 0) (cross (nAv D) (atlasCircle C 0 (t+A))) (t+A) := by simpa using hraw
      have hcomp : HasDerivAt (fun s : ℝ => atlasCircle C 0 (s+A))
          (cross (nAv D) (atlasCircle C 0 (t+A))) t := by
        simpa only [Function.comp_def,id_eq,one_smul] using! hraw'.scomp t ((hasDerivAt_id t).add_const A)
      have heq : atlasGamma C =ᶠ[𝓝 t] (fun s => atlasCircle C 0 (s+A)) := by
        filter_upwards [eventually_lt_nhds htn] with s hsneg
        simp [atlasGamma,hsneg,A]
      have hd := (hcomp.congr_of_eventuallyEq heq).deriv
      refine ⟨C.r 0,?_,by simp [atlasSpeed,htn,abs_of_pos (hr 0)]⟩
      rw [hd]
      simp only [atlasGamma,if_pos htn]
      change cross (nAv D) (atlasCircle C 0 (t+A)) =
        C.r 0 • boundaryTau D (atlasCircle C 0 (t+A))
      rw [boundaryTau,if_pos hv.1,tanA,unitDir,hn,smul_smul,mul_inv_cancel₀ (hr 0).ne',one_smul]
    · have hv : atlasCircle C 1 (t-1) ∈ arcB D \ F := hparts1 ▸ Set.mem_image_of_mem _ hs
      have hvnot : atlasCircle C 1 (t-1) ∉ arcA D := by
        intro hA
        exact hv.2 (hAB ⟨hA,hv.1⟩)
      have hraw := (hder 1 (t-1) hs).1
      have hn : ‖cross (nBv D) (atlasCircle C 1 (t-1))‖ = C.r 1 := by simpa using (hder 1 (t-1) hs).2
      have hraw' : HasDerivAt (atlasCircle C 1) (-cross (nBv D) (atlasCircle C 1 (t-1))) (t-1) := by simpa using hraw
      have hcomp : HasDerivAt (fun s : ℝ => atlasCircle C 1 (s-1))
          (-cross (nBv D) (atlasCircle C 1 (t-1))) t := by
        simpa only [Function.comp_def,id_eq,one_smul] using! hraw'.scomp t ((hasDerivAt_id t).sub_const 1)
      have heq : atlasGamma C =ᶠ[𝓝 t] (fun s => atlasCircle C 1 (s-1)) := by
        filter_upwards [eventually_gt_nhds htp] with s hspos
        simp [atlasGamma,not_lt.mpr hspos.le]
      have hd := (hcomp.congr_of_eventuallyEq heq).deriv
      refine ⟨-(C.r 1),?_,by simp [atlasSpeed,not_lt.mpr htp.le,abs_of_pos (hr 1)]⟩
      rw [hd]
      simp only [atlasGamma,if_neg (not_lt.mpr htp.le)]
      rw [boundaryTau,if_neg hvnot,tanB,unitDir,hn,neg_smul,smul_smul,mul_inv_cancel₀ (hr 1).ne',one_smul]
  have hsource : (atlasSourceMu C).map (atlasGamma C) = boundaryMu D := by
    rw [HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_endpoint_native_source_map C hE hr hT0 hT hdisjoint,
      hparts0,hparts1,← Set.union_sdiff_distrib]
    unfold boundaryMu
    letI : NullSingletonClass arcMeasure := by
      unfold arcMeasure
      exact Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
    have hae : ∀ᵐ z ∂arcMeasure, z ∉ F := by
      rw [ae_iff]
      simpa using hF.measure_zero arcMeasure
    apply Measure.restrict_congr_set
    filter_upwards [hae] with z hz
    apply propext
    change z ∈ (arcA D ∪ arcB D) \ F ↔ z ∈ arcA D ∪ arcB D
    simp [hz]
  refine ⟨C,⟨hE,hr,hT0,hT,hunit,hinj,htangent,hsource,?_⟩⟩
  refine ⟨F,hF,?_⟩
  rw [himage,hparts0,hparts1,← Set.union_sdiff_distrib,← hfront]

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_source_atlas
