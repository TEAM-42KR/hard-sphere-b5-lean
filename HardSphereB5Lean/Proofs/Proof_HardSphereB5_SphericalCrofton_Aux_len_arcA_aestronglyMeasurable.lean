import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 800000
set_option autoImplicit false
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

private theorem SphereGeom.arcMeasure_restrict_circle (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
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

open MeasureTheory Real SphereGeom
set_option maxHeartbeats 800000

private theorem SphereGeom.Aux.sphere_slice_circle_image (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (z : ℝ) (hz : |z| < 1) :
    {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = z} =
      circlePt (z • E 2) (E 0) (E 1) (Real.sqrt (1 - z ^ 2)) ''
        Set.Icc (0 : ℝ) (2 * Real.pi) := by
  classical
  let B : OrthonormalBasis (Fin 3) ℝ E3 :=
    OrthonormalBasis.mk hE
      (hE.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge
  have hsq (v : E3) :
      (inner ℝ (E 0) v) ^ 2 + (inner ℝ (E 1) v) ^ 2 +
        (inner ℝ (E 2) v) ^ 2 = ‖v‖ ^ 2 := by
    simpa [B, Fin.sum_univ_succ, real_inner_comm, pow_two,
      real_inner_self_eq_norm_sq, add_assoc] using B.sum_inner_mul_inner v v
  have hrep (v : E3) :
      inner ℝ (E 0) v • E 0 + inner ℝ (E 1) v • E 1 +
        inner ℝ (E 2) v • E 2 = v := by
    simpa [B, Fin.sum_univ_succ, add_assoc] using B.sum_repr' v
  have hEi : ∀ i j, inner ℝ (E i) (E j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp hE
  have hz2 : z ^ 2 < 1 := by
    have hz' := abs_lt.mp hz
    nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1)]
  let r : ℝ := Real.sqrt (1 - z ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
  ext u
  constructor
  · rintro ⟨hun, huz⟩
    let a : ℝ := inner ℝ (E 0) u
    let b : ℝ := inner ℝ (E 1) u
    have hab : a ^ 2 + b ^ 2 = r ^ 2 := by
      have hu := hsq u
      rw [hun, huz] at hu
      dsimp [a, b]
      nlinarith
    let x : ℝ := a / r
    let y : ℝ := b / r
    have hxy : x ^ 2 + y ^ 2 = 1 := by
      dsimp [x, y]
      field_simp
      nlinarith
    have hx : -1 ≤ x ∧ x ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg y, sq_nonneg (x - 1), sq_nonneg (x + 1)]
    have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
    have hs2 : Real.sin (Real.arccos x) ^ 2 = y ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.arccos x)]
    have hs0 : 0 ≤ Real.sin (Real.arccos x) := by
      rw [Real.sin_arccos]
      exact Real.sqrt_nonneg _
    have ha : r * x = a := by dsimp [x]; field_simp
    have hb : r * y = b := by dsimp [y]; field_simp
    have hpoint (t : ℝ) (hct : Real.cos t = x) (hst : Real.sin t = y) :
        circlePt (z • E 2) (E 0) (E 1) r t = u := by
      rw [circlePt, hct, hst, smul_add, smul_smul, smul_smul, ha, hb]
      rw [← huz]
      simpa [add_comm, add_left_comm, add_assoc, a, b] using hrep u
    by_cases hy : 0 ≤ y
    · have hs : Real.sin (Real.arccos x) = y := by nlinarith
      refine ⟨Real.arccos x, ⟨Real.arccos_nonneg x, ?_⟩, hpoint _ hc hs⟩
      have := Real.arccos_le_pi x
      linarith [Real.pi_pos]
    · have hs : -Real.sin (Real.arccos x) = y := by
        have hy' : y < 0 := lt_of_not_ge hy
        nlinarith
      refine ⟨2 * Real.pi - Real.arccos x, ⟨?_, ?_⟩, ?_⟩
      · linarith [Real.arccos_le_pi x, Real.pi_pos]
      · linarith [Real.arccos_nonneg x]
      · apply hpoint
        · simpa only [Real.cos_two_pi_sub] using hc
        · simpa only [Real.sin_two_pi_sub] using hs
  · rintro ⟨t, ht, rfl⟩
    have h0 : inner ℝ (E 0) (circlePt (z • E 2) (E 0) (E 1) r t) =
        r * Real.cos t := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    have h1 : inner ℝ (E 1) (circlePt (z • E 2) (E 0) (E 1) r t) =
        r * Real.sin t := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    have h2 : inner ℝ (E 2) (circlePt (z • E 2) (E 0) (E 1) r t) = z := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    refine ⟨?_, h2⟩
    have hu := hsq (circlePt (z • E 2) (E 0) (E 1) r t)
    rw [h0, h1, h2] at hu
    have hn : 0 ≤ ‖circlePt (z • E 2) (E 0) (E 1) r t‖ := norm_nonneg _
    nlinarith [Real.sin_sq_add_cos_sq t]

open MeasureTheory Real SphereGeom
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000

private theorem SphereGeom.Aux.pair_arc_subset_circle_pullback (c : E3) (E : Fin 2 → E3) (hE : Orthonormal ℝ E) (r : ℝ) (hr : 0 < r)
    (A : Set E3) (hA : MeasurableSet A)
    (hsub : A ⊆ circlePt c (E 0) (E 1) r '' Set.Icc (0 : ℝ) (2 * π))
    (g : E3 × E3 → ℝ) (hg : Measurable g) :
    (∫ u in A, ∫ v in A, g (u, v) ∂arcMeasure ∂arcMeasure) = r ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
        if circlePt c (E 0) (E 1) r t ∈ A ∧ circlePt c (E 0) (E 1) r s ∈ A
        then g (circlePt c (E 0) (E 1) r t, circlePt c (E 0) (E 1) r s) else 0 := by
  let I : Set ℝ := Set.Icc 0 (2 * π)
  let γ : ℝ → E3 := circlePt c (E 0) (E 1) r
  have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
  have hm : arcMeasure.restrict (γ '' I) =
      ENNReal.ofReal r • (volume.restrict I).map γ :=
    SphereGeom.arcMeasure_restrict_circle c E hE r hr 0 (2 * π)
      (by positivity) (by simp)
  have one (k : E3 → ℝ) (hk : Measurable k) :
      (∫ u in A, k u ∂arcMeasure) = r * ∫ t in I, A.indicator k (γ t) := by
    calc
      (∫ u in A, k u ∂arcMeasure) = ∫ u in A, k u ∂(arcMeasure.restrict (γ '' I)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = ∫ u, A.indicator k u ∂(arcMeasure.restrict (γ '' I)) := (integral_indicator hA).symm
      _ = r * ∫ t in I, A.indicator k (γ t) := by
        rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hr.le, smul_eq_mul,
          integral_map_of_stronglyMeasurable hγ (hk.stronglyMeasurable.indicator hA)]
  let Q : E3 → ℝ := fun u => ∫ s in I, A.indicator (fun v => g (u, v)) (γ s)
  have hQI : Measurable (fun z : E3 × ℝ => A.indicator (fun v => g (z.1, v)) (γ z.2)) := by
    apply (hg.comp (measurable_fst.prodMk (hγ.comp measurable_snd))).ite
      (hA.preimage (hγ.comp measurable_snd)) measurable_const
  have hQ : Measurable Q := hQI.stronglyMeasurable.integral_prod_right'.measurable
  have hinner (u : E3) : (∫ v in A, g (u, v) ∂arcMeasure) = r * Q u :=
    one _ (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  rw [integral_const_mul, one Q hQ]
  have hind (t : ℝ) : A.indicator Q (γ t) =
      ∫ s in I, if γ t ∈ A ∧ γ s ∈ A then g (γ t, γ s) else 0 := by
    by_cases ht : γ t ∈ A <;> simp [Q, Set.indicator, ht]
  simp_rw [hind]
  dsimp [I, γ]
  ring

set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
private theorem SphereGeom.exists_measurable_frame : ∃ F₁ F₂ : E3 → E3, Measurable F₁ ∧ Measurable F₂ ∧
    ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p] := by
  let r : E3 → ℝ := fun p => Real.sqrt (p 0 ^ 2 + p 1 ^ 2)
  let F₁ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![1,0,0]
    else WithLp.toLp 2 ![-p 1 / r p, p 0 / r p, 0]
  let F₂ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![0,1,0]
    else WithLp.toLp 2 ![-p 2 * p 0 / r p, -p 2 * p 1 / r p, r p]
  have hm : Measurable (fun p : E3 => p 0 ^ 2 + p 1 ^ 2) := by fun_prop
  have mr : Measurable r := by dsimp [r]; fun_prop
  have hms : MeasurableSet {p : E3 | p 0 ^ 2 + p 1 ^ 2 = 0} := hm (measurableSet_singleton 0)
  refine ⟨F₁, F₂, ?_, ?_, ?_⟩
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · intro p hp
    have hp2 : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hp, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq p).symm
    have hr2 : r p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt (by positivity)
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    by_cases h : p 0 ^ 2 + p 1 ^ 2 = 0
    · have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h2 : p 2 ^ 2 = 1 := by nlinarith
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ, h0, h1, ← sq, h2]
    · have hr0 : r p ≠ 0 := by intro hh; rw [hh] at hr2; simp at hr2; exact h hr2.symm
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ]
      all_goals field_simp [hr0]
      all_goals nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2),
        congrArg (fun a : ℝ => p 2 * a) hr2]

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.cross_joint_continuous : Continuous (fun z : Pt × Pt => cross z.1 z.2) := by
  unfold cross crossProduct
  fun_prop

private theorem HardSphereB5.SphericalCrofton.Aux.tanA_joint_measurable : Measurable (fun z : Pt × Pt => tanA z.1 z.2) := by
  unfold tanA unitDir nAv cross crossProduct
  fun_prop

private theorem HardSphereB5.SphericalCrofton.Aux.arcA_joint_measurableSet : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} := by
  have heq : {z : Pt × Pt | z.2 ∈ arcA z.1} =
      {z : Pt × Pt | z.1 ≠ 0 ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
        dist (z.1 + z.2) e ≤ 1 ∧ ‖z.1 + z.2‖ = 1} := by
    ext z
    by_cases h : z.1 = 0 <;> simp [arcA, SigmaD, LamC, h, and_assoc]
  rw [heq]
  measurability

private theorem HardSphereB5.SphericalCrofton.Aux.phiK_measurable (f : Kern) : Measurable (phiK f) := by
  cases f <;> unfold phiK <;> fun_prop

private theorem HardSphereB5.SphericalCrofton.Aux.cutKern_measurable (f : Kern) : Measurable (cutKern f) := by
  exact (HardSphereB5.SphericalCrofton.Aux.phiK_measurable f).ite (measurableSet_lt measurable_id measurable_const) measurable_const

private theorem HardSphereB5.SphericalCrofton.Aux.AA_joint_kernel_measurable (f : Kern) : Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcA z.1 then
        cutKern f (arccos (inner ℝ z.2.1 z.2.2)) *
          santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanA z.1 z.2.2)
      else 0) := by
  have h1 : Measurable (fun z : Pt × (Pt × Pt) => tanA z.1 z.2.1) := by
    unfold tanA unitDir nAv cross crossProduct
    fun_prop
  have h2 : Measurable (fun z : Pt × (Pt × Pt) => tanA z.1 z.2.2) := by
    unfold tanA unitDir nAv cross crossProduct
    fun_prop
  have hc : Measurable (fun z : Pt × (Pt × Pt) => cross z.2.1 z.2.2) := by
    unfold cross crossProduct
    fun_prop
  have ha : Measurable (fun z : Pt × (Pt × Pt) => arccos (inner ℝ z.2.1 z.2.2)) := by
    exact continuous_arccos.measurable.comp (measurable_snd.fst.inner measurable_snd.snd)
  have hk := (HardSphereB5.SphericalCrofton.Aux.cutKern_measurable f).comp ha
  have hd : Measurable (fun z : Pt × (Pt × Pt) =>
      santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanA z.1 z.2.2)) := by
    exact (((hc.inner h1).abs.mul (hc.inner h2).abs).div
      ((continuous_sin.measurable.comp ha).pow_const 3))
  exact (hk.mul hd).ite
    ((HardSphereB5.SphericalCrofton.Aux.arcA_joint_measurableSet.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (HardSphereB5.SphericalCrofton.Aux.arcA_joint_measurableSet.preimage (measurable_fst.prodMk measurable_snd.snd))) measurable_const

 theorem HardSphereB5.SphericalCrofton.Aux.AA_chart_stronglyMeasurable (f : Kern) (p : Pt × ℝ → Pt) (hp : Measurable p)
    (r : Pt → ℝ) (hr : Measurable r) : StronglyMeasurable
    (fun D : Pt => (1 / 2 : ℝ) * (r D) ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
        if p (D, t) ∈ arcA D ∧ p (D, s) ∈ arcA D then
          cutKern f (arccos (inner ℝ (p (D, t)) (p (D, s)))) *
            santaloDens (p (D, t)) (p (D, s)) (tanA D (p (D, t))) (tanA D (p (D, s)))
        else 0) := by
  let H : (Pt × ℝ) × ℝ → ℝ := fun z =>
    if p (z.1.1, z.1.2) ∈ arcA z.1.1 ∧ p (z.1.1, z.2) ∈ arcA z.1.1 then
      cutKern f (arccos (inner ℝ (p (z.1.1, z.1.2)) (p (z.1.1, z.2)))) *
        santaloDens (p (z.1.1, z.1.2)) (p (z.1.1, z.2))
          (tanA z.1.1 (p (z.1.1, z.1.2))) (tanA z.1.1 (p (z.1.1, z.2))) else 0
  have hmap : Measurable (fun z : (Pt × ℝ) × ℝ =>
      (z.1.1, (p (z.1.1, z.1.2), p (z.1.1, z.2)))) := by
    exact measurable_fst.fst.prodMk
      ((hp.comp measurable_fst).prodMk (hp.comp (measurable_fst.fst.prodMk measurable_snd)))
  have hH : Measurable H := (HardSphereB5.SphericalCrofton.Aux.AA_joint_kernel_measurable f).comp hmap
  have hinner : StronglyMeasurable (fun z : Pt × ℝ =>
      ∫ s in Set.Icc (0 : ℝ) (2 * π), H (z, s)) := hH.stronglyMeasurable.integral_prod_right'
  have houter : StronglyMeasurable (fun D : Pt =>
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), H ((D, t), s)) :=
    hinner.integral_prod_right'
  exact ((stronglyMeasurable_const.mul (hr.pow_const 2).stronglyMeasurable).mul houter)

open HardSphereB5.SphericalCrofton.Aux

private theorem HardSphereB5.SphericalCrofton.Aux.AA_circle_chart_formula (f : Kern) (D : Pt) (hD : D ∈ LamC) (h0 : D ≠ 0) (E : Fin 3 → Pt) (hE : Orthonormal ℝ E) (hn : E 2 = nAv D) : AAf f D = (1 / 2 : ℝ) * (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) ^ 2 * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), if circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t ∈ arcA D ∧ circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s ∈ arcA D then cutKern f (arccos (inner ℝ (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s))) * santaloDens (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t)) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s)) else 0  := by
  let r : ℝ := Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let γ : ℝ → Pt := circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) r
  have ha : ‖D‖ ≤ 1 := by
    have hd0 := hD.1
    simpa only [Metric.mem_closedBall, dist_zero_right] using hd0
  have hane : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg D])
  have hz : |‖D‖ / 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hcenter : (‖D‖ / 2) • E 2 = (-(1 / 2 : ℝ)) • D := by
    rw [hn, nAv, smul_smul, smul_neg]
    rw [neg_smul]
    congr 1
    field_simp
  have hrEq : Real.sqrt (1 - (‖D‖ / 2) ^ 2) = r := by
    dsimp [r]
    congr 1
    ring
  have hsub : arcA D ⊆ γ '' Set.Icc (0 : ℝ) (2 * π) := by
    intro u hu
    simp only [arcA, if_neg h0, Set.mem_setOf_eq, SigmaD] at hu
    have hdinner : inner ℝ D u = -‖D‖ ^ 2 / 2 := by
      have hsum := norm_add_sq_real D u
      rw [hu.2, hu.1.1] at hsum
      nlinarith
    have hninner : inner ℝ (E 2) u = ‖D‖ / 2 := by
      rw [hn, nAv, real_inner_smul_left, inner_neg_left, hdinner]
      field_simp
    have hum : u ∈ {u : Pt | ‖u‖ = 1 ∧ inner ℝ (E 2) u = ‖D‖ / 2} := ⟨hu.1.1, hninner⟩
    rw [SphereGeom.Aux.sphere_slice_circle_image E hE (‖D‖ / 2) hz] at hum
    simpa only [hcenter, hrEq] using hum
  have hE2 : Orthonormal ℝ ![E 0, E 1] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (1 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (1 : Fin 3)
  have hA : MeasurableSet (arcA D) :=
    HardSphereB5.SphericalCrofton.Aux.arcA_joint_measurableSet.preimage (show Measurable (fun u : Pt => (D, u)) from
      measurable_const.prodMk measurable_id)
  let g : Pt × Pt → ℝ := fun uv =>
    if uv.1 ∈ arcA D ∧ uv.2 ∈ arcA D then
      cutKern f (arccos (inner ℝ uv.1 uv.2)) *
        santaloDens uv.1 uv.2 (tanA D uv.1) (tanA D uv.2) else 0
  have hg : Measurable g := (HardSphereB5.SphericalCrofton.Aux.AA_joint_kernel_measurable f).comp
    (show Measurable (fun uv : Pt × Pt => (D, uv)) from measurable_const.prodMk measurable_id)
  have hmasked : AAf f D = (1 / 2 : ℝ) * ∫ u in arcA D, ∫ v in arcA D, g (u,v) ∂arcMeasure ∂arcMeasure := by
    unfold AAf
    congr 1
    apply setIntegral_congr_fun hA
    intro u hu
    apply setIntegral_congr_fun hA
    intro v hv
    simp [g, hu, hv]
  rw [hmasked, SphereGeom.Aux.pair_arc_subset_circle_pullback
    ((-(1 / 2 : ℝ)) • D) ![E 0, E 1] hE2 r hr (arcA D) hA hsub g hg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← mul_assoc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only [g]
  split_ifs <;> rfl

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000

private theorem HardSphereB5.SphericalCrofton.Aux.AAf_aestronglyMeasurable (f : Kern) : AEStronglyMeasurable (AAf f) (volume.restrict LamC) := by
  obtain ⟨F1, F2, hF1, hF2, hF⟩ := SphereGeom.exists_measurable_frame
  let r : Pt → ℝ := fun D => Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let p : Pt × ℝ → Pt := fun z =>
    circlePt ((-(1 / 2 : ℝ)) • z.1) (F1 (nAv z.1)) (F2 (nAv z.1)) (r z.1) z.2
  have hnmeas : Measurable nAv := by unfold nAv; fun_prop
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hp : Measurable p := by dsimp [p]; unfold circlePt; fun_prop
  let G : Pt → ℝ := fun D => (1 / 2 : ℝ) * (r D) ^ 2 *
    ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
      if p (D, t) ∈ arcA D ∧ p (D, s) ∈ arcA D then
        cutKern f (arccos (inner ℝ (p (D, t)) (p (D, s)))) *
          santaloDens (p (D, t)) (p (D, s)) (tanA D (p (D, t))) (tanA D (p (D, s))) else 0
  have hG : StronglyMeasurable G := HardSphereB5.SphericalCrofton.Aux.AA_chart_stronglyMeasurable f p hp r hr
  apply hG.aestronglyMeasurable.congr
  have hLam : MeasurableSet LamC := by
    exact measurableSet_closedBall.inter measurableSet_closedBall
  filter_upwards [ae_restrict_mem hLam] with D hD
  by_cases h0 : D = 0
  · subst D
    simp [G, AAf, arcA]
  · have hn : ‖nAv D‖ = 1 := by
      simp [nAv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg D),
        norm_ne_zero_iff.mpr h0, inv_mul_cancel₀]
    simpa [G, p, r] using
      (AA_circle_chart_formula f D hD h0 ![F1 (nAv D), F2 (nAv D), nAv D] (hF _ hn) rfl).symm

private theorem SphereGeom.Aux.contact_small_circle_subset (q : E3) (hbound : ‖q‖ ≤ 1)
(h0 : q ≠ 0) (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (hn : E 2 = ‖q‖⁻¹ • (-q)) :
{u : E3 | ‖u‖ = 1 ∧ ‖q + u‖ = 1} ⊆
circlePt ((-(1 / 2 : ℝ)) • q) (E 0) (E 1) (Real.sqrt (1 - ‖q‖ ^ 2 / 4)) ''
Set.Icc (0 : ℝ) (2 * π)  := by
  have hane : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hz : |‖q‖ / 2| < 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hcenter : (‖q‖ / 2) • E 2 = (-(1 / 2 : ℝ)) • q := by
    rw [hn, smul_smul, smul_neg, neg_smul]
    congr 1
    field_simp
  have hrEq : Real.sqrt (1 - (‖q‖ / 2) ^ 2) = Real.sqrt (1 - ‖q‖ ^ 2 / 4) := by
    congr 1
    ring
  intro u hu
  have hdinner : inner ℝ q u = -‖q‖ ^ 2 / 2 := by
    have hsum := norm_add_sq_real q u
    rw [hu.2, hu.1] at hsum
    nlinarith
  have hninner : inner ℝ (E 2) u = ‖q‖ / 2 := by
    rw [hn, real_inner_smul_left, inner_neg_left, hdinner]
    field_simp
  have hum : u ∈ {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = ‖q‖ / 2} := ⟨hu.1, hninner⟩
  rw [SphereGeom.Aux.sphere_slice_circle_image E hE (‖q‖ / 2) hz] at hum
  simpa only [hcenter, hrEq] using hum

theorem proof_HardSphereB5_SphericalCrofton_Aux_len_arcA_aestronglyMeasurable : AEStronglyMeasurable (fun D : Pt => len (arcA D))
    (volume.restrict LamC) := by
  have one (q : Pt) (hq : ‖q‖ ≤ 1) (hq0 : q ≠ 0)
      (E : Fin 3 → Pt) (hE : Orthonormal ℝ E) (hn : E 2 = ‖q‖⁻¹ • (-q))
      (A : Set Pt) (hA : MeasurableSet A)
      (hcontact : A ⊆ {u : Pt | ‖u‖ = 1 ∧ ‖q + u‖ = 1}) :
      len A = Real.sqrt (1 - ‖q‖ ^ 2 / 4) *
        ∫ t in Set.Icc (0 : ℝ) (2 * π),
          if circlePt ((-(1 / 2 : ℝ)) • q) (E 0) (E 1)
              (Real.sqrt (1 - ‖q‖ ^ 2 / 4)) t ∈ A then (1 : ℝ) else 0 := by
    let r : ℝ := Real.sqrt (1 - ‖q‖ ^ 2 / 4)
    let I : Set ℝ := Set.Icc 0 (2 * π)
    let γ : ℝ → Pt := circlePt ((-(1 / 2 : ℝ)) • q) (E 0) (E 1) r
    have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg q])
    have hsub : A ⊆ γ '' I :=
      hcontact.trans (SphereGeom.Aux.contact_small_circle_subset q hq hq0 E hE hn)
    have hE2 : Orthonormal ℝ ![E 0, E 1] := by
      apply orthonormal_iff_ite.mpr
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (0 : Fin 3)
      · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (1 : Fin 3)
      · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (0 : Fin 3)
      · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (1 : Fin 3)
    have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
    have hm : arcMeasure.restrict (γ '' I) =
        ENNReal.ofReal r • (volume.restrict I).map γ :=
      SphereGeom.arcMeasure_restrict_circle ((-(1 / 2 : ℝ)) • q) ![E 0, E 1]
        hE2 r hr 0 (2 * π) (by positivity) (by simp)
    calc
      len A = ∫ u in A, (1 : ℝ) ∂arcMeasure := by
        simp [len, Measure.real]
      _ = ∫ u in A, (1 : ℝ) ∂(arcMeasure.restrict (γ '' I)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂(arcMeasure.restrict (γ '' I)) :=
        (integral_indicator hA).symm
      _ = r * ∫ t in I, A.indicator (fun _ => (1 : ℝ)) (γ t) := by
        rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hr.le, smul_eq_mul,
          integral_map_of_stronglyMeasurable hγ (stronglyMeasurable_const.indicator hA)]
      _ = _ := by simp only [Set.indicator, γ, I, r]
  have hArc : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} :=
    HardSphereB5.SphericalCrofton.Aux.arcA_joint_measurableSet
  obtain ⟨F1, F2, hF1, hF2, hF⟩ := SphereGeom.exists_measurable_frame
  let r : Pt → ℝ := fun D => Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let p : Pt × ℝ → Pt := fun z =>
    circlePt ((-(1 / 2 : ℝ)) • z.1) (F1 (nAv z.1)) (F2 (nAv z.1)) (r z.1) z.2
  have hnmeas : Measurable nAv := by unfold nAv; fun_prop
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hp : Measurable p := by dsimp [p]; unfold circlePt; fun_prop
  let H : Pt × ℝ → ℝ := fun z => if p z ∈ arcA z.1 then 1 else 0
  have hH : Measurable H := measurable_const.ite
    (hArc.preimage (measurable_fst.prodMk hp)) measurable_const
  let G : Pt → ℝ := fun D => r D * ∫ t in Set.Icc (0 : ℝ) (2 * π), H (D, t)
  have hG : StronglyMeasurable G := hr.stronglyMeasurable.mul
    hH.stronglyMeasurable.integral_prod_right'
  apply hG.aestronglyMeasurable.congr
  have hLam : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
  filter_upwards [ae_restrict_mem hLam] with D hD
  by_cases h0 : D = 0
  · subst D
    simp [G, H, arcA, len]
  · have hn : ‖nAv D‖ = 1 := by
      simp [nAv, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg D), norm_ne_zero_iff.mpr h0, inv_mul_cancel₀]
    let E : Fin 3 → Pt := ![F1 (nAv D), F2 (nAv D), nAv D]
    have hE : Orthonormal ℝ E := hF _ hn
    have hA : MeasurableSet (arcA D) :=
      hArc.preimage (measurable_const.prodMk measurable_id)
    have hq : ‖D‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hD.1
    have hcontact : arcA D ⊆ {u : Pt | ‖u‖ = 1 ∧ ‖D + u‖ = 1} := by
      intro u hu
      simp only [arcA, if_neg h0, Set.mem_setOf_eq, SigmaD] at hu
      refine ⟨hu.1.1, ?_⟩
      exact hu.2
    have hnE : E 2 = ‖D‖⁻¹ • (-D) := by
      rfl
    have heq := one D hq h0 E hE hnE (arcA D) hA hcontact
    simpa [G, H, p, r, E] using heq.symm
