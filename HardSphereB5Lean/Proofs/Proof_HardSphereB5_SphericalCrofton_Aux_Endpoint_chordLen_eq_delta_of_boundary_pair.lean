import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import Mathlib
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

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
open MeasureTheory SphereGeom

private theorem SphereGeom.arcMeasure_circle_arc (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hab : a ≤ b) (hb : b - a ≤ 2 * Real.pi) :
    arcMeasure (circlePt c (e 0) (e 1) r '' Set.Icc a b) = ENNReal.ofReal (r * (b - a)) := by
  have hc : Continuous (circlePt c (e 0) (e 1) r) := by
    unfold circlePt
    fun_prop
  have hm := congrArg (fun μ : Measure E3 => μ Set.univ)
    (SphereGeom.Aux.ArcLength.restrict_circle_arc_eq_map c e he r hr a b hab hb)
  simpa [Measure.map_apply hc.measurable, Real.volume_Icc, ENNReal.ofReal_mul hr.le] using hm
private theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.chordLen_eq_delta_of_short_arc (K : Set Pt) (p u v E1 E2 : Pt) (a b : ℝ)
    (hE : Orthonormal ℝ ![E1,E2,p]) (hab : a < b) (hπ : b - a ≤ π)
    (huv : u ≠ v)
    (hgeom : greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b)
    (hends : ({circlePt 0 E1 E2 1 a, circlePt 0 E1 E2 1 b} : Set Pt) = {u,v}) :
    0 < arccos (inner ℝ u v) ∧ chordLen K (greatCircle p) = arccos (inner ℝ u v) := by
  let C : ℝ → Pt := circlePt 0 E1 E2 1
  have h00 : inner ℝ E1 E1 = 1 := by
    simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by
    simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by
    simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by
    simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have he2 : Orthonormal ℝ ![E1,E2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hinner (s t : ℝ) : inner ℝ (C s) (C t) = Real.cos (s - t) := by
    simp only [C, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h00, h01, h10, h11,
      mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Real.cos_sub]
    ring
  have humem : u ∈ ({C a,C b} : Set Pt) := by
    rw [show ({C a,C b} : Set Pt) = {u,v} from hends]
    simp
  have hvmem : v ∈ ({C a,C b} : Set Pt) := by
    rw [show ({C a,C b} : Set Pt) = {u,v} from hends]
    simp
  have hordered : (u = C a ∧ v = C b) ∨ (u = C b ∧ v = C a) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at humem hvmem
    rcases humem with hu | hu <;> rcases hvmem with hv | hv
    · exact False.elim (huv (hu.trans hv.symm))
    · exact Or.inl ⟨hu,hv⟩
    · exact Or.inr ⟨hu,hv⟩
    · exact False.elim (huv (hu.trans hv.symm))
  have huvinner : inner ℝ u v = Real.cos (b - a) := by
    rcases hordered with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · rw [hu,hv,hinner]
      rw [show a - b = -(b - a) by ring, Real.cos_neg]
    · rw [hu,hv,hinner]
  have hdelta : arccos (inner ℝ u v) = b - a := by
    rw [huvinner]
    exact Real.arccos_cos (sub_nonneg.mpr hab.le) hπ
  have hlen : chordLen K (greatCircle p) = b - a := by
    unfold chordLen len
    rw [hgeom]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num)
      a b hab.le (by linarith [Real.pi_pos])
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] using congrArg ENNReal.toReal hm
  rw [hdelta]
  exact ⟨sub_pos.mpr hab, hlen⟩

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Set NormedSpace

private theorem HardSphereB5.SphericalCrofton.Aux.HitMass.regular_cone_geometry (K : Set Pt) (hK : IsRegularRegionCrofton K) :
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
    IsClosed C ∧ Convex ℝ C ∧ (∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C) ∧
      (interior C).Nonempty ∧
      (∀ u : Pt, ‖u‖ = 1 → (u ∈ frontier C ↔ u ∈ sFrontier K)) := by
  classical
  have htransport :
      let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
      ∀ u : Pt, ‖u‖ = 1 → (u ∈ interior C ↔ u ∈ sInterior K) := by
    classical
    dsimp only
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
    let P : Set Pt := {v | v ≠ 0}
    let f : Pt → Pt := fun v => ‖v‖⁻¹ • v
    have hP : IsOpen P := isClosed_singleton.isOpen_compl
    have hfnorm (v : Pt) (hv : v ≠ 0) : ‖f v‖ = 1 := by
      have hvp := norm_pos_iff.mpr hv
      simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]
    let T : Set (Metric.sphere (0 : Pt) 1) := Subtype.val ⁻¹' K
    have hsC : ∀ z : Metric.sphere (0 : Pt) 1, (z : Pt) ∈ C ↔ (z : Pt) ∈ K := by
      intro z
      have hznorm : ‖(z : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using z.property
      have hz0 : (z : Pt) ≠ 0 := by intro hh; simp [hh] at hznorm
      simp [C, hznorm, hz0]
    intro u hu
    have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
    let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
    constructor
    · intro huC
      have hO : IsOpen ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C) :=
        isOpen_interior.preimage continuous_subtype_val
      have hOT : (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C ⊆ T := by
        intro z hz
        exact (hsC z).mp (interior_subset hz)
      refine ⟨us, interior_mono hOT ?_, rfl⟩
      rw [hO.interior_eq]
      exact huC
    · rintro ⟨z, hz, hzu⟩
      have hNmap : Continuous (fun v : P => f (v : Pt)) :=
        (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val
      let fs : P → Metric.sphere (0 : Pt) 1 := fun v =>
        ⟨f v, by simpa [Metric.mem_sphere, dist_zero_right] using hfnorm v v.property⟩
      have hfs : Continuous fs := hNmap.subtype_mk _
      let up : P := ⟨u, hu0⟩
      have hfup : fs up = z := by
        apply Subtype.ext
        change f u = (z : Pt)
        simp [f, hu, hzu]
      let W := fs ⁻¹' interior T
      have hW : IsOpen W := hfs.isOpen_preimage _ isOpen_interior
      have huW : up ∈ W := by change fs up ∈ interior T; rw [hfup]; exact hz
      have hO : IsOpen ((Subtype.val : P → Pt) '' W) := hP.isOpenMap_subtype_val _ hW
      have hOC : ((Subtype.val : P → Pt) '' W) ⊆ C := by
        rintro v ⟨vp, hvp, rfl⟩
        have hvpre : fs vp ∈ T := interior_subset hvp
        exact Or.inr hvpre
      apply interior_mono hOC
      rw [hO.interior_eq]
      exact ⟨up, huW, rfl⟩
  dsimp only
  let C : Set Pt := {v | v = 0 ∨ normalize v ∈ K}
  have hzero : (0 : Pt) ∈ C := Or.inl rfl
  have hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C := by
    intro r hr v hv
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · subst r
      simpa using hzero
    · rcases hv with hv0 | hvK
      · simp [hv0, C]
      · exact Or.inr (by rwa [normalize_smul_of_pos hrpos])
  have hunit : ∀ u : Pt, ‖u‖ = 1 → (u ∈ C ↔ u ∈ K) := by
    intro u hu
    have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
    simp [C, hu0, normalize_eq_self_of_norm_eq_one hu]
  have hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
    intro x hx y hy
    by_cases hx0 : x = 0
    · simpa [hx0] using hy
    by_cases hy0 : y = 0
    · simpa [hy0] using hx
    have hxK : normalize x ∈ K := hx.resolve_left hx0
    have hyK : normalize y ∈ K := hy.resolve_left hy0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let u := normalize x
    let v := normalize y
    have hxu : ‖x‖ • u = x := norm_smul_normalize x
    have hyv : ‖y‖ • v = y := norm_smul_normalize y
    have huC : u ∈ C := (hunit u (norm_normalize hx0)).mpr hxK
    have hvC : v ∈ C := (hunit v (norm_normalize hy0)).mpr hyK
    by_cases huv : u = -v
    · have hvu : v = -u := by rw [huv]; simp
      by_cases hnorm : ‖y‖ ≤ ‖x‖
      · have heq : x + y = (‖x‖ - ‖y‖) • u := by
          calc
            x + y = ‖x‖ • u + ‖y‖ • v := congrArg₂ (· + ·) hxu.symm hyv.symm
            _ = (‖x‖ - ‖y‖) • u := by rw [hvu, smul_neg, sub_smul, sub_eq_add_neg]
        rw [heq]
        exact hscale (‖x‖ - ‖y‖) (sub_nonneg.mpr hnorm) u huC
      · have heq : x + y = (‖y‖ - ‖x‖) • v := by
          calc
            x + y = ‖x‖ • u + ‖y‖ • v := congrArg₂ (· + ·) hxu.symm hyv.symm
            _ = (‖y‖ - ‖x‖) • v := by rw [huv, smul_neg, sub_smul, sub_eq_add_neg]; abel
        rw [heq]
        exact hscale (‖y‖ - ‖x‖) (by linarith) v hvC
    · let d : ℝ := ‖x‖ + ‖y‖
      let t : ℝ := ‖y‖ / d
      have hd : 0 < d := by dsimp [d]; linarith
      have ht0 : 0 ≤ t := div_nonneg hypos.le hd.le
      have ht1 : t ≤ 1 := (div_le_one hd).mpr (by dsimp [d]; linarith)
      have hgc : normalize ((1 - t) • u + t • v) ∈ K :=
        hK.geodesically_convex u hxK v hyK huv t ⟨ht0, ht1⟩
      have hdt : d * t = ‖y‖ := by dsimp [t]; field_simp
      have hdone : d * (1 - t) = ‖x‖ := by dsimp [d] at *; nlinarith [hdt]
      have heq : x + y = d • ((1 - t) • u + t • v) := by
        rw [smul_add, smul_smul, smul_smul, hdone, hdt, hxu, hyv]
      exact Or.inr (by rw [heq, normalize_smul_of_pos hd]; exact hgc)
  have hconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    exact hadd (a • x) (hscale a ha x hx) (b • y) (hscale b hb y hy)
  let P : Set Pt := {v | v ≠ 0}
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  have hf : ContinuousOn (normalize : Pt → Pt) P := by
    intro v hv
    exact ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul
      continuous_id.continuousAt).continuousWithinAt
  have hCclosed : IsClosed C := by
    have hO := hf.isOpen_inter_preimage hP hK.isCompact.isClosed.isOpen_compl
    have heq : Cᶜ = P ∩ normalize ⁻¹' Kᶜ := by
      ext v
      simp [C, P, not_or]
    rw [← isOpen_compl_iff, heq]
    exact hO
  have hint : (interior C).Nonempty := by
    obtain ⟨u, hu⟩ := hK.interior_nonempty
    have hunorm : ‖u‖ = 1 := by
      obtain ⟨us, hus, rfl⟩ := hu
      simpa [Metric.mem_sphere, dist_zero_right] using us.property
    refine ⟨u, ?_⟩
    exact (htransport u hunorm).mpr hu
  refine ⟨hCclosed, hconv, hscale, hint, ?_⟩
  intro u hu
  let T : Set (Metric.sphere (0 : Pt) 1) := Subtype.val ⁻¹' K
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  have hT : IsClosed T := hK.isCompact.isClosed.preimage continuous_subtype_val
  have hsfront : u ∈ sFrontier K ↔ us ∈ frontier T := by
    constructor
    · rintro ⟨z, hz, hzu⟩
      have heq : z = us := Subtype.ext hzu
      exact heq ▸ hz
    · intro hz
      exact ⟨us, hz, rfl⟩
  have hsint : u ∈ sInterior K ↔ us ∈ interior T := by
    constructor
    · rintro ⟨z, hz, hzu⟩
      have heq : z = us := Subtype.ext hzu
      exact heq ▸ hz
    · intro hz
      exact ⟨us, hz, rfl⟩
  have hi : u ∈ interior C ↔ us ∈ interior T :=
    (htransport u hu).trans hsint
  change (u ∈ frontier C ↔ u ∈ sFrontier K)
  rw [hCclosed.frontier_eq, hsfront, hT.frontier_eq]
  change (u ∈ C ∧ u ∉ interior C) ↔ ((u ∈ K) ∧ us ∉ interior T)
  rw [hunit u hu, hi]

end

section
open MeasureTheory SphereGeom
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

end

section
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

end

section
open MeasureTheory SphereGeom
set_option maxHeartbeats 800000
private theorem SphereGeom.Aux.Pair.circle_image (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p := by
  let e : Fin 3 → E3 := ![v₁, v₂, p]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb (i : Fin 3) : b i = e i := by simp [b, e]
  have hb0 : b 0 = v₁ := by simp [hb, e]
  have hb1 : b 1 = v₂ := by simp [hb, e]
  have hb2 : b 2 = p := by simp [hb, e]
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : circlePt 0 v₁ v₂ 1 t = b.repr.symm (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]) := by
        rw [← b.sum_repr_symm]
        simp [Fin.sum_univ_succ, hb0, hb1, hb2, circlePt]
      rw [hc, b.repr.symm.norm_map]
      have hs : ‖(WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)‖ ^ 2 = 1 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)]
    · have h1 : inner ℝ p v₁ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)
      have h2 : inner ℝ p v₂ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
      simp [circlePt, inner_add_right, inner_smul_right, h1, h2]
  · rintro ⟨hu, hup⟩
    have hpcoord : b.repr u 2 = 0 := by simpa [b.repr_apply_apply, hb2] using hup
    have hnorm : b.repr u 0 ^ 2 + b.repr u 1 ^ 2 = 1 := by
      have h : ‖b.repr u‖ ^ 2 = 1 := by rw [b.repr.norm_map, hu]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ, hpcoord] using h
    let z : ℂ := ⟨b.repr u 0, b.repr u 1⟩
    have hzn : ‖z‖ = 1 := by
      have h : ‖z‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]
        simpa [Complex.normSq, z, pow_two] using hnorm
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; norm_num at hzn
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have hc : Real.cos z.arg = b.repr u 0 := by simpa [Complex.cos_arg hz, hzn, z]
    have hs : Real.sin z.arg = b.repr u 1 := by simpa [Complex.sin_arg, hzn, z]
    rw [circlePt, zero_add, one_smul, hc, hs]
    have h := b.sum_repr u
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, hpcoord] using h

end

section
open MeasureTheory SphereGeom
private theorem SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    arcMeasure.restrict (greatCircle p) =
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)).map (circlePt 0 v₁ v₂ 1) := by
  have he : Orthonormal ℝ ![v₁, v₂] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have h := orthonormal_iff_ite.mp hv (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    fin_cases i <;> fin_cases j <;> simpa using h
  have hm := arcMeasure_restrict_circle (0 : E3) ![v₁, v₂] he 1 (by norm_num)
    (-Real.pi) Real.pi (by linarith [Real.pi_pos]) (by linarith)
  simpa [SphereGeom.Aux.Pair.circle_image v₁ v₂ p hv] using hm

end

section
open MeasureTheory SphereGeom Real
open scoped Classical
set_option maxHeartbeats 1200000

private theorem finite_unitCircle_line (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.Finite {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = 1 ∧ a * z.1 + b * z.2 = 0} := by
  classical
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine (Set.toFinite ({(1, 0), (-1, 0)} : Set (ℝ × ℝ))).subset ?_
    rintro ⟨x,y⟩ ⟨hn, hl⟩
    have hy : y = 0 := by simpa [ha, hb] using hl
    have hx : x ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with hx | hx
    · simp [hx, hy]
    · simp [hx, hy]
  · let P : Polynomial ℝ := Polynomial.C (a ^ 2 + b ^ 2) * Polynomial.X ^ 2 - Polynomial.C (a ^ 2)
    have hP : P ≠ 0 := by
      intro h
      have hv := congrArg (Polynomial.eval (0 : ℝ)) h
      have hsq : a ^ 2 = 0 := by simpa [P] using hv
      exact ha (sq_eq_zero_iff.mp hsq)
    apply Set.Finite.of_finite_image (f := fun z : ℝ × ℝ => z.2)
    · refine (Polynomial.finite_setOf_isRoot hP).subset ?_
      rintro y ⟨⟨x,y⟩, ⟨hn,hl⟩, rfl⟩
      change P.eval y = 0
      simp only [P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hs : (a * x) ^ 2 = (b * y) ^ 2 := by
        have hh : a * x = -(b * y) := by linarith
        rw [hh]
        ring
      have ht := congrArg (fun q : ℝ => a ^ 2 * q) hn
      nlinarith [hs, ht]
    · rintro ⟨x,y⟩ ⟨hn,hl⟩ ⟨x',y'⟩ ⟨hn',hl'⟩ hyy
      change y = y' at hyy
      have hxx : x = x' := by
        apply (mul_left_cancel₀ ha)
        simp only [Prod.fst, Prod.snd] at hl hl'
        rw [hyy] at hl
        linarith
      exact Prod.ext hxx hyy

private theorem SphereGeom.Aux.Chord.arcMeasure_greatCircle_closedHemisphere (n p : E3) (hn : ‖n‖ = 1) (hp : ‖p‖ = 1)
    (hpn : p ≠ n) (hpnm : p ≠ -n) :
    arcMeasure (greatCircle p ∩ {u : E3 | 0 ≤ inner ℝ n u}) = ENNReal.ofReal Real.pi := by
  obtain ⟨F₁,F₂,hF₁,hF₂,hF⟩ := SphereGeom.exists_measurable_frame
  let v₁ := F₁ p
  let v₂ := F₂ p
  have hv : Orthonormal ℝ ![v₁,v₂,p] := hF p hp
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![v₁,v₂,p]) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let B : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb0 : B 0 = v₁ := by simp [B]
  have hb1 : B 1 = v₂ := by simp [B]
  have hb2 : B 2 = p := by simp [B]
  have hsum (u : E3) : B.repr u 0 • v₁ + B.repr u 1 • v₂ + B.repr u 2 • p = u := by
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, add_assoc] using B.sum_repr u
  have hnorm (u : E3) (hu : ‖u‖ = 1) :
      B.repr u 0 ^ 2 + B.repr u 1 ^ 2 + B.repr u 2 ^ 2 = 1 := by
    have hh : ‖B.repr u‖ ^ 2 = 1 := by rw [B.repr.norm_map, hu]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have hinner (u : E3) : inner ℝ n u =
      B.repr n 0 * B.repr u 0 + B.repr n 1 * B.repr u 1 + B.repr n 2 * B.repr u 2 := by
    have hh := B.repr.inner_map_map n u
    rw [PiLp.inner_apply, Fin.sum_univ_three] at hh
    simpa only [Real.inner_apply] using hh.symm
  have hnot : B.repr n 0 ≠ 0 ∨ B.repr n 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : B.repr n 2 ^ 2 = (1 : ℝ) ^ 2 := by nlinarith [hnorm n hn]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hc | hc
    · have hnp : n = p := by simpa [h.1,h.2,hc] using (hsum n).symm
      exact hpn hnp.symm
    · have hnp : n = -p := by simpa [h.1,h.2,hc] using (hsum n).symm
      apply hpnm
      rw [hnp, neg_neg]
  let Z : Set E3 := greatCircle p ∩ {u : E3 | inner ℝ n u = 0}
  have hzcoord {u : E3} (hu : u ∈ Z) :
      B.repr u 2 = 0 ∧ B.repr u 0 ^ 2 + B.repr u 1 ^ 2 = 1 ∧
        B.repr n 0 * B.repr u 0 + B.repr n 1 * B.repr u 1 = 0 := by
    have hpu : B.repr u 2 = 0 := by
      simpa [B.repr_apply_apply, hb2] using hu.1.2
    refine ⟨hpu, ?_, ?_⟩
    · nlinarith [hnorm u hu.1.1]
    · have hh := hinner u
      rw [hu.2,hpu] at hh
      nlinarith
  have hzfin : Z.Finite := by
    apply Set.Finite.of_finite_image (f := fun u : E3 => (B.repr u 0, B.repr u 1))
    · refine (finite_unitCircle_line (B.repr n 0) (B.repr n 1) hnot).subset ?_
      rintro z ⟨u,hu,rfl⟩
      exact (hzcoord hu).2
    · intro u hu v hv huv
      apply B.repr.injective
      apply PiLp.ext
      intro i
      fin_cases i
      · exact congrArg Prod.fst huv
      · exact congrArg Prod.snd huv
      · exact (hzcoord hu).1.trans (hzcoord hv).1.symm
  letI : NullSingletonClass arcMeasure := by
    unfold arcMeasure
    exact Measure.nullSingletonClass_hausdorff E3 (by norm_num : (0 : ℝ) < 1)
  have hz : arcMeasure Z = 0 := hzfin.measure_zero arcMeasure
  let A : Set E3 := greatCircle p ∩ {u : E3 | 0 ≤ inner ℝ n u}
  let C : Set E3 := greatCircle p ∩ {u : E3 | inner ℝ n u ≤ 0}
  have hC : MeasurableSet C := by
    exact ((isClosed_eq continuous_norm continuous_const).measurableSet.inter
      (isClosed_eq (by fun_prop : Continuous (fun u : E3 => inner ℝ p u)) continuous_const).measurableSet).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hUnion : A ∪ C = greatCircle p := by
    ext u
    simp only [A,C,Set.mem_union,Set.mem_inter_iff,Set.mem_setOf_eq]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro h
      rcases le_total (0 : ℝ) (inner ℝ n u) with hu | hu
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr ⟨h,hu⟩
  have hInter : A ∩ C = Z := by
    ext u
    simp only [A,C,Z,Set.mem_inter_iff,Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h,ha⟩,hc,hb⟩
      exact ⟨h,le_antisymm hb ha⟩
    · rintro ⟨h,hz⟩
      exact ⟨⟨h,by simp [hz]⟩,h,by simp [hz]⟩
  have hImage : (fun u : E3 => -u) '' A = C := by
    ext u
    constructor
    · rintro ⟨v,⟨⟨hv,hpv⟩,hnv⟩,rfl⟩
      exact ⟨⟨by simpa using hv,by simp [inner_neg_right,hpv]⟩,by simpa [inner_neg_right] using hnv⟩
    · rintro ⟨⟨hu,hpu⟩,hnu⟩
      refine ⟨-u,⟨⟨by simpa using hu,by simp [inner_neg_right,hpu]⟩,?_⟩,by simp⟩
      simpa [inner_neg_right] using hnu
  have hEq : arcMeasure C = arcMeasure A := by
    rw [← hImage]
    exact (LinearIsometryEquiv.neg ℝ : E3 ≃ₗᵢ[ℝ] E3).isometry.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) A
  have hGc : arcMeasure (greatCircle p) = ENNReal.ofReal (2 * Real.pi) := by
    have hc : Measurable (circlePt 0 v₁ v₂ 1) := by unfold circlePt; fun_prop
    have hh := congrArg (fun μ : Measure E3 => μ Set.univ)
      (SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame v₁ v₂ p hv)
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.map_apply hc MeasurableSet.univ] at hh
    simpa only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, sub_neg_eq_add, ← two_mul] using hh
  have hAdd := measure_union_add_inter (μ := arcMeasure) A hC
  rw [hUnion,hInter,hz,hEq,hGc,add_zero] at hAdd
  have hfinite : arcMeasure A ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [← hGc]
    exact measure_mono Set.inter_subset_left
  apply (ENNReal.toReal_eq_toReal_iff' hfinite ENNReal.ofReal_ne_top).mp
  have ht := congrArg ENNReal.toReal hAdd
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal (by positivity)] at ht
  rw [ENNReal.toReal_ofReal Real.pi_pos.le]
  linarith

end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) {u v : Pt}
    (hu : u ∈ greatCircle p ∩ K) (hv : v ∈ greatCircle p ∩ K)
    (huv : u ≠ -v) : JoinedIn (greatCircle p ∩ K) u v := by
  let z : ℝ → Pt := fun t => (1 - t) • u + t • v
  have hun : ‖u‖ = 1 := hu.1.1
  have hvn : ‖v‖ = 1 := hv.1.1
  have hzn (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : z t ≠ 0 := by
    intro hz
    have heq : (1 - t) • u = -(t • v) := eq_neg_of_add_eq_zero_left hz
    have hn := congrArg norm heq
    simp only [norm_smul, norm_neg, Real.norm_eq_abs, hun, hvn, mul_one,
      abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hn
    have ht2 : t = (1 / 2 : ℝ) := by linarith
    have hzero : (1 / 2 : ℝ) • (u + v) = 0 := by
      norm_num [z, ht2, smul_add] at hz ⊢
      exact hz
    have huv0 : u + v = 0 := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact huv (eq_neg_of_add_eq_zero_left huv0)
  let g : ℝ → Pt := fun t => ‖z t‖⁻¹ • z t
  have hzcont : Continuous z := by fun_prop
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    exact (hzcont.norm.continuousOn.inv₀ (fun t ht => norm_ne_zero_iff.mpr (hzn t ht))).smul
      hzcont.continuousOn
  refine JoinedIn.ofLine hgcont ?_ ?_ ?_
  · simp [g, z, hun]
  · simp [g, z, hvn]
  · rintro x ⟨t, ht, rfl⟩
    have hk := hK.geodesically_convex u hu.2 v hv.2 huv t ht
    refine ⟨⟨?_, ?_⟩, hk⟩
    · simpa only [Metric.mem_sphere, dist_zero_right, g, z] using hK.subset_sphere hk
    · simp [g, z, inner_smul_right, inner_add_right, hu.1.2, hv.1.2]

end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_connected {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) :
    (greatCircle p ∩ K).Finite ∨ IsConnected (greatCircle p ∩ K) := by
  let S : Set Pt := greatCircle p ∩ K
  by_cases hSn : S.Nonempty
  · obtain ⟨u, hu⟩ := hSn
    by_cases hall : S ⊆ ({u, -u} : Set Pt)
    · exact Or.inl (((Set.finite_singleton (-u)).insert u).subset hall)
    · obtain ⟨v, hv, hvpair⟩ := Set.not_subset.mp hall
      have hvu : v ≠ u := by
        intro heq
        exact hvpair (by simp [heq])
      have hvmu : v ≠ -u := by
        intro heq
        exact hvpair (by simp [heq])
      right
      apply IsPathConnected.isConnected
      refine ⟨u, hu, ?_⟩
      intro x hx
      by_cases hux : u ≠ -x
      · exact HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hu hx hux
      · have hux : u = -x := not_ne_iff.mp hux
        have huv : u ≠ -v := by
          intro hh
          apply hvmu
          simpa [hh] using (show v = v from rfl)
        have hvx : v ≠ -x := by
          intro hh
          exact hvu (hh.trans hux.symm)
        exact (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hu hv huv).trans
          (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hv hx hvx)
  · exact Or.inl (by change S.Finite; rw [Set.not_nonempty_iff_eq_empty.mp hSn]; exact Set.finite_empty)

end

section
open MeasureTheory Real
open scoped Classical
private theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.periodic_compact_connected_arc {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : ℝ → X) (hC : Continuous C) (T : ℝ) (hT : 0 < T)
    (hper : Function.Periodic C T)
    (hinj : ∀ a b : ℝ, b - a < T → Set.InjOn C (Set.Icc a b))
    (S : Set X) (hS : IsConnected S) (hcompact : IsCompact S)
    (hsub : S ⊆ Set.range C) (cut : ℝ) (hcut : C cut ∉ S) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < T ∧ S = C '' Set.Icc a b := by
  letI : Fact (0 < T) := ⟨hT⟩
  have himg : C '' Set.Icc cut (cut + T) = Set.range C := by
    apply Set.Subset.antisymm (Set.image_subset_range _ _)
    rintro x ⟨t, rfl⟩
    have hx : (t : AddCircle T) ∈ ((↑) : ℝ → AddCircle T) '' Set.Icc cut (cut + T) := by
      rw [AddCircle.coe_image_Icc_eq T cut]
      trivial
    obtain ⟨s, hs, hst⟩ := hx
    refine ⟨s, hs, ?_⟩
    simpa only [Function.Periodic.lift_coe] using congrArg hper.lift hst
  let U : Set ℝ := Set.Icc cut (cut + T) ∩ C ⁻¹' S
  have hU : IsCompact U :=
    isCompact_Icc.inter_right (hcompact.isClosed.preimage hC)
  have hUimg : C '' U = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact ht.2
    · intro x hx
      obtain ⟨t, ht, htx⟩ := himg.symm ▸ hsub hx
      exact ⟨t, ⟨ht, (show C t ∈ S by simpa only [htx] using hx)⟩, htx⟩
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    obtain ⟨t, ht, _⟩ := hUimg.symm ▸ hx
    exact ⟨t, ht⟩
  have hUstrict (t : ℝ) (ht : t ∈ U) : cut < t ∧ t < cut + T := by
    obtain ⟨⟨hlt, htu⟩, hts⟩ := ht
    change C t ∈ S at hts
    refine ⟨lt_of_le_of_ne hlt ?_, lt_of_le_of_ne htu ?_⟩
    · intro heq
      subst t
      exact hcut hts
    · intro heq
      subst t
      rw [hper cut] at hts
      exact hcut hts
  have hUinj : Set.InjOn C U := by
    intro s hs t ht hst
    by_cases hle : s ≤ t
    · exact hinj s t (by
        have h₁ := hUstrict s hs
        have h₂ := hUstrict t ht
        linarith) ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hst
    · have hle' : t ≤ s := le_of_not_ge hle
      exact hinj t s (by
        have h₁ := hUstrict s hs
        have h₂ := hUstrict t ht
        linarith) ⟨hle', le_rfl⟩ ⟨le_rfl, hle'⟩ hst
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let f : U → X := fun t => C t
  have hf : Continuous f := hC.comp continuous_subtype_val
  have hfemb := hf.isClosedEmbedding (fun s t heq => Subtype.ext (hUinj s.property t.property heq))
  have hfimg : f '' Set.univ = S := by
    change (C ∘ (Subtype.val : U → ℝ)) '' Set.univ = S
    rw [Set.image_comp, Set.image_univ, Subtype.range_val]
    exact hUimg
  have hUpcsub : IsPreconnected (Set.univ : Set U) :=
    hfemb.isInducing.isPreconnected_image.mp (hfimg ▸ hS.isPreconnected)
  have hUpc : IsPreconnected U := by
    have hh := Topology.IsInducing.subtypeVal.isPreconnected_image.mpr hUpcsub
    simpa only [Set.image_univ, Subtype.range_val] using hh
  have hconn : IsConnected U := ⟨hUne, hUpc⟩
  let a := sInf U
  let b := sSup U
  have ha : a ∈ U := hU.sInf_mem hUne
  have hb : b ∈ U := hU.sSup_mem hUne
  have hle : a ≤ b := csInf_le hU.bddBelow hb
  have hshort : b - a < T := by
    have h₁ := hUstrict a ha
    have h₂ := hUstrict b hb
    linarith
  refine ⟨a, b, hle, hshort, ?_⟩
  rw [← hUimg, eq_Icc_of_connected_compact hconn hU]

end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 800000
private theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_short_arc {K : Set Pt} (hK : IsRegularRegionCrofton K) (E1 E2 p : Pt)
    (hE : Orthonormal ℝ ![E1, E2, p]) (hL : chordLen K (greatCircle p) ≤ π) :
    (greatCircle p ∩ K).Finite ∨
      ∃ a b : ℝ, a ≤ b ∧ b - a ≤ π ∧
        greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b := by
  rcases HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_connected hK p with hf | hc
  · exact Or.inl hf
  right
  let C : ℝ → Pt := circlePt 0 E1 E2 1
  let S : Set Pt := greatCircle p ∩ K
  have h00 : inner ℝ E1 E1 = 1 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have hp0 : inner ℝ p E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 0)
  have hp1 : inner ℝ p E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 1)
  have he2 : Orthonormal ℝ ![E1,E2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hinner (s t : ℝ) : inner ℝ (C s) (C t) = Real.cos (s - t) := by
    simp only [C, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h00, h01, h10, h11,
      mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Real.cos_sub]
    ring
  have hCg (t : ℝ) : C t ∈ greatCircle p := by
    refine ⟨?_, ?_⟩
    · have hh : ‖C t‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, hinner]
        simp
      nlinarith [norm_nonneg (C t)]
    · simp [C, circlePt, inner_add_right, real_inner_smul_right, hp0, hp1]
  have hrange : Set.range C = greatCircle p := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      exact hCg t
    · rw [← SphereGeom.Aux.Pair.circle_image E1 E2 p hE]
      exact Set.image_subset_range _ _
  have hgclosed : IsClosed (greatCircle p) :=
    (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hcomp : IsCompact S := hK.isCompact.inter_left hgclosed
  have hmass : arcMeasure (greatCircle p) = ENNReal.ofReal (2 * π) := by
    rw [← SphereGeom.Aux.Pair.circle_image E1 E2 p hE]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num)
      (-π) π (by linarith [Real.pi_pos]) (by linarith)
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      show π - -π = 2 * π by ring] using hm
  have hnot : ¬ Set.range C ⊆ S := by
    intro hs
    have heq : S = greatCircle p := Set.Subset.antisymm (Set.inter_subset_left) (hrange ▸ hs)
    have hlen : chordLen K (greatCircle p) = 2 * π := by
      change (arcMeasure S).toReal = _
      rw [heq, hmass, ENNReal.toReal_ofReal (by positivity)]
    linarith [Real.pi_pos]
  obtain ⟨x, hx, hxS⟩ := Set.not_subset.mp hnot
  obtain ⟨cut, rfl⟩ := hx
  have hCcont : Continuous C := by unfold C circlePt; fun_prop
  have hper : Function.Periodic C (2 * π) := by
    intro t
    simp [C, circlePt, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshort : ∀ a b : ℝ, b - a < 2 * π → Set.InjOn C (Set.Icc a b) := by
    intro a b hab
    exact SphereGeom.Aux.ArcLength.injOn_Icc 0 ![E1,E2] he2 1 (by norm_num) a b hab
  have hsub : S ⊆ Set.range C := hrange.symm ▸ Set.inter_subset_left
  obtain ⟨a,b,hab,hb,hgeom⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Chord.Interval.periodic_compact_connected_arc C hCcont
      (2 * π) (by positivity) hper hshort S hc hcomp hsub cut hxS
  have hlen : chordLen K (greatCircle p) = b - a := by
    change (arcMeasure S).toReal = _
    rw [hgeom]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num) a b hab hb.le
    simpa [C, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using congrArg ENNReal.toReal hm
  exact ⟨a,b,hab,hlen ▸ hL,hgeom⟩

end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Topology Filter
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.boundary_pair_short_arc {K : Set Pt} (hK : IsRegularRegionCrofton K) (p u v : Pt)
    (hp : ‖p‖ = 1) (huv : u ≠ v)
    (hb : greatCircle p ∩ sFrontier K = {u,v})
    (hpos : 0 < chordLen K (greatCircle p)) :
    ∃ (E1 E2 : Pt) (a b : ℝ), Orthonormal ℝ ![E1,E2,p] ∧ a < b ∧ b - a ≤ π ∧
      greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b ∧
      ({circlePt 0 E1 E2 1 a, circlePt 0 E1 E2 1 b} : Set Pt) = {u,v} := by
  classical
  letI : NullSingletonClass arcMeasure := by
    unfold arcMeasure
    exact Measure.nullSingletonClass_hausdorff E3 (by norm_num : (0 : ℝ) < 1)
  let S : Set Pt := greatCircle p ∩ K
  let C : Set Pt := {w | w = 0 ∨ ‖w‖⁻¹ • w ∈ K}
  obtain ⟨hCclosed,hCconvex,hCscale,hCinter,hCfront⟩ :=
    HardSphereB5.SphericalCrofton.Aux.HitMass.regular_cone_geometry K hK
  have hSnot : ¬ S ⊆ ({u,v} : Set Pt) := by
    intro hsub
    have hzero : arcMeasure S = 0 := ((Set.toFinite ({u,v} : Set Pt)).subset hsub).measure_zero arcMeasure
    have hlen0 : chordLen K (greatCircle p) = 0 := by
      change (arcMeasure S).toReal = 0
      rw [hzero, ENNReal.toReal_zero]
    linarith
  obtain ⟨z,hz,hzpair⟩ := Set.not_subset.mp hSnot
  have hzunit : ‖z‖ = 1 := hz.1.1
  have hzfront : z ∉ sFrontier K := by
    intro hf
    apply hzpair
    rw [← hb]
    exact ⟨hz.1,hf⟩
  have hzC : z ∈ C := by
    right
    simpa [hzunit] using hz.2
  have hzinter : z ∈ interior C := by
    by_contra hzi
    apply hzfront
    apply (hCfront z hzunit).mp
    exact ⟨subset_closure hzC,hzi⟩
  obtain ⟨n,hn,hhalf⟩ := hK.in_closed_hemisphere
  have hnNorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hConeHalf : ∀ w ∈ C, 0 ≤ inner ℝ n w := by
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    have hwK : ‖w‖⁻¹ • w ∈ K := hw.resolve_left hw0
    have h := hhalf _ hwK
    rw [real_inner_smul_right] at h
    have hwNorm : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw0)
    by_contra hh
    have hneg : inner ℝ n w < 0 := lt_of_not_ge hh
    nlinarith
  have hnz : 0 < inner ℝ n z := by
    have hnonneg := hConeHalf z (interior_subset hzinter)
    by_contra hposz
    have hnz0 : inner ℝ n z = 0 := le_antisymm (le_of_not_gt hposz) hnonneg
    have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
    have hcont : ContinuousAt (fun d : ℝ => z - d • n) 0 := by fun_prop
    have hnear : ∀ᶠ d in 𝓝 (0 : ℝ), z - d • n ∈ interior C := by
      apply hcont.eventually
      simpa using isOpen_interior.mem_nhds hzinter
    have hnear' := hnear.filter_mono
      (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hm : ∀ᶠ d in 𝓝[Set.Ioi (0 : ℝ)] 0, d ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
    obtain ⟨d,hdz,hd⟩ := (hnear'.and hm).exists
    have hbad := hConeHalf (z - d • n) (interior_subset hdz)
    simp only [inner_sub_right, real_inner_smul_right, hnz0] at hbad
    have hdpos : 0 < d := hd
    nlinarith
  let n0 : Pt := ‖n‖⁻¹ • n
  have hn0 : ‖n0‖ = 1 := by
    simp [n0, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hnNorm.ne']
  have hn0z : 0 < inner ℝ n0 z := by
    simpa [n0, real_inner_smul_left] using mul_pos (inv_pos.mpr hnNorm) hnz
  have hpn : p ≠ n0 := by
    intro heq
    rw [← heq, hz.1.2] at hn0z
    linarith
  have hpnm : p ≠ -n0 := by
    intro heq
    have hpz := hz.1.2
    rw [heq, inner_neg_left] at hpz
    linarith
  have hhem := SphereGeom.Aux.Chord.arcMeasure_greatCircle_closedHemisphere n0 p hn0 hp hpn hpnm
  have hmass : arcMeasure S ≤ ENNReal.ofReal π := by
    rw [← hhem]
    apply measure_mono
    intro w hw
    refine ⟨hw.1, ?_⟩
    change 0 ≤ inner ℝ n0 w
    dsimp only [n0]
    rw [real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg n)) (hhalf w hw.2)
  have hL : chordLen K (greatCircle p) ≤ π := by
    change (arcMeasure S).toReal ≤ π
    simpa [ENNReal.toReal_ofReal Real.pi_pos.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  obtain ⟨F1,F2,hF1,hF2,hF⟩ := SphereGeom.exists_measurable_frame
  let E1 : Pt := F1 p
  let E2 : Pt := F2 p
  have hE : Orthonormal ℝ ![E1,E2,p] := hF p hp
  rcases HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_short_arc hK E1 E2 p hE hL with hf | hg
  · have hzero := hf.measure_zero arcMeasure
    have hlen0 : chordLen K (greatCircle p) = 0 := by
      unfold chordLen len
      rw [hzero, ENNReal.toReal_zero]
    linarith
  obtain ⟨a,b,hab,hπ,hgeom⟩ := hg
  let f : ℝ → Pt := circlePt 0 E1 E2 1
  have h00 : inner ℝ E1 E1 = 1 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have hp0 : inner ℝ p E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 0)
  have hp1 : inner ℝ p E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 1)
  have he2 : Orthonormal ℝ ![E1,E2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hlen : chordLen K (greatCircle p) = b - a := by
    unfold chordLen len
    rw [hgeom]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num)
      a b hab (by linarith [Real.pi_pos])
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using congrArg ENNReal.toReal hm
  have hablt : a < b := by linarith
  have hfcont : Continuous f := by unfold f circlePt; fun_prop
  have hfin (t : ℝ) : f t ∈ greatCircle p := by
    have hinnerSelf : inner ℝ (f t) (f t) = 1 := by
      simp only [f, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11,
        mul_one,mul_zero,zero_mul,add_zero,zero_add]
      nlinarith [Real.sin_sq_add_cos_sq t]
    refine ⟨?_, ?_⟩
    · nlinarith [real_inner_self_eq_norm_sq (f t), norm_nonneg (f t)]
    · simp [f, circlePt, inner_add_right, real_inner_smul_right, hp0, hp1]
  have hmemC (t : ℝ) : f t ∈ C ↔ f t ∈ K := by
    have htNorm := (hfin t).1
    have htne : f t ≠ 0 := by
      intro ht0
      rw [ht0, norm_zero] at htNorm
      norm_num at htNorm
    simp only [C, Set.mem_setOf_eq, htne, false_or, htNorm, inv_one, one_smul]
  have hfaK : f a ∈ K := by
    have hh : f a ∈ greatCircle p ∩ K := hgeom ▸ Set.mem_image_of_mem _ ⟨le_rfl,hab⟩
    exact hh.2
  have hfbK : f b ∈ K := by
    have hh : f b ∈ greatCircle p ∩ K := hgeom ▸ Set.mem_image_of_mem _ ⟨hab,le_rfl⟩
    exact hh.2
  have hfaFront : f a ∈ sFrontier K := by
    apply (hCfront (f a) (hfin a).1).mp
    refine ⟨subset_closure ((hmemC a).mpr hfaK), ?_⟩
    intro hi
    have hnear : ∀ᶠ t in 𝓝 a, f t ∈ interior C :=
      hfcont.continuousAt.eventually (isOpen_interior.mem_nhds hi)
    have hleft : ∀ᶠ t in 𝓝[Set.Iio a] a, f t ∈ interior C := hnear.filter_mono nhdsWithin_le_nhds
    have hlow : ∀ᶠ t in 𝓝[Set.Iio a] a, a - π/2 < t :=
      (eventually_gt_nhds (by linarith [Real.pi_pos] : a - π/2 < a)).filter_mono nhdsWithin_le_nhds
    have hlt : ∀ᶠ t in 𝓝[Set.Iio a] a, t < a := self_mem_nhdsWithin
    obtain ⟨t,⟨hti,hlo⟩,hlt⟩ := ((hleft.and hlow).and hlt).exists
    have hftK := (hmemC t).mp (interior_subset hti)
    have hftS : f t ∈ greatCircle p ∩ K := ⟨hfin t,hftK⟩
    rw [hgeom] at hftS
    obtain ⟨s,hs,hst⟩ := hftS
    have heq : s = t := SphereGeom.Aux.ArcLength.injOn_Icc
      0 ![E1,E2] he2 1 (by norm_num) (a-π/2) b (by linarith [Real.pi_pos])
      ⟨by linarith [hs.1],hs.2⟩ ⟨hlo.le,by linarith⟩ hst
    linarith [hs.1]
  have hfbFront : f b ∈ sFrontier K := by
    apply (hCfront (f b) (hfin b).1).mp
    refine ⟨subset_closure ((hmemC b).mpr hfbK), ?_⟩
    intro hi
    have hnear : ∀ᶠ t in 𝓝 b, f t ∈ interior C :=
      hfcont.continuousAt.eventually (isOpen_interior.mem_nhds hi)
    have hright : ∀ᶠ t in 𝓝[Set.Ioi b] b, f t ∈ interior C := hnear.filter_mono nhdsWithin_le_nhds
    have hupp : ∀ᶠ t in 𝓝[Set.Ioi b] b, t < b + π/2 :=
      (eventually_lt_nhds (by linarith [Real.pi_pos] : b < b + π/2)).filter_mono nhdsWithin_le_nhds
    have hgt : ∀ᶠ t in 𝓝[Set.Ioi b] b, b < t := self_mem_nhdsWithin
    obtain ⟨t,⟨hti,hupp⟩,hgt⟩ := ((hright.and hupp).and hgt).exists
    have hftK := (hmemC t).mp (interior_subset hti)
    have hftS : f t ∈ greatCircle p ∩ K := ⟨hfin t,hftK⟩
    rw [hgeom] at hftS
    obtain ⟨s,hs,hst⟩ := hftS
    have heq : s = t := SphereGeom.Aux.ArcLength.injOn_Icc
      0 ![E1,E2] he2 1 (by norm_num) a (b+π/2) (by linarith [Real.pi_pos])
      ⟨hs.1,by linarith [hs.2]⟩ ⟨by linarith,hupp.le⟩ hst
    linarith [hs.2]
  have hfne : f a ≠ f b := by
    intro heq
    have habeq := SphereGeom.Aux.ArcLength.injOn_Icc
      0 ![E1,E2] he2 1 (by norm_num) a b (by linarith [Real.pi_pos])
      ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ heq
    linarith
  have hamem : f a ∈ ({u,v} : Set Pt) := hb ▸ ⟨hfin a,hfaFront⟩
  have hbmem : f b ∈ ({u,v} : Set Pt) := hb ▸ ⟨hfin b,hfbFront⟩
  have hends : ({f a,f b} : Set Pt) = {u,v} := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hamem hbmem
    rcases hamem with ha | ha <;> rcases hbmem with hb' | hb'
    · exact False.elim (hfne (ha.trans hb'.symm))
    · rw [ha,hb']
    · rw [ha,hb']
      exact Set.pair_comm v u
    · exact False.elim (hfne (ha.trans hb'.symm))
  exact ⟨E1,E2,a,b,hE,hablt,hπ,hgeom,hends⟩

end

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_chordLen_eq_delta_of_boundary_pair {K : Set Pt} (hK : IsRegularRegionCrofton K) (p u v : Pt) (hp : ‖p‖ = 1) (huv : u ≠ v) (hb : greatCircle p ∩ sFrontier K = {u,v}) (hpos : 0 < chordLen K (greatCircle p)) :
    0 < arccos (inner ℝ u v) ∧ chordLen K (greatCircle p) = arccos (inner ℝ u v) := by
  obtain ⟨E1,E2,a,b,hE,hab,hπ,hgeom,hends⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Endpoint.boundary_pair_short_arc hK p u v hp huv hb hpos
  exact HardSphereB5.SphericalCrofton.Aux.Endpoint.chordLen_eq_delta_of_short_arc
    K p u v E1 E2 a b hE hab hπ huv hgeom hends

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_chordLen_eq_delta_of_boundary_pair
