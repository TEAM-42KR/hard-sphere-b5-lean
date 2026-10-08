import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_oriented_fiber
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_pair_ae_off_finite
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_ae_radial_of_ae_spherical
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_fibers (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D))
    (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) :
    MeasurableSet (hitPoleSet D) ∧ (∀ᵐ y ∂(volume : Measure Pt),
      ({x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = y}.encard : ENNReal) =
        (Metric.ball (0:Pt) 1 ∩ (fun y : Pt => ‖y‖⁻¹ • y) ⁻¹' hitPoleSet D).indicator
          (fun _ => (1:ENNReal)) y) := by
  classical
  have hL : Measurable (fun p : Pt => chordLen (SigmaD D) (greatCircle p)) :=
    (SphereGeom.Aux.Chord.measurable_arcMeasure_greatCircle_inter (SigmaD D)
      hK.isCompact.isClosed.measurableSet).ennreal_toReal
  have hHit : MeasurableSet (hitPoleSet D) := measurableSet_lt measurable_const hL
  refine ⟨hHit, ?_⟩
  obtain ⟨F,hF,hcover⟩ := hC.frontier_cover
  let F' : Set Pt := F ∩ Metric.sphere (0 : Pt) 1
  have hF' : F'.Finite := hF.subset Set.inter_subset_left
  have hFu : ∀ u ∈ F', ‖u‖ = 1 := fun u hu => by
    simpa only [Metric.mem_sphere,dist_zero_right] using hu.2
  have hfrontsphere : ∀ u ∈ sFrontier (SigmaD D), u ∈ Metric.sphere (0 : Pt) 1 := by
    intro u hu
    obtain ⟨v,_,rfl⟩ := hu
    exact v.property
  have hcover' : atlasGamma C '' atlasInterval C = sFrontier (SigmaD D) \ F' := by
    rw [hcover]
    ext u
    constructor
    · intro hu
      exact ⟨hu.1, fun hf => hu.2 hf.1⟩
    · intro hu
      exact ⟨hu.1,fun hf => hu.2 ⟨hf,hfrontsphere u hu.1⟩⟩
  have hgood : ∀ᵐ p ∂dOmega, ‖p‖ = 1 ∧ greatCircle p ∩ F' = ∅ ∧
      ((greatCircle p ∩ sFrontier (SigmaD D)).encard : ENNReal) =
        if p ∈ hitPoleSet D then 2 else 0 := by
    simpa only [hitPoleSet, Set.mem_setOf_eq] using boundary_pair_ae_off_finite hK F' hF' hFu
  have hrad := ae_radial_of_ae_spherical _ hgood
  have hnz : ∀ᵐ y ∂(volume : Measure Pt), y ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not,Set.setOf_eq_eq_singleton] using (measure_singleton (0 : Pt) : (volume : Measure Pt) {(0 : Pt)} = 0)
  have hnorm (x : Pt) (hx : x ∈ atlasRadialSource C) : ‖atlasRadial C x‖ = x 2 := by
    have hn : ‖pairPole (atlasPair C x)‖ = 1 :=
      (pole_orientation (atlasGamma C (x 0)) (atlasGamma C (x 1))).2.2.2 hx.2.2.2
    change ‖(x 2) • pairPole (atlasPair C x)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hx.2.2.1.1,hn,mul_one]
  apply ae_of_ae_restrict_of_ae_restrict_compl (Metric.ball (0 : Pt) 1)
  · filter_upwards [hrad, ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hnz] with y hy hyball hy0
    have hr : ‖y‖ ∈ Set.Ioo (0 : ℝ) 1 := ⟨norm_pos_iff.mpr hy0,by
      simpa only [Metric.mem_ball,dist_zero_right] using hyball⟩
    have hyrep : ‖y‖ • (‖y‖⁻¹ • y) = y := by
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0),one_smul]
    have hc := circle_atlas_oriented_fiber D hD hK C hC F' hcover'
      (‖y‖⁻¹ • y) hy.1 hy.2.1 hy.2.2 ‖y‖ hr
    rw [hyrep] at hc
    rw [hc]
    by_cases hhit : ‖y‖⁻¹ • y ∈ hitPoleSet D
    · have hmem : y ∈ Metric.ball (0 : Pt) 1 ∩
          (fun y : Pt => ‖y‖⁻¹ • y) ⁻¹' hitPoleSet D := ⟨hyball,hhit⟩
      rw [if_pos hhit,Set.indicator_of_mem hmem]
    · rw [if_neg hhit,Set.indicator_of_notMem (fun h => hhit h.2)]
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    have hempty : {x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hy
      have hh : ‖y‖ < 1 := by rw [←hx.2,hnorm x hx.1]; exact hx.1.2.2.1.2
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    rw [hempty,Set.encard_empty,ENat.toENNReal_zero,
      Set.indicator_of_notMem (fun h => hy h.1)]
