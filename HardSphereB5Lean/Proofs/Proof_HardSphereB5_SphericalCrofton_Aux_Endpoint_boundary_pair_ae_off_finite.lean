import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_support_poles_null
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_height_level_null
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_encard_off_support
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_pair_ae_off_finite {K : Set Pt} (hK : IsRegularRegionCrofton K) (F : Set Pt)
    (hF : F.Finite) (hFu : ∀ u ∈ F, ‖u‖ = 1) :
    ∀ᵐ p ∂dOmega, ‖p‖ = 1 ∧ greatCircle p ∩ F = ∅ ∧
      ((greatCircle p ∩ sFrontier K).encard : ENNReal) =
        if 0 < chordLen K (greatCircle p) then 2 else 0 := by
  have hsn : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0:Pt) 1 :=
    ae_iff.mpr SphereGeom.dOmega_compl_sphere
  have hs := SphereGeom.Aux.SupportCircles.support_poles_null K hK.subset_sphere
  have hn : ∀ᵐ p ∂dOmega, p ∉ {p : Pt | ‖p‖ = 1 ∧
      ((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧
        ∃ u ∈ K, inner ℝ p u = 0} := by
    exact ae_iff.mpr (by simpa only [Set.mem_setOf_eq, not_not] using hs)
  have hv : ∀ u ∈ F, ∀ᵐ p ∂dOmega, inner ℝ u p ≠ 0 := by
    intro u hu
    have hh := SphereGeom.Aux.SupportCircles.height_level_null u (hFu u hu) 0
    exact ae_iff.mpr (by simpa only [Set.mem_setOf_eq, not_not] using hh)
  have hvall : ∀ᵐ p ∂dOmega, ∀ u ∈ F, inner ℝ u p ≠ 0 :=
    (ae_ball_iff hF.countable).mpr hv
  filter_upwards [hsn,hn,hvall] with p hp hpn hpF
  have hp' : ‖p‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp
  refine ⟨hp',?_,?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hpu : inner ℝ p u = 0 := hu.1.2
    exact hpF u hu.2 (by rwa [real_inner_comm])
  · exact HardSphereB5.SphericalCrofton.Aux.HitMass.encard_off_support hK p hp'
      (fun h => hpn ⟨hp',h⟩)
