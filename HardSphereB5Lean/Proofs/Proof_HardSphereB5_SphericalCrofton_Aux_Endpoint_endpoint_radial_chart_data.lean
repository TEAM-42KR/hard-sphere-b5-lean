import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_source_atlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_fibers
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_source_push
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_endpoint_radial_chart_data (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    ∃ (Φ : Pt → Pt) (Φ' : Pt → Pt →L[ℝ] Pt) (P : Pt → Pt × Pt) (s : Set Pt),
      Measurable Φ ∧ Measurable Φ' ∧ Measurable P ∧ MeasurableSet s ∧
      MeasurableSet (hitPoleSet D) ∧
      (∀ x ∈ s, HasFDerivWithinAt Φ (Φ' x) s x) ∧
      (∀ x ∈ s, ‖Φ x‖⁻¹ • Φ x = pairPole (P x)) ∧
      (∀ᵐ y ∂(volume : Measure Pt),
        ({x : Pt | x ∈ s ∧ Φ x = y}.encard : ENNReal) =
          (Metric.ball (0:Pt) 1 ∩ (fun y : Pt => ‖y‖⁻¹ • y) ⁻¹' hitPoleSet D).indicator
            (fun _ => (1:ENNReal)) y) ∧
      (((volume : Measure Pt).restrict s).withDensity
        (fun x => ENNReal.ofReal |(Φ' x).det|)).map P =
          (3:ENNReal)⁻¹ • weightedPairMu D := by
  obtain ⟨C, hC⟩ := circle_endpoint_source_atlas D hD hK
  obtain ⟨hPhi, hPhi', hP, hs, hder, hdir⟩ := circle_atlas_radial_regular D C hC
  obtain ⟨hHit, hcount⟩ := circle_atlas_radial_fibers D hD hK C hC
  exact ⟨atlasRadial C, fderiv ℝ (atlasRadial C), atlasPair C, atlasRadialSource C,
    hPhi, hPhi', hP, hs, hHit, hder, hdir, hcount, circle_atlas_radial_source_push D C hC⟩
