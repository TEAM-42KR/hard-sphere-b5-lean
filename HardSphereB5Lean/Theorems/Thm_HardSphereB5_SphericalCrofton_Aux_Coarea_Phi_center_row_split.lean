import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_split
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_center_row_split :
    ∀ (x : Chart5) (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1), ∃ LP LQ : Pt →L[ℝ] ℝ, ∀ w : Chart5,
      (fderiv ℝ Phi x w) 4 =
        (dist (sourceEndpointA x) (sourceEndpointB x) *
          (1-dist (sourceEndpointA x) (sourceEndpointB x)^2/4))⁻¹ *
          inner ℝ (cross (sourceEndpointA x-sourceCenter x) (sourceEndpointB x-sourceCenter x))
            (fderiv ℝ sourceCenter x w) +
        LP (fderiv ℝ sourceEndpointA x w) + LQ (fderiv ℝ sourceEndpointB x w) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_split
