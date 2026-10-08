import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_elimination
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_center_row_elimination :
    ∀ (x : Chart5) (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1), ∃ k : Fin 4 → ℝ, ∀ w : Chart5,
      (fderiv ℝ Phi x w) 4 =
        (dist (sourceEndpointA x) (sourceEndpointB x) *
          (1-dist (sourceEndpointA x) (sourceEndpointB x)^2/4))⁻¹ *
          inner ℝ (cross (sourceEndpointA x-sourceCenter x) (sourceEndpointB x-sourceCenter x))
            (fderiv ℝ sourceCenter x w) +
        k 0 * (fderiv ℝ Phi x w) 0 + k 1 * (fderiv ℝ Phi x w) 1 +
        k 2 * (fderiv ℝ Phi x w) 2 + k 3 * (fderiv ℝ Phi x w) 3 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_elimination
