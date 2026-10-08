import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_jacobian
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_jacobian :
    ∀ (x : Chart5)
    (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1)
    (hα : x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)))
    (hβ : x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x))), |LinearMap.det (fderiv ℝ Phi x).toLinearMap| =
      dist (sourceEndpointA x) (sourceEndpointB x) /
        (‖sourceCenter x‖ * ‖sourceCenter x-e‖) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_jacobian
