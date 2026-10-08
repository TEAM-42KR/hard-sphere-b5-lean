import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_regular_integral
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_regular_integral :
    ∀ (S : Set Chart5)
    (hS : ∀ x ∈ S, sourceRegular x ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)))
    (hSm : MeasurableSet S) (g : Chart5 → ℝ), (∫ y in Phi '' S, g y) =
      ∫ x in S, (dist (sourceEndpointA x) (sourceEndpointB x) /
        (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) * g (Phi x) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_regular_integral
