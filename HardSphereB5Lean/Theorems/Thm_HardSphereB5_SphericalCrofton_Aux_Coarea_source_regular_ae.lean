import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_ae
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_regular_ae :
    ∀ᵐ x : Chart5 ∂volume,
    (offAxis (sourceCenter x) ∧ sourceCenter x ∈ LamC ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x - e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1) → sourceRegular x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_ae
