import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_of_generic
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_regular_of_generic :
    ∀ (x : Chart5)
    (hAnte : offAxis (sourceCenter x) ∧ sourceCenter x ∈ LamC ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x - e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1)
    (hαneg : x 3 ≠ -Real.pi) (hαpos : x 3 ≠ Real.pi)
    (hβneg : x 4 ≠ -Real.pi) (hβpos : x 4 ≠ Real.pi)
    (hp2 : (sourceEndpointA x) 2 ≠ 0) (hp'2 : (sourceEndpointB x) 2 ≠ 0)
    (hT : inner ℝ (cross (u (sourceCenter x) (x 3))
      (v (sourceCenter x) (x 4))) e ≠ 0), sourceRegular x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_of_generic
