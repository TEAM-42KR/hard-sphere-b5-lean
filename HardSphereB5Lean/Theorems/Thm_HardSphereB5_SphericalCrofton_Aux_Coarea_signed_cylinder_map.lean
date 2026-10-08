import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_cylinder_map
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.signed_cylinder_map :
    dOmega =
    ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)).map
        (fun x : ℝ × ℝ => endpointCylinder x.1 x.2) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_cylinder_map
