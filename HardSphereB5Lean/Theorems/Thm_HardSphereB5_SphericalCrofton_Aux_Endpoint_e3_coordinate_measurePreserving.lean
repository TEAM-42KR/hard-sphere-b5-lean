import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_e3_coordinate_measurePreserving
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.e3_coordinate_measurePreserving :
    MeasurePreserving (fun x : SphereGeom.E3 => ((x 0,x 1),x 2)) (volume : Measure SphereGeom.E3) ((volume : Measure (ℝ×ℝ)).prod (volume : Measure ℝ)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_e3_coordinate_measurePreserving
