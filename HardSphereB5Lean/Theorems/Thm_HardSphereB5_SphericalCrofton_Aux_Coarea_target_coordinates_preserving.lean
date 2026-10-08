import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_coordinates_preserving
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_coordinates_preserving :
    MeasurePreserving (fun y : Chart5 => (((y 0,y 1),(y 2,y 3)),y 4))
      (volume : Measure Chart5) (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_coordinates_preserving
