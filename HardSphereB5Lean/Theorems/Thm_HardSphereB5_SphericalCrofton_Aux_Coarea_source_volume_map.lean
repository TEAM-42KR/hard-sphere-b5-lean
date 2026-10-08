import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_volume_map
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_volume_map :
    MeasurePreserving
    (fun x : Chart5 => (sourceCenter x, (x 3, x 4))) volume
      (volume.prod (volume.prod volume)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_volume_map
