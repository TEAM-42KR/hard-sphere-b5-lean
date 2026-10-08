import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_pair_inverse_distance
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.sphere_pair_inverse_distance :
    Integrable (fun pq : Pt × Pt => (dist pq.1 pq.2)⁻¹)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_pair_inverse_distance
