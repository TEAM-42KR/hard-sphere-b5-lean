import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_endpoint_frame_ae
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_endpoint_frame_ae :
    ∀ᵐ pq : Pt × Pt ∂(((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)),
      centerFrame0 (pq.2-pq.1) ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_endpoint_frame_ae
