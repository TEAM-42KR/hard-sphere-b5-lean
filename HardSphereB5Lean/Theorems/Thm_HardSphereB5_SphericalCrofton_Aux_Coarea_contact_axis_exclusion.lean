import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_axis_exclusion
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.contact_axis_exclusion :
    ∀ (D p q : Pt) (hD : D ∈ LamC) (hp : ‖p‖ = 1) (hq : ‖q-e‖ = 1)
    (hp0 : 1/2 < p 0) (hq0 : q 0 < 1/2)
    (hDp : dist D p = 1) (hDq : dist D q = 1), offAxis D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_axis_exclusion
