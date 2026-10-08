import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_incidence_regular
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.contact_incidence_regular :
    ∀ (D p q : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hp : p ∈ FA) (hq : q ∈ FB) (hDp : dist D p = 1) (hDq : dist D q = 1)
    (hpq : 0 < dist p q), Rc ‖D‖ ‖D-e‖ < 1 ∧ 0 < (sourcePhaseA D p).re ∧ 0 < (sourcePhaseB D q).re :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_incidence_regular
