import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_contact_distances
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_contact_distances :
    ∀ (p q : Pt)
    (hz0 : 0 < dist p q) (hz2 : dist p q < 2)
    (hf : centerFrame0 (q-p) ≠ 0) (θ : ℝ),
    let D := midpoint ℝ p q + Real.sqrt (1-dist p q^2/4) •
      (Real.cos θ • centerFrame0 (q-p)+Real.sin θ • centerFrame1 (q-p))
    dist D p = 1 ∧ dist D q = 1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_contact_distances
