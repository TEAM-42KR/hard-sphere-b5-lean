import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_contact_gradient
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_contact_gradient :
    ∀ (D p p' : Pt) (hz0 : 0 < dist p p') (hz2 : dist p p' < 2)
    (hDp : dist D p = 1) (hDp' : dist D p' = 1)
    (hframe : centerFrame0 (p'-p) ≠ 0)
    (hphase : centerPhase D p p' ∈ Complex.slitPlane), HasFDerivAt (fun W : Pt => Complex.arg (centerPhase W p p'))
      ((dist p p' * (1 - dist p p' ^ 2 / 4))⁻¹ •
        (innerSL ℝ (cross (p-D) (p'-D)))) D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_contact_gradient
