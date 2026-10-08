import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_fderiv
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_fderiv :
    ∀ (D p p' : Pt) (hz : centerPhase D p p' ∈ Complex.slitPlane), HasFDerivAt (fun W : Pt => Complex.arg (centerPhase W p p'))
      ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p') /
          ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p'))^2 +
            (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p'))^2)) •
        (innerSL ℝ (centerFrame1 (p'-p))) -
      (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p') /
          ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p'))^2 +
            (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p'))^2)) •
        (innerSL ℝ (centerFrame0 (p'-p)))) D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_fderiv
