import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_arg_inverse
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_arg_inverse :
    ∀ (D p p' : Pt) (h0 : 0 < dist p p') (hz : dist p p' < 2)
    (hA : dist D p = 1) (hB : dist D p' = 1)
    (hf : centerFrame0 (p'-p) ≠ 0), midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
      (Real.cos (Complex.arg (centerPhase D p p')) • centerFrame0 (p'-p) +
        Real.sin (Complex.arg (centerPhase D p p')) • centerFrame1 (p'-p)) = D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_arg_inverse
