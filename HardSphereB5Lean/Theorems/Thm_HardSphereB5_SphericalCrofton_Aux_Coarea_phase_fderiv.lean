import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_phase_fderiv
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.phase_fderiv :
    ∀ (a b : ℝ) (hz : phase a b ∈ Complex.slitPlane), HasFDerivAt (fun p : ℝ × ℝ => Complex.arg (phase p.1 p.2))
      ((a / (a^2+b^2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (b / (a^2+b^2)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) (a,b) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_phase_fderiv
