import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_orthogonal_phase_inverse
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.orthogonal_phase_inverse :
    ∀ (f : Fin 3 → Pt) (hf : Orthonormal ℝ f) (w : Pt)
    (hw : inner ℝ (f 2) w = 0), ‖w‖ • (Real.cos (Complex.arg (phase (inner ℝ (f 0) w) (inner ℝ (f 1) w))) • f 0 +
      Real.sin (Complex.arg (phase (inner ℝ (f 0) w) (inner ℝ (f 1) w))) • f 1) = w :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_orthogonal_phase_inverse
