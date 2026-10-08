import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_frame_orthonormal :
    ∀ (d : Pt) (hd : d ≠ 0) (hr : centerFrame0 d ≠ 0), Orthonormal ℝ ![centerFrame0 d, centerFrame1 d, unitDir d] :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
