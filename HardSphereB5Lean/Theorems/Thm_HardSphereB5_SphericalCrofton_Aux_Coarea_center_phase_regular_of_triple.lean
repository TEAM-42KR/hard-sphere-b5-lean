import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_regular_of_triple
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_regular_of_triple :
    ∀ (D u v : Pt) (hT : inner ℝ (cross u v) e ≠ 0), centerFrame0 (v-u) ≠ 0 ∧ centerPhase D (D+u) (D+v) ∈ Complex.slitPlane :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_regular_of_triple
