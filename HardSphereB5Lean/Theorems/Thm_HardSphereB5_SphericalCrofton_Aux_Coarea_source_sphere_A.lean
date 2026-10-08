import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A :
    ∀ (D : Pt) (hoff : offAxis D) (hr : ‖D‖ < 2) (θ : ℝ), ‖u D θ‖ = 1 ∧ ‖D+u D θ‖ = 1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
