import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B :
    ∀ (D : Pt) (hoff : offAxis D) (hr : ‖D-e‖ < 2) (θ : ℝ), ‖v D θ‖ = 1 ∧ ‖D+v D θ-e‖ = 1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B
