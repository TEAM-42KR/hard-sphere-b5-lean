import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_isChart_exists
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.isChart_exists :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D - e‖ < 1), ∃ C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts, HardSphereB5.SphericalCrofton.Aux.Santalo.IsChart D C :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_isChart_exists
