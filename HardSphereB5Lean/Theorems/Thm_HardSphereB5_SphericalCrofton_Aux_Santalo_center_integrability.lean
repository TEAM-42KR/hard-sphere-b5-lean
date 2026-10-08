import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_center_integrability
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.center_integrability :
    ∀ (f : Kern), IntegrableOn (fun D => if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then 2 * Pprim f (min (deltaV D) (Real.pi / 3)) else 0) LamC volume ∧ IntegrableOn (Bf f) LamC volume :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_center_integrability
