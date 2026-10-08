import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_cross_zero
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.inactive_cross_zero :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC) (h : ¬ (offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1)), ABf f D = 0 ∧ Bf f D = 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_cross_zero
