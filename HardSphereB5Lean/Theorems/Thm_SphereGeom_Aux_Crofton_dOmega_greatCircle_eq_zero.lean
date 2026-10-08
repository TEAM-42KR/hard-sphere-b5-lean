import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_dOmega_greatCircle_eq_zero
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.dOmega_greatCircle_eq_zero :
    ∀ (n : E3) (hn : ‖n‖ = 1), dOmega (greatCircle n) = 0 :=
  @proof_SphereGeom_Aux_Crofton_dOmega_greatCircle_eq_zero
