import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.dOmega_eq_three_smul_map_radial :
    dOmega = (3 : ENNReal) • (volume.restrict (Metric.ball (0 : E3) 1)).map (fun x : E3 => ‖x‖⁻¹ • x) :=
  @proof_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
