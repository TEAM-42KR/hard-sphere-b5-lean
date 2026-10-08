import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_activeSphereCircle_measure_le
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem SphereGeom.Aux.activeSphereCircle_measure_le :
    ∀ (v : E3) (hv0 : v ≠ 0) (hv1 : ‖v‖ ≤ 1), arcMeasure {u : E3 | ‖u‖ = 1 ∧ ‖v + u‖ = 1} ≤ ENNReal.ofReal (2 * Real.pi) :=
  @proof_SphereGeom_Aux_activeSphereCircle_measure_le
