import HardSphereB5Lean.Proofs.Proof_SphereGeom_gcIntegral_one
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.gcIntegral_one :
    gcIntegral (fun _ => 1) = 2 * Real.pi :=
  @proof_SphereGeom_gcIntegral_one
