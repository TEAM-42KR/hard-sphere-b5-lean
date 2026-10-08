import HardSphereB5Lean.Proofs.Proof_SolidGeom_sphereMeasure_sphere_inter_null
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.sphereMeasure_sphere_inter_null :
    ∀ (c d : E3) (hcd : c ≠ d), sphereMeasure c (Metric.sphere d 1) = 0 :=
  @proof_SolidGeom_sphereMeasure_sphere_inter_null
