import HardSphereB5Lean.Proofs.Proof_SphereGeom_sphereMeasure_univ
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.sphereMeasure_univ :
    ∀ (c : E3), sphereMeasure c Set.univ = ENNReal.ofReal (4 * Real.pi) :=
  @proof_SphereGeom_sphereMeasure_univ
