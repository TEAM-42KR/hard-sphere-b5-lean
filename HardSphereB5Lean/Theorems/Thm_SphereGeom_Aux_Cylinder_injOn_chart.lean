import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_injOn_chart
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Cylinder.injOn_chart :
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    Set.InjOn f {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧ 0 < x 2 ∧ x 2 < 2 * Real.pi} :=
  @proof_SphereGeom_Aux_Cylinder_injOn_chart
