import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_jacobian
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Cylinder.jacobian :
    ∀ (x : Fin 3 → ℝ) (hx : -1 < x 1 ∧ x 1 < 1),
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    (Matrix.det (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (fderiv ℝ f x).toLinearMap)) = -(x 0)^2 :=
  @proof_SphereGeom_Aux_Cylinder_jacobian
