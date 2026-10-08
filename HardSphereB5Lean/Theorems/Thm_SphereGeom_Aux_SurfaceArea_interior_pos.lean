import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SurfaceArea_interior_pos
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

theorem SphereGeom.Aux.SurfaceArea.interior_pos :
    ∀ (A : Set E3) (hA : MeasurableSet A) (hi : (interior ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ⁻¹' A)).Nonempty), 0 < (dOmega A).toReal :=
  @proof_SphereGeom_Aux_SurfaceArea_interior_pos
