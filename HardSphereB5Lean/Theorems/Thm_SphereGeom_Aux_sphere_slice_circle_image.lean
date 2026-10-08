import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_sphere_slice_circle_image
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.Aux.sphere_slice_circle_image :
    ∀ (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (z : ℝ) (hz : |z| < 1), {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = z} = circlePt (z • E 2) (E 0) (E 1) (Real.sqrt (1 - z ^ 2)) '' Set.Icc (0 : ℝ) (2 * Real.pi) :=
  @proof_SphereGeom_Aux_sphere_slice_circle_image
