import HardSphereB5Lean.Proofs.Proof_SphereGeom_cross_vec_triple
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.cross_vec_triple :
    ∀ (u v w : E3), cross u (cross v w) = (inner ℝ u w) • v - (inner ℝ v u) • w :=
  @proof_SphereGeom_cross_vec_triple
