import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_circle_image
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.circle_image :
    ∀ (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]), circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p :=
  @proof_SphereGeom_Aux_Pair_circle_image
