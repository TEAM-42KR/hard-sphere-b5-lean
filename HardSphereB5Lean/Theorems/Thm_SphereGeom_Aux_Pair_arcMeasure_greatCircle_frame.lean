import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame :
    ∀ (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]), arcMeasure.restrict (greatCircle p) =
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)).map (circlePt 0 v₁ v₂ 1) :=
  @proof_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
