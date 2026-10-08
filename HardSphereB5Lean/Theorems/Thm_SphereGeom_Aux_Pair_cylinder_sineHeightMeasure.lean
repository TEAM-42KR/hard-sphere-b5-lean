import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_sineHeightMeasure
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_sineHeightMeasure :
    (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod
      ((volume : Measure ℝ).restrict (Set.Ico 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ => Real.sqrt (1-x.1^2) * Real.sin x.2) =
    ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1) :=
  @proof_SphereGeom_Aux_Pair_cylinder_sineHeightMeasure
