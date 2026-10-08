import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_standard_map
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Cylinder.standard_map :
    dOmega =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi))).map
        (fun x : ℝ × ℝ => (WithLp.toLp 2
          ![Real.sqrt (1-x.1^2) * Real.cos x.2,
            Real.sqrt (1-x.1^2) * Real.sin x.2, x.1] : E3)) :=
  @proof_SphereGeom_Aux_Cylinder_standard_map
