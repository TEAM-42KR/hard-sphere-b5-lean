import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Archimedes_cone_volume_axis0_Iic
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem SphereGeom.Aux.Archimedes.cone_volume_axis0_Iic :
    ∀ (h : ℝ), (volume : Measure E3) (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
        {u : Metric.sphere (0 : E3) 1 | inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (u : E3) ≤ h})) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) :=
  @proof_SphereGeom_Aux_Archimedes_cone_volume_axis0_Iic
