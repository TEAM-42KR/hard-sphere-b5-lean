import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_angle_average
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_angle_average :
    ∀ (f : E3 → ENNReal) (z t : ℝ), (∫⁻ φ in Set.Ico 0 (2 * Real.pi), f (WithLp.toLp 2
      ![-Real.cos t * Real.sin φ - z * Real.sin t * Real.cos φ,
        Real.cos t * Real.cos φ - z * Real.sin t * Real.sin φ,
        Real.sqrt (1-z^2) * Real.sin t] : E3)) =
    (∫⁻ φ in Set.Ico 0 (2 * Real.pi), f (WithLp.toLp 2
      ![Real.sqrt (z^2 * Real.sin t^2 + Real.cos t^2) * Real.cos φ,
        Real.sqrt (z^2 * Real.sin t^2 + Real.cos t^2) * Real.sin φ,
        Real.sqrt (1-z^2) * Real.sin t] : E3)) :=
  @proof_SphereGeom_Aux_Pair_cylinder_angle_average
