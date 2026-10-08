import HardSphereB5Lean.Proofs.Proof_SolidGeom_projected_sphere_tie_null
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.projected_sphere_tie_null :
    ∀ (c d : E3) (hcd : c ≠ d) (e : Fin 3 → E3) (he : Orthonormal ℝ e),
    let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
    let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
      (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
        (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
    (volume : Measure (ℝ × ℝ)) {p | p ∈ D ∧ U p ∈ Metric.sphere d 1} = 0 :=
  @proof_SolidGeom_projected_sphere_tie_null
