import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_map_cylinder
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_map_cylinder :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e), dOmega =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (1 - x.1 ^ 2) * Real.cos x.2) • e 0 +
          (Real.sqrt (1 - x.1 ^ 2) * Real.sin x.2) • e 1 + x.1 • e 2) :=
  @proof_SphereGeom_dOmega_map_cylinder
