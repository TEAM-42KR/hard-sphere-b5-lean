import HardSphereB5Lean.Proofs.Proof_SolidGeom_sphere_upper_projection
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.sphere_upper_projection :
    ∀ (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e), Measure.map (fun x : E3 => (inner ℝ (e 0) x, inner ℝ (e 1) x))
      (((sphereMeasure c).restrict {x : E3 | 0 < inner ℝ (e 2) (x - c)}).withDensity
        (fun x => ENNReal.ofReal (inner ℝ (e 2) (x - c)))) =
    (volume : Measure (ℝ × ℝ)).restrict
      {p : ℝ × ℝ | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1} :=
  @proof_SolidGeom_sphere_upper_projection
