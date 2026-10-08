import HardSphereB5Lean.Proofs.Proof_SolidGeom_sphere_upper_patch_transport
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical

theorem SolidGeom.sphere_upper_patch_transport :
    ∀ (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (A : Set E3) (hA : MeasurableSet A) (F : ℝ × ℝ → ℝ) (hF : Continuous F),
    let P : E3 → ℝ × ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
    let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
    let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
      (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
        (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
    let H : Set E3 := {x | 0 < inner ℝ (e 2) (x - c)}
    (∫ x in A ∩ H, F (P x) * inner ℝ (e 2) (x - c) ∂sphereMeasure c) =
      ∫ p in D, if U p ∈ A then F p else 0 :=
  @proof_SolidGeom_sphere_upper_patch_transport
