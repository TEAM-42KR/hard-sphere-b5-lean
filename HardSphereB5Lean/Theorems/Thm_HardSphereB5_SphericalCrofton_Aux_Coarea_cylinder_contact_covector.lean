import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cylinder_contact_covector
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.cylinder_contact_covector :
    ∀ (p u w : SphereGeom.E3) (htan : inner ℝ p w = 0)
    (hR : p 1 ^ 2 + p 2 ^ 2 ≠ 0),
    let R : ℝ := p 1 ^ 2 + p 2 ^ 2
    let α : ℝ := u 0 - p 0 * (p 1 * u 1 + p 2 * u 2) / R
    let β : ℝ := p 1 * u 2 - p 2 * u 1
    (α * w 0 + β * ((p 1 * w 2 - p 2 * w 1) / R) = inner ℝ u w) ∧
      (SphereGeom.cross p u) 0 = β ∧
      (p 1 * (SphereGeom.cross p u) 2 - p 2 * (SphereGeom.cross p u) 1) / R = -α :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cylinder_contact_covector
