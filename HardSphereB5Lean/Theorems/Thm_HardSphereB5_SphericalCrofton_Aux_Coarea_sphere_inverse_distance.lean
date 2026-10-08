import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_inverse_distance
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.sphere_inverse_distance :
    ∀ (c p : E3) (hp : ‖p - c‖ ≤ 1), Integrable (fun v : E3 => (dist p v)⁻¹) (sphereMeasure c) ∧
      (∫ v : E3, (dist p v)⁻¹ ∂sphereMeasure c) = 4 * Real.pi :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_inverse_distance
