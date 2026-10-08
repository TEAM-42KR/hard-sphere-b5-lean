import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean (Pt e)
open SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_iff :
    ∀ (p p' D : Pt) (hpp : dist p p' < 2), (dist D p = 1 ∧ dist D p' = 1) ↔ ∃ q : Pt, ‖q‖ = 1 ∧ inner ℝ q (p' - p) = 0 ∧ D = midpoint ℝ p p' + Real.sqrt (1 - dist p p' ^ 2 / 4) • q :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
