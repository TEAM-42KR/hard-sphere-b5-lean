import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_product
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_product :
    ∀ (p p' D q : Pt) (r : ℝ)
  (hD : D = midpoint ℝ p p' + r • q), inner ℝ (p - D) (NAv p p') * inner ℝ (p' - D) (NBv p p') =
    r ^ 2 * inner ℝ q (NAv p p') * inner ℝ q (NBv p p') :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_product
