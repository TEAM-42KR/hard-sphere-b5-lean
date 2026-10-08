import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_projection
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_projection :
    ∀ (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c) (hd : 0 < 1 - c ^ 2),
    let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
    inner ℝ x p = a ∧ inner ℝ y p = b ∧
    ‖p‖ ^ 2 = (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_projection
