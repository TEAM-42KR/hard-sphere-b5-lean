import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_vertices
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_vertices :
    ∀ (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c)
    (hd : 0 < 1 - c ^ 2)
    (hq : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1), ∃ V W : Pt, V ≠ W ∧ {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} = {V, W} :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_vertices
