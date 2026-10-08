import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D),
    let x := nAv D
    let y := nBv D
    let a := ‖D‖ / 2
    let b := ‖D - e‖ / 2
    let c := inner ℝ x y
    ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ 0 < 1 - c ^ 2 ∧ 0 < a ∧ 0 < b ∧
    0 ≤ a - c * b ∧ 0 ≤ b - c * a ∧
    (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = (Rc ‖D‖ ‖D - e‖) ^ 2 ∧
    0 ≤ Rc ‖D‖ ‖D - e‖ ∧
    SigmaD D = {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u} ∧
    vertsD D = {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
