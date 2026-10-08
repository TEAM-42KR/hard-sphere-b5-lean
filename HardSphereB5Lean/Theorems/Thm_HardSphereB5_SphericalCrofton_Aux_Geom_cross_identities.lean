import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_cross_identities
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open SphereGeom
open HardSphereB5.Lean (Pt)

theorem HardSphereB5.SphericalCrofton.Aux.Geom.cross_identities :
    ∀ (x y u : Pt), inner ℝ x (cross x y) = 0 ∧ inner ℝ y (cross x y) = 0 ∧
    inner ℝ (cross x y) (cross x y) = inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 ∧
    (inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2) • u =
      (inner ℝ y y * inner ℝ x u - inner ℝ x y * inner ℝ y u) • x +
      (inner ℝ x x * inner ℝ y u - inner ℝ x y * inner ℝ x u) • y +
      (inner ℝ (cross x y) u) • cross x y :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_cross_identities
