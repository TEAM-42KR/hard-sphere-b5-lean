import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_dihedral_identity
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.near_dihedral_identity :
    ∀ (X Y s : ℝ), (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 + 4 * s * Hpoly X Y s =
      (4 * s - (1 + s - Y) ^ 2) * (4 * s * X - (X + s - 1) ^ 2) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_dihedral_identity
