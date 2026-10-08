import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.coordinate_realization :
    ∀ {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s), IsPathConfig (canonicalCenters X Y s) X Y s ∧
  ∃ χ : ℝ, 0 < χ ∧ χ < π ∧ s = a0 X Y - b0 X Y * Real.cos χ ∧
    Hpoly X Y s = (b0 X Y) ^ 2 - (a0 X Y - s) ^ 2 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization
