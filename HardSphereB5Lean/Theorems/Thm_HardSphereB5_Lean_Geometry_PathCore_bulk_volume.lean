import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_bulk_volume
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.bulk_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s), vol c Finset.univ = (1 / 2) * ∑ l, vol c (faceSet l) - 4 * π / 3
      + (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * phiE c i j else 0)
      - √(Hpoly X Y s) / 12 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_bulk_volume
