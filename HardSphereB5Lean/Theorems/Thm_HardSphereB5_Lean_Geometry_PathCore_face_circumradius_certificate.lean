import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_face_circumradius_certificate
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.face_circumradius_certificate :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4), (Apoly X Y s l)^2 - 4*Hpoly X Y s*Qface c l =
    -Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 * P4poly X Y s :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_face_circumradius_certificate
