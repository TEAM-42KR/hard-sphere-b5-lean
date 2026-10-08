import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_face_circumcenter_identities
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.face_circumcenter_identities :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k), inner ℝ (c j-c i) (faceCircRel c i j k) = q c i j / 2 ∧
  inner ℝ (c k-c i) (faceCircRel c i j k) = q c i k / 2 ∧
  ‖faceCircRel c i j k‖ ^ 2 = q c i j * q c i k * q c j k / Deltaf c i j k ∧
  (∀ ε : ℝ, (ε=1 ∨ ε= -1) → ∀ m ∈ ({i,j,k} : Finset (Fin 4)), dist (triplePoint c i j k ε) (c m)=1) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_face_circumcenter_identities
