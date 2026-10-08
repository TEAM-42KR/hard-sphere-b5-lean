import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_triple_retention_test
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.triple_retention_test :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k l : Fin 4)
  (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
  (ε : ℝ) (hε : ε=1 ∨ ε= -1), dist (triplePoint c i j k ε) (c l) ^ 2 - 1 =
    q c i l - 2*inner ℝ (c l-c i) (faceCircRel c i j k) -
      ε * 4*√(Qf c i j k) / Deltaf c i j k * det3 (c j-c i) (c k-c i) (c l-c i) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_triple_retention_test
