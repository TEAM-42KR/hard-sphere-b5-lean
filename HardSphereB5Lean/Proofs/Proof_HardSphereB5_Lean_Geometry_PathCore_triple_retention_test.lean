import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_face_circumcenter_identities
set_option autoImplicit false

noncomputable section
open MeasureTheory Real
private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_triple_retention_test : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace

private def HardSphereB5.Lean.Geometry.PathCore.FaceCircumcenterIdentitiesStmt : Prop :=
  ∀ {c : Fin 4 → Pt} {X Y s : ℝ}, IsPathConfig c X Y s →
  ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
  inner ℝ (c j-c i) (faceCircRel c i j k) = q c i j / 2 ∧
  inner ℝ (c k-c i) (faceCircRel c i j k) = q c i k / 2 ∧
  ‖faceCircRel c i j k‖ ^ 2 = q c i j * q c i k * q c j k / Deltaf c i j k ∧
  (∀ ε : ℝ, (ε=1 ∨ ε= -1) → ∀ m ∈ ({i,j,k} : Finset (Fin 4)),
    dist (triplePoint c i j k ε) (c m)=1)

private theorem HardSphereB5.Lean.Geometry.PathCore.triple_retention_test_of_deps (h1 : FaceCircumcenterIdentitiesStmt)
    {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    dist (triplePoint c i j k ε) (c l) ^ 2 - 1 =
      q c i l - 2*inner ℝ (c l-c i) (faceCircRel c i j k) -
        ε * 4*√(Qf c i j k) / Deltaf c i j k *
          det3 (c j-c i) (c k-c i) (c l-c i) := by
  have ht : dist (triplePoint c i j k ε) (c i) = 1 :=
    (h1 hc i j k hij hik hjk).2.2.2 ε hε i (by simp)
  have hx : triplePoint c i j k ε - c i =
      faceCircRel c i j k + (ε * 2 * √(Qf c i j k) / Deltaf c i j k) •
        cross (c j - c i) (c k - c i) := by
    unfold triplePoint
    abel
  have hz : triplePoint c i j k ε - c l =
      (triplePoint c i j k ε - c i) - (c l - c i) := by abel
  have hn : ‖triplePoint c i j k ε - c i‖ ^ 2 = 1 := by
    rw [← dist_eq_norm, ht]
    norm_num
  have hq : ‖c l - c i‖ ^ 2 = q c i l := by
    rw [← dist_eq_norm, dist_comm]
    rfl
  rw [dist_eq_norm, hz, norm_sub_sq_real, hn, hq]
  rw [hx, inner_add_left, real_inner_smul_left,
    real_inner_comm (faceCircRel c i j k) (c l-c i)]
  simp only [det3]
  ring

end

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}
theorem proof_HardSphereB5_Lean_Geometry_PathCore_triple_retention_test (hc : IsPathConfig c X Y s) (i j k l : Fin 4)
  (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
  (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
  dist (triplePoint c i j k ε) (c l) ^ 2 - 1 =
    q c i l - 2*inner ℝ (c l-c i) (faceCircRel c i j k) -
      ε * 4*√(Qf c i j k) / Deltaf c i j k * det3 (c j-c i) (c k-c i) (c l-c i) := by
  exact triple_retention_test_of_deps face_circumcenter_identities hc i j k l hij hik hil hjk hjl hkl ε hε
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_triple_retention_test
