import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

private lemma q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private def Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]

private def gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2

private def faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)

private lemma face_polys (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    let i := (faceVerts l).1
    let j := (faceVerts l).2.1
    let k := (faceVerts l).2.2
    Qface c l = Qpoly X Y s l ∧
    Deltaf c i j k = Dpoly X Y s l ∧
    faceAPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Apoly X Y s l ∧
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Hpoly X Y s := by
  have h10 : q c 1 0 = 1 := by rw [q_symm', hc.q01]
  have h20 : q c 2 0 = 1 := by rw [q_symm', hc.q02]
  have h30 : q c 3 0 = Y := by rw [q_symm', hc.q03]
  have h21 : q c 2 1 = X := by rw [q_symm', hc.q12]
  have h31 : q c 3 1 = 1 := by rw [q_symm', hc.q13]
  have h32 : q c 3 2 = s := by rw [q_symm', hc.q23]
  fin_cases l <;>
    dsimp [faceVerts, Qface, Qf, Deltaf, QT, DeltaT, Dpoly, Qpoly, Apoly,
      faceAPoly, gramPoly, Hpoly] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hc.q01, hc.q02, hc.q03, hc.q12, hc.q13, hc.q23,
      h10, h20, h30, h21, h31, h32] <;> ring

private lemma cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, Dpoly, DeltaT, P4poly] <;> ring

theorem proof_HardSphereB5_Lean_Geometry_PathCore_face_circumradius_certificate {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4) :
  (Apoly X Y s l)^2 - 4*Hpoly X Y s*Qface c l =
    -Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 * P4poly X Y s := by
  have hp := face_polys c X Y s hc l
  rw [hp.1,hp.2.1]
  exact cayley_menger_face_identity X Y s l

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_face_circumradius_certificate
