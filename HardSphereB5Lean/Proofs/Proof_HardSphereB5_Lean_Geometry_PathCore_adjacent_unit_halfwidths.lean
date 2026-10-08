import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

private lemma q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

theorem proof_HardSphereB5_Lean_Geometry_PathCore_adjacent_unit_halfwidths {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) :
  betaA c 0 1 2=betaA c 0 2 1 ∧ betaA c 0 1 3=betaA c 1 3 0 := by
  have h10 : q c 1 0=1 := by rw [q_symm', hc.q01]
  have h30 : q c 3 0=Y := by rw [q_symm', hc.q03]
  have h21 : q c 2 1=X := by rw [q_symm', hc.q12]
  have h31 : q c 3 1=1 := by rw [q_symm', hc.q13]
  have hQ1 : Qf c 0 1 2=Qf c 0 2 1 := by
    simp only [Qf, QT, Deltaf, DeltaT, hc.q01, hc.q02, hc.q12, h21]
  have hQ2 : Qf c 0 1 3=Qf c 1 3 0 := by
    simp only [Qf, QT, Deltaf, DeltaT, hc.q01, hc.q03, hc.q13, h10, h30]
    ring
  constructor
  · simp only [betaA, hQ1, hc.q01, hc.q02, hc.q12, h21]
  · simp only [betaA, hQ2, hc.q01, hc.q03, hc.q13, h10, h30]
    congr 2 <;> ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_adjacent_unit_halfwidths
