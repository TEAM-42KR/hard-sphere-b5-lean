import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

private lemma q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

theorem proof_HardSphereB5_Lean_Geometry_PathCore_weighted_apex_coefficient {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) :
  Lapex c 3 0 2 = (2*Y*s-Y^2-s^2+Y+s)/(4*Y*s-(Y+s-1)^2) := by
  have h30 : q c 3 0=Y := by rw [q_symm', hc.q03]
  have h32 : q c 3 2=s := by rw [q_symm', hc.q23]
  simp only [Lapex, Deltaf, DeltaT, h30, h32, hc.q02]
  congr 1 <;> ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_weighted_apex_coefficient
