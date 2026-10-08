import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_Qface_eq_poly {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4) : Qface c l = Qpoly X Y s l := by
  have h01 := hc.q01
  have h02 := hc.q02
  have h03 := hc.q03
  have h12 := hc.q12
  have h13 := hc.q13
  have h23 := hc.q23
  fin_cases l <;>
    simp [Qface, faceVerts, Qf, QT, DeltaT, Qpoly, h01, h02, h03, h12, h13, h23] <;> ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_Qface_eq_poly
