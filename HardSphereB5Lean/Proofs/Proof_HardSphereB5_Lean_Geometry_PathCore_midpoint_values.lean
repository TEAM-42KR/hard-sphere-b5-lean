import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_midpoint_values {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) :
  let M := (1/2 : ℝ) • (c 0+c 1)
  dist M (c 0)^2=1/4 ∧ dist M (c 1)^2=1/4 ∧
  dist M (c 2)^2=(1+2*X)/4 ∧ dist M (c 3)^2=(1+2*Y)/4 := by
  let M := (1/2 : ℝ) • (c 0+c 1)
  have hm : M=midpoint ℝ (c 0) (c 1) := by simp [M, midpoint_eq_smul_add]
  have h01 : dist (c 0) (c 1)^2=1 := hc.q01
  have h02 : dist (c 0) (c 2)^2=1 := hc.q02
  have h03 : dist (c 0) (c 3)^2=Y := hc.q03
  have h12 : dist (c 1) (c 2)^2=X := hc.q12
  have h13 : dist (c 1) (c 3)^2=1 := hc.q13
  have h0 := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (c 0) (c 0) (c 1)
  have h1 := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (c 1) (c 0) (c 1)
  have h2 := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (c 2) (c 0) (c 1)
  have h3 := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (c 3) (c 0) (c 1)
  simp only [dist_self, zero_pow (by decide : 2 ≠ 0), h01, dist_comm (c 1) (c 0)] at h0 h1
  simp only [dist_comm (c 2) (c 0),dist_comm (c 2) (c 1),h02,h12,h01] at h2
  simp only [dist_comm (c 3) (c 0),dist_comm (c 3) (c 1),h03,h13,h01] at h3
  change dist M (c 0)^2=1/4 ∧ dist M (c 1)^2=1/4 ∧ dist M (c 2)^2=(1+2*X)/4 ∧ dist M (c 3)^2=(1+2*Y)/4
  rw [hm]
  simp only [dist_comm (midpoint ℝ (c 0) (c 1))]
  constructor
  · nlinarith [h0]
  constructor
  · nlinarith [h1]
  constructor <;> nlinarith

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_midpoint_values
