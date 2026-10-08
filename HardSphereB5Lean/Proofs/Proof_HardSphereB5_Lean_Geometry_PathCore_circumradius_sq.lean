import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner (x y : Pt) :
    dist x y ^ 2 = inner ℝ (x - y) (x - y) := by
  simp only [dist_eq_norm, real_inner_self_eq_norm_sq]
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_expand (x y : Pt) :
    dist x y ^ 2 = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm y x]
  ring
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq_of_deps {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    ∃ O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s) := by
  let u : Pt := c 1 - c 0
  let v : Pt := c 2 - c 0
  let w : Pt := c 3 - c 0
  have huu : inner ℝ u u = 1 := by
    rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner]
    simpa only [q, u, dist_comm] using hc.q01
  have hvv : inner ℝ v v = 1 := by
    rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner]
    simpa only [q, v, dist_comm] using hc.q02
  have hww : inner ℝ w w = Y := by
    rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner]
    simpa only [q, w, dist_comm] using hc.q03
  have huv : inner ℝ u v = 1 - X / 2 := by
    have hdist : dist u v ^ 2 = X := by
      simpa only [u, v, q, dist_sub_right] using hc.q12
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_expand, huu, hvv] at hdist
    linarith
  have huw : inner ℝ u w = Y / 2 := by
    have hdist : dist u w ^ 2 = 1 := by
      simpa only [u, w, q, dist_sub_right] using hc.q13
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_expand, huu, hww] at hdist
    linarith
  have hvw : inner ℝ v w = (1 + Y - s) / 2 := by
    have hdist : dist v w ^ 2 = s := by
      simpa only [v, w, q, dist_sub_right] using hc.q23
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_expand, hvv, hww] at hdist
    linarith
  have hvu : inner ℝ v u = 1 - X / 2 := by exact (real_inner_comm _ _).trans huv
  have hwu : inner ℝ w u = Y / 2 := by exact (real_inner_comm _ _).trans huw
  have hwv : inner ℝ w v = (1 + Y - s) / 2 := by exact (real_inner_comm _ _).trans hvw
  have hH : Hpoly X Y s ≠ 0 := ne_of_gt hc.H_pos
  let a : ℝ := (-X * Y ^ 2 + X * Y * s + X * Y - Y * s + Y - s ^ 2 + 2 * s - 1) /
    (2 * Hpoly X Y s)
  let b : ℝ := Y * (-X * Y + 2 * X + s - 1) / (2 * Hpoly X Y s)
  let d : ℝ := X * (-X * Y + 2 * Y + s - 1) / (2 * Hpoly X Y s)
  let z : Pt := a • u + b • v + d • w
  have hzu : inner ℝ z u = 1 / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huu, hvu, hwu]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzv : inner ℝ z v = 1 / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huv, hvv, hwv]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzw : inner ℝ z w = Y / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huw, hvw, hww]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzz : inner ℝ z z = 1 - P4poly X Y s / (4 * Hpoly X Y s) := by
    change inner ℝ z (a • u + b • v + d • w) = _
    simp only [inner_add_right, real_inner_smul_right, hzu, hzv, hzw]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly P4poly
    ring
  refine ⟨z + c 0, ?_⟩
  intro i
  fin_cases i
  · change dist (z + c 0) (c 0) ^ 2 = _
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner, add_sub_cancel_right]
    exact hzz
  · change dist (z + c 0) (c 1) ^ 2 = _
    have hh : z + c 0 - c 1 = z - u := by dsimp [u]; abel
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner, hh]
    simp only [inner_sub_left, inner_sub_right]
    have hsym : inner ℝ u z = 1 / 2 := (real_inner_comm _ _).trans hzu
    rw [hzu, hsym, huu, hzz]
    ring
  · change dist (z + c 0) (c 2) ^ 2 = _
    have hh : z + c 0 - c 2 = z - v := by dsimp [v]; abel
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner, hh]
    simp only [inner_sub_left, inner_sub_right]
    have hsym : inner ℝ v z = 1 / 2 := (real_inner_comm _ _).trans hzv
    rw [hzv, hsym, hvv, hzz]
    ring
  · change dist (z + c 0) (c 3) ^ 2 = _
    have hh : z + c 0 - c 3 = z - w := by dsimp [w]; abel
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_sqdist_inner, hh]
    simp only [inner_sub_left, inner_sub_right]
    have hsym : inner ℝ w z = Y / 2 := (real_inner_comm _ _).trans hzw
    rw [hzw, hsym, hww, hzz]
    ring
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) :
    ∃ O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s) := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq_of_deps c X Y s hc

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq
