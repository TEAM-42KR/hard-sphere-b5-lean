import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_realizable_of_deps (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) : ∃ c : Fin 4 → Pt, IsPathConfig c X Y s := by
  have hr : 0 < X - X ^ 2 / 4 := by
    nlinarith [mul_pos hX (show 0 < 4 - X by linarith)]
  let b : ℝ := √(X - X ^ 2 / 4)
  have hb : 0 < b := Real.sqrt_pos.2 hr
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hb2 : b ^ 2 = X - X ^ 2 / 4 := Real.sq_sqrt hr.le
  let t : ℝ := 1 - s + X * Y / 2
  let f : ℝ := t / (2 * b)
  let z : ℝ := √(Hpoly X Y s / (4 * b ^ 2))
  have hz2 : z ^ 2 = Hpoly X Y s / (4 * b ^ 2) := by
    apply Real.sq_sqrt
    exact (div_pos hH (mul_pos (by norm_num) (sq_pos_of_pos hb))).le
  have hf2 : f ^ 2 = t ^ 2 / (4 * b ^ 2) := by
    dsimp [f]
    field_simp [hb0]
    <;> ring
  have hbf : 2 * b * f = 1 - s + X * Y / 2 := by
    dsimp [f, t]
    field_simp [hb0]
  have hid : t ^ 2 + Hpoly X Y s = (Y - Y ^ 2 / 4) * (4 * b ^ 2) := by
    dsimp [t]
    rw [hb2]
    unfold Hpoly
    ring
  have hd : (Y / 2) ^ 2 + f ^ 2 + z ^ 2 = Y := by
    calc
      (Y / 2) ^ 2 + f ^ 2 + z ^ 2 =
          (Y / 2) ^ 2 + (t ^ 2 + Hpoly X Y s) / (4 * b ^ 2) := by
            rw [hf2, hz2]
            ring
      _ = Y := by
        rw [hid]
        field_simp [hb0]
        <;> ring
  have hdist (u v : Pt) : dist u v ^ 2 =
      (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, PiLp.sub_apply, add_assoc]
  let c : Fin 4 → Pt := ![0, WithLp.toLp 2 ![1, 0, 0],
    WithLp.toLp 2 ![1 - X / 2, b, 0], WithLp.toLp 2 ![Y / 2, f, z]]
  refine ⟨c, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hX, hX1, hY, hY1, hH⟩

  · unfold q
    rw [hdist]
    change (0-1 : ℝ)^2 + (0-0)^2 + (0-0)^2 = 1
    norm_num
  · unfold q
    rw [hdist]
    change (0-(1-X/2))^2 + (0-b)^2 + (0-0)^2 = 1
    nlinarith only [hb2]
  · unfold q
    rw [hdist]
    change (0-Y/2)^2 + (0-f)^2 + (0-z)^2 = Y
    nlinarith only [hd]
  · unfold q
    rw [hdist]
    change (1-(1-X/2))^2 + (0-b)^2 + (0-0)^2 = X
    nlinarith only [hb2]
  · unfold q
    rw [hdist]
    change (1-Y/2)^2 + (0-f)^2 + (0-z)^2 = 1
    nlinarith only [hd]
  · unfold q
    rw [hdist]
    change (1-X/2-Y/2)^2 + (b-f)^2 + (0-z)^2 = s
    nlinarith only [hb2, hd, hbf]
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_realizable {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s) :
    ∃ c : Fin 4 → Pt, IsPathConfig c X Y s := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_realizable_of_deps X Y s hX hX1 hY hY1 hH

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_realizable
