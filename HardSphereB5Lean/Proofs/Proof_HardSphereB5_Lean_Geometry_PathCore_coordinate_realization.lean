import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization_of_deps (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s) :
  IsPathConfig (canonicalCenters X Y s) X Y s ∧
  ∃ χ : ℝ, 0 < χ ∧ χ < π ∧ s = a0 X Y - b0 X Y * Real.cos χ ∧
    Hpoly X Y s = (b0 X Y) ^ 2 - (a0 X Y - s) ^ 2 := by
  have hrX : 0 < X * (1 - X / 4) := mul_pos hX (by linarith only [hX1])
  have hrY : 0 < Y * (1 - Y / 4) := mul_pos hY (by linarith only [hY1])
  have hx : 0 < rX X := Real.sqrt_pos.2 hrX
  have hy : 0 < rX Y := Real.sqrt_pos.2 hrY
  have hx0 : rX X ≠ 0 := ne_of_gt hx
  have hx2 : (rX X) ^ 2 = X * (1 - X / 4) := Real.sq_sqrt hrX.le
  have hy2 : (rX Y) ^ 2 = Y * (1 - Y / 4) := Real.sq_sqrt hrY.le
  have hb : 0 < b0 X Y := mul_pos (mul_pos (by norm_num) hx) hy
  have hB : Hpoly X Y s = (b0 X Y) ^ 2 - (a0 X Y - s) ^ 2 := by
    dsimp [b0]
    rw [mul_pow, mul_pow, hx2, hy2]
    unfold a0 Hpoly
    ring
  let f : ℝ := (a0 X Y - s) / (2 * rX X)
  let z : ℝ := √(Hpoly X Y s) / (2 * rX X)
  have hf2 : f ^ 2 = (a0 X Y - s) ^ 2 / (4 * (rX X) ^ 2) := by
    dsimp [f]
    rw [div_pow, mul_pow]
    norm_num
  have hz2 : z ^ 2 = Hpoly X Y s / (4 * (rX X) ^ 2) := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt hH.le, mul_pow]
    norm_num
  have hrf : 2 * rX X * f = 1 - s + X * Y / 2 := by
    dsimp [f, a0]
    field_simp [hx0]
    <;> ring
  have hAlg : (a0 X Y - s) ^ 2 + Hpoly X Y s =
      (Y - Y ^ 2 / 4) * (4 * (rX X) ^ 2) := by
    rw [hx2]
    unfold a0 Hpoly
    ring
  have hD : f ^ 2 + z ^ 2 + (Y / 2) ^ 2 = Y := by
    calc
      f ^ 2 + z ^ 2 + (Y / 2) ^ 2 =
          ((a0 X Y - s) ^ 2 + Hpoly X Y s) / (4 * (rX X) ^ 2) + (Y / 2) ^ 2 := by
            rw [hf2, hz2]
            ring
      _ = Y := by
        rw [hAlg]
        field_simp [hx0]
        <;> ring
  have hd (u v : Pt) : dist u v ^ 2 =
      (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, PiLp.sub_apply, add_assoc]
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hX, hX1, hY, hY1, hH⟩
    · unfold q
      rw [hd]
      change (0 - 0 : ℝ) ^ 2 + (0 - 0 : ℝ) ^ 2 + (0 - 1 : ℝ) ^ 2 = 1
      norm_num
    · unfold q
      rw [hd]
      change (0 - rX X) ^ 2 + (0 - 0 : ℝ) ^ 2 + (0 - (1 - X / 2)) ^ 2 = 1
      nlinarith only [hx2]
    · unfold q
      rw [hd]
      change (0 - f) ^ 2 + (0 - z) ^ 2 + (0 - Y / 2) ^ 2 = Y
      nlinarith only [hD]
    · unfold q
      rw [hd]
      change (0 - rX X) ^ 2 + (0 - 0 : ℝ) ^ 2 + (1 - (1 - X / 2)) ^ 2 = X
      nlinarith only [hx2]
    · unfold q
      rw [hd]
      change (0 - f) ^ 2 + (0 - z) ^ 2 + (1 - Y / 2) ^ 2 = 1
      nlinarith only [hD]
    · unfold q
      rw [hd]
      change (rX X - f) ^ 2 + (0 - z) ^ 2 + ((1 - X / 2) - Y / 2) ^ 2 = s
      nlinarith only [hx2, hD, hrf]
  · have ht : |a0 X Y - s| < b0 X Y := by
      simpa only [abs_of_pos hb] using
        (sq_lt_sq.1 (show (a0 X Y - s) ^ 2 < (b0 X Y) ^ 2 by linarith only [hH, hB]))
    obtain ⟨htl, htr⟩ := abs_lt.1 ht
    have hu0 : -1 < (a0 X Y - s) / b0 X Y := (lt_div_iff₀ hb).2 (by simpa using htl)
    have hu1 : (a0 X Y - s) / b0 X Y < 1 := (div_lt_iff₀ hb).2 (by simpa using htr)
    refine ⟨Real.arccos ((a0 X Y - s) / b0 X Y), Real.arccos_pos.2 hu1,
      Real.arccos_lt_pi.2 hu0, ?_, hB⟩
    rw [Real.cos_arccos hu0.le hu1.le]
    field_simp [ne_of_gt hb]
    <;> ring
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s) :
  IsPathConfig (canonicalCenters X Y s) X Y s ∧
  ∃ χ : ℝ, 0 < χ ∧ χ < π ∧ s = a0 X Y - b0 X Y * Real.cos χ ∧
    Hpoly X Y s = (b0 X Y) ^ 2 - (a0 X Y - s) ^ 2 := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization_of_deps X Y s hX hX1 hY hY1 hH

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization
