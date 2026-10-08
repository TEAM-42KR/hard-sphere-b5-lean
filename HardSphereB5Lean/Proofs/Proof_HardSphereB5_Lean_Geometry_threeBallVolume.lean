import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Theorems.Thm_SolidGeom_volume_triple_ball
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean
set_option maxHeartbeats 1000000

private theorem pathFaceQCertificate (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 < 4 * dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2
        - (dist (c i) (c j) ^ 2 + dist (c i) (c k) ^ 2 - dist (c j) (c k) ^ 2) ^ 2
        - dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2 * dist (c j) (c k) ^ 2 := by
  have hs : 0 ≤ s := by rw [← h23]; exact sq_nonneg _
  have hQX : 0 < X * (3-X) := mul_pos hX0 (by linarith)
  have hQY : 0 < Y * (3-Y) := mul_pos hY0 (by linarith)
  have hpY : 0 < Y * (1-X) * (s+(1-X)+(1-Y)) :=
    mul_pos (mul_pos hY0 (by linarith)) (by linarith)
  have hpX : 0 < X * (1-Y) * (s+(1-X)+(1-Y)) :=
    mul_pos (mul_pos hX0 (by linarith)) (by linarith)
  have hQSX : 0 < -X^2+X*s+2*X-s^2+2*s-1 := by nlinarith only [hH,hpX]
  have hQSY : 0 < -Y^2+Y*s+2*Y-s^2+2*s-1 := by nlinarith only [hH,hpY]
  have h10 : dist (c 1) (c 0)^2 = 1 := by simpa only [dist_comm] using h01
  have h20 : dist (c 2) (c 0)^2 = 1 := by simpa only [dist_comm] using h02
  have h30 : dist (c 3) (c 0)^2 = Y := by simpa only [dist_comm] using h03
  have h21 : dist (c 2) (c 1)^2 = X := by simpa only [dist_comm] using h12
  have h31 : dist (c 3) (c 1)^2 = 1 := by simpa only [dist_comm] using h13
  have h32 : dist (c 3) (c 2)^2 = s := by simpa only [dist_comm] using h23
  have hf (u : Fin 4) : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
  rcases hf i with rfl | rfl | rfl | rfl <;>
    rcases hf j with rfl | rfl | rfl | rfl <;>
      rcases hf k with rfl | rfl | rfl | rfl
  all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim | skip
  all_goals simp only [h01,h02,h03,h12,h13,h23,h10,h20,h30,h21,h31,h32]
  all_goals nlinarith only [hQX,hQY,hQSX,hQSY]

theorem proof_HardSphereB5_Lean_Geometry_threeBallVolume (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let a := dist (c i) (c j) ^ 2
    let b := dist (c i) (c k) ^ 2
    let cc := dist (c j) (c k) ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    let g : ℝ → ℝ := fun d => d - d ^ 3 / 12
    (volume (Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1)).toReal =
      2 * π - 2 / 3 * (Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
          + Complex.arg ⟨2 * (a + cc - b) - a * cc, 2 * √Q⟩
          + Complex.arg ⟨2 * (b + cc - a) - b * cc, 2 * √Q⟩)
        - (g (√a) * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
          + g (√b) * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩
          + g (√cc) * Complex.arg ⟨√cc * (a + b - cc), 2 * √Q⟩)
        + √Q / 6 := by
  have hQ := pathFaceQCertificate c X Y s h01 h02 h03 h12 h13 h23 hX0 hX1 hY0 hY1 hH i j k hij hik hjk
  simpa using SolidGeom.volume_triple_ball (![c i, c j, c k] : Fin 3 → SphereGeom.E3)
    (by simpa using hQ)

#print axioms proof_HardSphereB5_Lean_Geometry_threeBallVolume
