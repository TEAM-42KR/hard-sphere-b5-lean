import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_bothAngleSheetsMeasure
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton
open scoped ENNReal
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsCroftonMeasure (X Y : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1) :
    let μ := (volume.restrict {s : ℝ | 0 < Hpoly X Y s}).withDensity
      (fun s => ENNReal.ofReal (1 / Real.sqrt (Hpoly X Y s)))
    μ.map (fun s => chiPlus X Y s) + μ.map (fun s => -chiPlus X Y s) =
      volume.restrict (Set.Ioo (-Real.pi) Real.pi) := by
  have hradX : 0 < X * (1-X/4) := mul_pos hX0 (by linarith)
  have hradY : 0 < Y * (1-Y/4) := mul_pos hY0 (by linarith)
  have hx := Real.sq_sqrt hradX.le
  have hy := Real.sq_sqrt hradY.le
  have hb : 0 < b0 X Y := by
    unfold b0
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hradX))
      (Real.sqrt_pos.mpr hradY)
  have hpoly (s : ℝ) : Hpoly X Y s = (b0 X Y)^2 - (s-a0 X Y)^2 := by
    unfold Hpoly b0 a0
    simp only [mul_pow, hx, hy]
    ring
  have hdomain : {s : ℝ | 0 < Hpoly X Y s} = Set.Ioo (a0 X Y - b0 X Y) (a0 X Y + b0 X Y) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, hpoly]
    constructor
    · intro h
      have hs : |s-a0 X Y| < b0 X Y := (sq_lt_sq₀ (abs_nonneg _) hb.le).mp (by
        simpa only [sq_abs] using (sub_pos.mp h))
      rw [abs_lt] at hs
      constructor <;> linarith [hs.1, hs.2]
    · intro hs
      have hl : 0 < b0 X Y + (s-a0 X Y) := by linarith [hs.1]
      have hr : 0 < b0 X Y - (s-a0 X Y) := by linarith [hs.2]
      nlinarith [mul_pos hl hr]
  dsimp only
  rw [hdomain]
  simp only [hpoly, chiPlus]
  exact HardSphereB5.SphericalCrofton.Aux.Flat.bothAngleSheetsMeasure (a0 X Y) (b0 X Y) hb
