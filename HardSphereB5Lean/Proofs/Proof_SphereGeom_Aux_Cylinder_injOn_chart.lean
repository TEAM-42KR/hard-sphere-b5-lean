import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_norm_chart
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Cylinder_injOn_chart :
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    Set.InjOn f {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧ 0 < x 2 ∧ x 2 < 2 * Real.pi} := by
  dsimp only
  intro x hx y hy hxy
  have hr : x 0 = y 0 := by
    have hn := congrArg (fun z => ‖(WithLp.toLp 2 z : E3)‖) hxy
    rw [SphereGeom.Aux.Cylinder.norm_chart (x 0) (x 1) (x 2) ⟨hx.2.1.le, hx.2.2.1.le⟩,
      SphereGeom.Aux.Cylinder.norm_chart (y 0) (y 1) (y 2) ⟨hy.2.1.le, hy.2.2.1.le⟩,
      abs_of_pos hx.1, abs_of_pos hy.1] at hn
    exact hn
  have hz : x 1 = y 1 := by
    have hh := congrFun hxy 2
    simp only [Matrix.cons_val_two] at hh
    rw [hr] at hh
    exact mul_left_cancel₀ (ne_of_gt hy.1) hh
  have hp : 0 < 1 - (x 1)^2 := by nlinarith [hx.2.1, hx.2.2.1]
  have ha : x 0 * Real.sqrt (1 - (x 1)^2) ≠ 0 :=
    mul_ne_zero (ne_of_gt hx.1) (ne_of_gt (Real.sqrt_pos.2 hp))
  have hc : Real.cos (x 2) = Real.cos (y 2) := by
    have hh := congrFun hxy 0
    simp only [Matrix.cons_val_zero] at hh
    rw [← hr, ← hz] at hh
    exact mul_left_cancel₀ ha hh
  have hs : Real.sin (x 2) = Real.sin (y 2) := by
    have hh := congrFun hxy 1
    simp only [Matrix.cons_val_one] at hh
    rw [← hr, ← hz] at hh
    exact mul_left_cancel₀ ha hh
  have hphi : x 2 = y 2 := by
    apply Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by linarith)
      ⟨hx.2.2.2.1.le, hx.2.2.2.2⟩ ⟨hy.2.2.2.1.le, hy.2.2.2.2⟩
    apply Subtype.ext
    apply Complex.ext <;> simp [Circle.coe_exp, Complex.exp_ofReal_mul_I, hc, hs]
  funext i
  fin_cases i
  · exact hr
  · exact hz
  · exact hphi
