import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_formula
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_ne_zero (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hD1 : D 1 ≠ 0) (α : ℝ) (hα : Real.sin α ≠ 0) :
    inner ℝ (SphereGeom.cross (u D α) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) e ≠ 0 := by
  have hD : D ≠ 0 := by
    intro hz
    exact hoff 0 (by simpa using hz)
  have hraw : rawA D ≠ 0 := by
    intro hz
    have hon := (EA_orthonormal D hoff).norm_eq_one (0 : Fin 2)
    simp [EA, unitDir, hz] at hon
  have hnle : ‖D‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hL.1
  have hr : 0 < rA D := by
    unfold rA
    apply Real.sqrt_pos.2
    nlinarith [norm_nonneg D]
  have hQ : D 1 ^ 2 + D 2 ^ 2 ≠ 0 := by
    have hpos : 0 < D 1 ^ 2 := sq_pos_of_ne_zero hD1
    nlinarith [sq_nonneg (D 2)]
  rw [HardSphereB5.SphericalCrofton.Aux.Coarea.cross_u_cB_axis_formula]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hr.ne' hα) hQ)
    (mul_ne_zero (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr hD))
      (norm_ne_zero_iff.mpr hraw))
