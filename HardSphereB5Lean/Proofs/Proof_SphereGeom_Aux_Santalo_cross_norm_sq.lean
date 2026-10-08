import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_Santalo_cross_norm_sq (u v : E3) :
    ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq]
  have hinner (s t : E3) : inner ℝ s t =
      s 0 * t 0 + s 1 * t 1 + s 2 * t 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
    <;> ring
  simp_rw [hinner]
  simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring
