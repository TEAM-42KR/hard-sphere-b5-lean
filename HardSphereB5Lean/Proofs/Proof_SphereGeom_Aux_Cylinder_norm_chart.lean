import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Cylinder_norm_chart (r z phi : ℝ) (hz : -1 ≤ z ∧ z ≤ 1) :
    ‖(WithLp.toLp 2 ![r * Real.sqrt (1-z^2) * Real.cos phi,
      r * Real.sqrt (1-z^2) * Real.sin phi, r*z] : E3)‖ = |r| := by
  have hzsq : 0 ≤ 1-z^2 := by nlinarith [sq_nonneg (z+1), sq_nonneg (z-1)]
  have hsq : ‖(WithLp.toLp 2 ![r * Real.sqrt (1-z^2) * Real.cos phi,
      r * Real.sqrt (1-z^2) * Real.sin phi, r*z] : E3)‖^2 = r^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, Fin.sum_univ_zero,
      add_zero, mul_pow]
    calc
      _ = r^2 * (Real.sqrt (1-z^2))^2 * ((Real.sin phi)^2 + (Real.cos phi)^2) + r^2*z^2 := by ring
      _ = r^2 := by rw [Real.sq_sqrt hzsq, Real.sin_sq_add_cos_sq]; ring
  nlinarith [norm_nonneg (WithLp.toLp 2 ![r * Real.sqrt (1-z^2) * Real.cos phi,
      r * Real.sqrt (1-z^2) * Real.sin phi, r*z] : E3), abs_nonneg r,
    sq_abs r]
