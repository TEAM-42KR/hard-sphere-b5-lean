import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
noncomputable section

private theorem SphereGeom.Aux.Santalo.cross_norm_sq (u v : E3) :
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
theorem proof_SphereGeom_Aux_Santalo_rational_remainder_bound
    (nA nB u v : E3) (q : ℝ) (hnA : ‖nA‖ ≤ 1) (hnB : ‖nB‖ ≤ 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |q / (1 - inner ℝ u v ^ 2) * inner ℝ nA (cross u v) * inner ℝ nB (cross u v)|
      ≤ |q| := by
  have hnorm : ‖cross u v‖ ^ 2 = 1 - inner ℝ u v ^ 2 := by
    simpa [hu, hv] using SphereGeom.Aux.Santalo.cross_norm_sq u v
  have hS : 0 ≤ 1 - inner ℝ u v ^ 2 := by rw [← hnorm]; positivity
  have hA : |inner ℝ nA (cross u v)| ≤ ‖cross u v‖ := by
    calc
      _ ≤ ‖nA‖ * ‖cross u v‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖cross u v‖ := mul_le_mul_of_nonneg_right hnA (norm_nonneg _)
      _ = ‖cross u v‖ := one_mul _
  have hB : |inner ℝ nB (cross u v)| ≤ ‖cross u v‖ := by
    calc
      _ ≤ ‖nB‖ * ‖cross u v‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖cross u v‖ := mul_le_mul_of_nonneg_right hnB (norm_nonneg _)
      _ = ‖cross u v‖ := one_mul _
  by_cases hzero : 1 - inner ℝ u v ^ 2 = 0
  · simp [hzero]
  · have hpos : 0 < 1 - inner ℝ u v ^ 2 := lt_of_le_of_ne hS (Ne.symm hzero)
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hS]
    calc
      |q| / (1 - inner ℝ u v ^ 2) * |inner ℝ nA (cross u v)| *
            |inner ℝ nB (cross u v)| ≤
          |q| / (1 - inner ℝ u v ^ 2) * ‖cross u v‖ * ‖cross u v‖ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hA (div_nonneg (abs_nonneg q) hS)) hB
          (abs_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg q) hS) (norm_nonneg _))
      _ = |q| := by
        rw [mul_assoc, ← pow_two, hnorm]
        exact div_mul_cancel₀ _ hzero
