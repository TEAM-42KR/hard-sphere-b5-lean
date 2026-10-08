import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_Santalo_gram_residual_bound (n u v : E3) (hn : ‖n‖ ≤ 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |inner ℝ n v - inner ℝ n u * inner ℝ u v| ≤ Real.sqrt (1 - inner ℝ u v ^ 2) := by
  let x := inner ℝ u v
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hres : ‖v - x • u‖ ^ 2 = 1 - x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, huu, hvv]
    dsimp [x]
    rw [real_inner_comm v u]
    ring
  have hres_norm : ‖v - x • u‖ = Real.sqrt (1 - x ^ 2) := by
    rw [← hres, Real.sqrt_sq (norm_nonneg _)]
  have hre : inner ℝ n v - inner ℝ n u * x = inner ℝ n (v - x • u) := by
    simp [inner_sub_right, real_inner_smul_right, mul_comm]
  rw [hre]
  calc
    _ ≤ ‖n‖ * ‖v - x • u‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖v - x • u‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := by rw [one_mul, hres_norm]
