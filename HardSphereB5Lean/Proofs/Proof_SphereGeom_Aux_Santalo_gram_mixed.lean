import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_Santalo_gram_mixed
    (nA nB u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (1 - inner ℝ u v ^ 2) *
        (inner ℝ nA v * inner ℝ nB u - inner ℝ nA nB * inner ℝ u v) +
      inner ℝ u v * inner ℝ nA (cross u v) * inner ℝ nB (cross u v) =
    (inner ℝ nA v - inner ℝ nA u * inner ℝ u v) *
      (inner ℝ nB u - inner ℝ nB v * inner ℝ u v) := by
  have hgram : inner ℝ nA (cross u v) * inner ℝ nB (cross u v) =
      inner ℝ nA nB * (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) -
        inner ℝ nA u * inner ℝ nB u * inner ℝ v v -
        inner ℝ nA v * inner ℝ nB v * inner ℝ u u +
        inner ℝ u v * (inner ℝ nA u * inner ℝ nB v + inner ℝ nA v * inner ℝ nB u) := by
    have hinner (s t : E3) : inner ℝ s t =
        s 0 * t 0 + s 1 * t 1 + s 2 * t 2 := by
      simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
      <;> ring
    simp_rw [hinner]
    simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  rw [mul_assoc (inner ℝ u v), hgram, huu, hvv]
  ring
