import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_frame_tangent_parseval
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_radial_angle_prod_lintegral
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_frame_radial_angle_prod_lintegral (a b g v : E3) (hframe : Orthonormal ℝ ![a, b, g])
    (hvg : inner ℝ v g = 0) :
    (∫⁻ q : ℝ × ℝ in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (q.1 ^ 2 * |inner ℝ (Real.cos q.2 • a + Real.sin q.2 • b) v|)
        ∂(volume.prod volume)) =
      (4 / 3 : ENNReal) * ENNReal.ofReal ‖v‖ := by
  have hsqrt : Real.sqrt ((inner ℝ a v) ^ 2 + (inner ℝ b v) ^ 2) = ‖v‖ := by
    rw [SphereGeom.Aux.Crofton.frame_tangent_parseval a b g v hframe hvg,
      Real.sqrt_sq (norm_nonneg v)]
  calc
    _ = ∫⁻ q : ℝ × ℝ in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (q.1 ^ 2 *
          |(inner ℝ a v) * Real.cos q.2 + (inner ℝ b v) * Real.sin q.2|)
          ∂(volume.prod volume) := by
      apply lintegral_congr
      intro q
      simp only [inner_add_left, real_inner_smul_left, mul_comm]
    _ = ENNReal.ofReal ((4 / 3 : ℝ) * ‖v‖) := by
      rw [SphereGeom.Aux.Crofton.radial_angle_prod_lintegral, hsqrt]
    _ = (4 / 3 : ENNReal) * ENNReal.ofReal ‖v‖ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
