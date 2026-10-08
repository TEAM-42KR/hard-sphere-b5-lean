import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_pair_normal_frame
set_option autoImplicit false
noncomputable section
open SphereGeom

theorem proof_SphereGeom_pair_normalized_frame (v w : E3)
 (hG : 0 < ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2) :
 ∃ e : Fin 3 → E3, Orthonormal ℝ e ∧ v = ‖v‖ • e 0 ∧
 w = ‖w‖ • (Real.cos (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) • e 0 +
 Real.sin (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) • e 1) := by
  have hv : 0 < ‖v‖ := by
    by_contra ht
    have hz : ‖v‖ = 0 := le_antisymm (le_of_not_gt ht) (norm_nonneg v)
    rw [hz] at hG
    nlinarith [sq_nonneg (inner ℝ v w)]
  have hw : 0 < ‖w‖ := by
    by_contra ht
    have hz : ‖w‖ = 0 := le_antisymm (le_of_not_gt ht) (norm_nonneg w)
    rw [hz] at hG
    nlinarith [sq_nonneg (inner ℝ v w)]
  have hv0 := ne_of_gt hv
  have hw0 := ne_of_gt hw
  have hprod : 0 < ‖v‖ * ‖w‖ := mul_pos hv hw
  have hp0 : ‖v‖ * ‖w‖ ≠ 0 := ne_of_gt hprod
  have hupper : inner ℝ v w < ‖v‖ * ‖w‖ := by
    nlinarith [sq_nonneg (‖v‖ * ‖w‖ - inner ℝ v w)]
  have hlower : -(‖v‖ * ‖w‖) < inner ℝ v w := by
    nlinarith [sq_nonneg (‖v‖ * ‖w‖ + inner ℝ v w)]
  have hp1 : inner ℝ v w / (‖v‖ * ‖w‖) ≤ 1 := (div_le_iff₀ hprod).2 (by linarith)
  have hpm1 : -1 ≤ inner ℝ v w / (‖v‖ * ‖w‖) := (le_div_iff₀ hprod).2 (by linarith)
  obtain ⟨e, he, hve, hwe⟩ := SphereGeom.exists_pair_normal_frame v w hG
  refine ⟨e, he, hve, ?_⟩
  have hc : ‖w‖ * Real.cos (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) = inner ℝ v w / ‖v‖ := by
    rw [Real.cos_arccos hpm1 hp1]
    field_simp
  have hs : ‖w‖ * Real.sin (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) =
      Real.sqrt (‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2) := by
    rw [Real.sin_arccos]
    have hr : 0 ≤ 1 - (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2 := by
      nlinarith
    have hb : 0 ≤ ‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2 := by
      have hg := hG
      apply (le_of_lt ?_)
      apply (lt_of_mul_lt_mul_left (a := ‖v‖ ^ 2))
      · have ht : (‖v‖ ^ 2) * (‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2) =
            ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2 := by field_simp <;> ring
        rw [ht]
        simpa using hg
      · positivity
    have heq : (‖w‖ * Real.sqrt (1 - (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2)) ^ 2 =
        ‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hr]
      field_simp <;> ring
    have hpos : 0 ≤ ‖w‖ * Real.sqrt (1 - (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2) := by positivity
    nlinarith [Real.sqrt_nonneg (1 - (inner ℝ v w / (‖v‖ * ‖w‖)) ^ 2),
      Real.sqrt_nonneg (‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2), Real.sq_sqrt hb]
  rw [smul_add, smul_smul, smul_smul, hc, hs]
  exact hwe
