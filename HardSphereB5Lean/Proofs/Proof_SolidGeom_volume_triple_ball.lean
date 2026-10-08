import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_integral_max_cos_sectors
import HardSphereB5Lean.Theorems.Thm_SolidGeom_integral_vertex_sector
import HardSphereB5Lean.Theorems.Thm_SolidGeom_triple_normal_form
import HardSphereB5Lean.Theorems.Thm_SolidGeom_Q_inscribed
import HardSphereB5Lean.Theorems.Thm_SolidGeom_gamma_sum_inscribed
import HardSphereB5Lean.Theorems.Thm_SolidGeom_beta_inscribed
import HardSphereB5Lean.Theorems.Thm_SolidGeom_volume_normal_form_angular
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1600000
theorem proof_SolidGeom_volume_triple_ball (c : Fin 3 → E3)
    (hQ : 0 < 4 * dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2
        - (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) ^ 2
        - dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2 * dist (c 1) (c 2) ^ 2) :
    let a := dist (c 0) (c 1) ^ 2
    let b := dist (c 0) (c 2) ^ 2
    let cc := dist (c 1) (c 2) ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    let g : ℝ → ℝ := fun d => d - d ^ 3 / 12
    (volume (Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩ Metric.closedBall (c 2) 1)).toReal =
      2 * π - 2 / 3 * (Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
          + Complex.arg ⟨2 * (a + cc - b) - a * cc, 2 * √Q⟩
          + Complex.arg ⟨2 * (b + cc - a) - b * cc, 2 * √Q⟩)
        - (g (√a) * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
          + g (√b) * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩
          + g (√cc) * Complex.arg ⟨√cc * (a + b - cc), 2 * √Q⟩)
        + √Q / 6  := by
  dsimp only
  obtain ⟨o, e, R, ψ, α₀, α₁, α₂, he, hR0, hR1, h0, h1, h2, hs,
      hc0, hc1, hc2⟩ := SolidGeom.triple_normal_form c hQ

  have hdist : ∀ (θ α : ℝ),
      dist (o - R • (cos θ • e 0 + sin θ • e 1))
        (o - R • (cos (θ + 2 * α) • e 0 + sin (θ + 2 * α) • e 1)) ^ 2 =
          4 * R ^ 2 * sin α ^ 2 := by
    intro θ α
    rw [dist_eq_norm]
    have hv : (o - R • (cos θ • e 0 + sin θ • e 1)) -
        (o - R • (cos (θ + 2 * α) • e 0 + sin (θ + 2 * α) • e 1)) =
        R • ((cos (θ + 2 * α) - cos θ) • e 0 + (sin (θ + 2 * α) - sin θ) • e 1) := by
      module
    rw [hv, ← real_inner_self_eq_norm_sq]
    have hinner := (orthonormal_iff_ite.mp he)
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hinner]
    norm_num
    calc
      _ = R ^ 2 * (cos θ ^ 2 + sin θ ^ 2 + cos (θ + 2 * α) ^ 2 +
          sin (θ + 2 * α) ^ 2 - 2 * (cos (θ + 2 * α) * cos θ +
          sin (θ + 2 * α) * sin θ)) := by ring
      _ = R ^ 2 * (2 - 2 * cos ((θ + 2 * α) - θ)) := by
        congr 1
        rw [cos_sub]
        nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq (θ + 2 * α)]
      _ = 4 * R ^ 2 * sin α ^ 2 := by
        rw [show θ + 2 * α - θ = 2 * α by ring, cos_two_mul]
        have ht : 2 - 2 * (2 * cos α ^ 2 - 1) = 4 * sin α ^ 2 := by
          nlinarith [sin_sq_add_cos_sq α]
        rw [ht]
        ring
  have ha : dist (c 0) (c 1) ^ 2 = 4 * R ^ 2 * sin α₂ ^ 2 := by
    rw [hc0, hc1]
    exact hdist ψ α₂
  have hb : dist (c 0) (c 2) ^ 2 = 4 * R ^ 2 * sin α₁ ^ 2 := by
    rw [hc0, hc2]
    have heq : ψ + 2 * α₂ + 2 * α₀ = ψ + 2 * (α₂ + α₀) := by ring
    rw [heq, hdist]
    have heq' : α₂ + α₀ = π - α₁ := by linarith
    rw [heq', sin_pi_sub]
  have hcc : dist (c 1) (c 2) ^ 2 = 4 * R ^ 2 * sin α₀ ^ 2 := by
    rw [hc1, hc2]
    exact hdist (ψ + 2 * α₂) α₀
  have hsqrt : ∀ (α : ℝ), 0 < α → α < π →
      √(4 * R ^ 2 * sin α ^ 2) = 2 * R * sin α := by
    intro α hα hαπ
    rw [show 4 * R ^ 2 * sin α ^ 2 = (2 * R * sin α) ^ 2 by ring,
      sqrt_sq_eq_abs, abs_of_nonneg]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hR0))
      (le_of_lt (sin_pos_of_pos_of_lt_pi hα hαπ))
  have haπ : α₀ < π := by linarith
  have hbπ : α₁ < π := by linarith
  have hcπ : α₂ < π := by linarith
  have hsa := hsqrt α₂ h2 hcπ
  have hsb := hsqrt α₁ h1 hbπ
  have hsc := hsqrt α₀ h0 haπ
  let h : ℝ := √(1 - R ^ 2)
  let I : ℝ → ℝ := fun p => 2 / 3 * h ^ 3 + p ^ 2 * h -
    p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h))
  have hF : Continuous (fun w : ℝ => I (R * w)) := by
    dsimp [I]
    fun_prop
  have hv := SolidGeom.volume_normal_form_angular c o e R ψ α₀ α₁ α₂
    he hR0 hR1 h0 h1 h2 hs hc0 hc1 hc2
  have hsectors := SolidGeom.integral_max_cos_sectors (fun w => I (R * w)) hF
    ψ α₀ α₁ α₂ h0 h1 h2 hs
  have hv' : (volume (Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩
      Metric.closedBall (c 2) 1)).toReal =
      2 * ((∫ t in (0 : ℝ)..α₀, I (R * cos t)) +
        (∫ t in (0 : ℝ)..α₁, I (R * cos t)) +
        ∫ t in (0 : ℝ)..α₂, I (R * cos t)) := by
    exact hv.trans hsectors
  rw [hv', ha, hb, hcc, hsa, hsb, hsc]
  have hV0 := SolidGeom.integral_vertex_sector R α₀ hR0 hR1 (le_of_lt h0) haπ
  have hV1 := SolidGeom.integral_vertex_sector R α₁ hR0 hR1 (le_of_lt h1) hbπ
  have hV2 := SolidGeom.integral_vertex_sector R α₂ hR0 hR1 (le_of_lt h2) hcπ
  change (∫ t in (0 : ℝ)..α₀, I (R * cos t)) = _ at hV0
  change (∫ t in (0 : ℝ)..α₁, I (R * cos t)) = _ at hV1
  change (∫ t in (0 : ℝ)..α₂, I (R * cos t)) = _ at hV2
  rw [hV0, hV1, hV2]
  have hq := SolidGeom.Q_inscribed R α₀ α₁ α₂ hR0 hR1 h0 h1 h2 hs
  have hgs := SolidGeom.gamma_sum_inscribed R α₀ α₁ α₂ hR0 hR1 h0 h1 h2 hs
  dsimp only at hgs
  have hb0 := SolidGeom.beta_inscribed R α₀ α₁ α₂ hR0 hR1 h0 h1 h2 hs
  have hb1 := SolidGeom.beta_inscribed R α₁ α₀ α₂ hR0 hR1 h1 h0 h2
    (by linarith : α₁ + α₀ + α₂ = π)
  have hb2 := SolidGeom.beta_inscribed R α₂ α₀ α₁ hR0 hR1 h2 h0 h1
    (by linarith : α₂ + α₀ + α₁ = π)
  rw [hq]
  ring_nf at hgs hb0 hb1 hb2 ⊢
  rw [hb0, hb1, hb2]
  nlinarith [hgs]
