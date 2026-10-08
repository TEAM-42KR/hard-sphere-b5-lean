import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1200000

theorem proof_SphereGeom_two_cap_normal_moment (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (A K L h b : ℝ) :
    inner ℝ (e 2) (∫ u in cap (A • e 0) h ∩
      cap (K • e 0 + L • e 1) b, u ∂dOmega) = 0 := by
  classical
  let S := cap (A • e 0) h ∩ cap (K • e 0 + L • e 1) b
  have hcap (v : E3) (d : ℝ) : MeasurableSet (cap v d) := by
    unfold cap
    exact ((isClosed_eq (continuous_norm : Continuous (fun u : E3 => ‖u‖))
      (continuous_const : Continuous (fun _ : E3 => (1:ℝ)))).inter
      (isClosed_le (continuous_const : Continuous (fun _ : E3 => d))
        (by fun_prop : Continuous (fun u : E3 => inner ℝ v u)))).measurableSet
  have hs : MeasurableSet S := (hcap _ _).inter (hcap _ _)
  haveI : IsFiniteMeasure dOmega := by unfold dOmega sphereMeasure; infer_instance
  have hfi : Integrable (S.indicator (fun u : E3 => u)) dOmega := by
    refine (integrable_const (1:ℝ)).mono' ?_ ?_
    · exact (measurable_id.indicator hs).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        by_cases hu : u ∈ S
        · rw [Set.indicator_of_mem hu]
          exact le_of_eq hu.1.1
        · simp [Set.indicator_of_notMem hu]
  let ep : Fin 3 → E3 := ![e 1, e 2, e 0]
  have hei := orthonormal_iff_ite.mp he
  have hep : Orthonormal ℝ ep := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ep, hei, Fin.ext_iff, he.norm_eq_one]
  rw [← integral_indicator hs, ← integral_inner hfi (e 2)]
  rw [SphereGeom.integral_dOmega_frame ep hep _ (hfi.const_inner (e 2))]
  let J : ℝ → ℝ → ℝ := fun θ φ => Real.sin θ *
    (if h ≤ A * Real.cos θ ∧
      b ≤ K * Real.cos θ + L * Real.sin θ * Real.cos φ
      then Real.sin θ * Real.sin φ else 0)
  have point (θ φ : ℝ) :
      Real.sin θ • inner ℝ (e 2)
        (S.indicator (fun v : E3 => v)
          ((Real.sin θ * Real.cos φ) • ep 0 +
           (Real.sin θ * Real.sin φ) • ep 1 + Real.cos θ • ep 2)) = J θ φ := by
    let u := (Real.sin θ * Real.cos φ) • e 1 +
      (Real.sin θ * Real.sin φ) • e 2 + Real.cos θ • e 0
    have hnorm : ‖u‖ = 1 := by
      have hh : inner ℝ u u = 1 := by
        dsimp [u]
        simp only [inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, hei]
        norm_num [Fin.ext_iff]
        nlinarith [Real.sin_sq_add_cos_sq θ,
          congrArg (fun z : ℝ => Real.sin θ ^ 2 * z) (Real.sin_sq_add_cos_sq φ)]
      rw [real_inner_self_eq_norm_sq] at hh
      nlinarith [norm_nonneg u]
    have h0 : inner ℝ (e 0) u = Real.cos θ := by
      dsimp [u]
      simp only [inner_add_right, real_inner_smul_right, hei]
      norm_num [Fin.ext_iff]
    have h1 : inner ℝ (e 1) u = Real.sin θ * Real.cos φ := by
      dsimp [u]
      simp only [inner_add_right, real_inner_smul_right, hei]
      norm_num [Fin.ext_iff]
    have h2 : inner ℝ (e 2) u = Real.sin θ * Real.sin φ := by
      dsimp [u]
      simp only [inner_add_right, real_inner_smul_right, hei]
      norm_num [Fin.ext_iff]
    have ha : inner ℝ (A • e 0) u = A * Real.cos θ := by
      rw [real_inner_smul_left, h0]
    have hw : inner ℝ (K • e 0 + L • e 1) u =
        K * Real.cos θ + L * Real.sin θ * Real.cos φ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h0, h1]
      ring
    have hm : u ∈ S ↔ h ≤ A * Real.cos θ ∧
        b ≤ K * Real.cos θ + L * Real.sin θ * Real.cos φ := by
      simp [S, cap, hnorm, ha, hw]
    change Real.sin θ * inner ℝ (e 2) (S.indicator (fun v : E3 => v) u) = J θ φ
    dsimp only [J]
    by_cases hc : h ≤ A * Real.cos θ ∧
        b ≤ K * Real.cos θ + L * Real.sin θ * Real.cos φ
    · rw [Set.indicator_of_mem (hm.mpr hc), if_pos hc, h2]
    · rw [Set.indicator_of_notMem (mt hm.mp hc), if_neg hc]
      simp
  have hzero (θ : ℝ) : (∫ φ in (0 : ℝ)..(2 * Real.pi), J θ φ) = 0 := by
    have hsym : (fun φ => J θ (2 * Real.pi - φ)) = fun φ => -J θ φ := by
      funext φ
      dsimp only [J]
      rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
      split_ifs <;> ring
    have hh := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := 2 * Real.pi) (J θ) (2 * Real.pi)
    rw [hsym, intervalIntegral.integral_neg, sub_self, sub_zero] at hh
    linarith
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      calc
        _ = ∫ φ in (0 : ℝ)..(2 * Real.pi), J θ φ := by
          apply intervalIntegral.integral_congr
          intro φ _
          exact point θ φ
        _ = 0 := hzero θ
    _ = 0 := by simp
