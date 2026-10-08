import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_circInt_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_circInt_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_inverse_distance
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_rho_squared_distance
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical ENNReal
set_option maxHeartbeats 1200000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_kernel_integrable (f : Kern) :
  Integrable (Function.uncurry (fun p p' : Pt =>
    if 0 < dist p p' ∧ dist p p' < 1 then
      rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0))
    (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)) := by
  let μ : Measure Pt := (sphereMeasure 0).restrict FA
  let ν : Measure Pt := (sphereMeasure e).restrict FB
  haveI (c : Pt) : IsFiniteMeasure (sphereMeasure c) := ⟨by
    rw [sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hFA : MeasurableSet FA := Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall
  have hFB : MeasurableSet FB := Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall
  let V : Pt × Pt → ℝ := fun p => (dist p.1 p.2)⁻¹
  have hVm : Measurable V := by dsimp [V]; fun_prop
  have hVi : Integrable V (μ.prod ν) := by
    apply (integrable_prod_iff hVm.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem hFA] with p hp
      have hnp : ‖p-e‖ ≤ 1 := by simpa [dist_eq_norm] using hp.2
      exact (Aux.Coarea.sphere_inverse_distance e p hnp).1.integrableOn
    · have hφ : AEStronglyMeasurable (fun p => ∫ p' : Pt, ‖V (p,p')‖ ∂ν) μ :=
        hVm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      refine (integrable_const (4*π : ℝ)).mono' hφ ?_
      filter_upwards [ae_restrict_mem hFA] with p hp
      have hnp : ‖p-e‖ ≤ 1 := by simpa [dist_eq_norm] using hp.2
      rcases Aux.Coarea.sphere_inverse_distance e p hnp with ⟨hi,heq⟩
      have hnonneg (p' : Pt) : 0 ≤ (dist p p')⁻¹ := inv_nonneg.mpr dist_nonneg
      have hnorm : (fun p' : Pt => ‖V (p,p')‖) = (fun p' => (dist p p')⁻¹) := by
        funext p'; simp only [V, Real.norm_eq_abs, abs_of_nonneg (hnonneg p')]
      rw [hnorm, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg (fun p' => hnonneg p'))]
      change ∫ p' in FB, (dist p p')⁻¹ ∂sphereMeasure e ≤ 4*π
      rw [← heq]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall hnonneg)
  let K : Pt × Pt → ℝ := fun p =>
    if 0 < dist p.1 p.2 ∧ dist p.1 p.2 < 1 then
      rhoK f (1 - dist p.1 p.2 ^ 2 / 2) / dist p.1 p.2 * circInt p.1 p.2 else 0
  have hKm : Measurable K := by
    have hrho : Measurable (fun p : Pt × Pt => rhoK f (1-dist p.1 p.2^2/2)) := by
      cases f <;> dsimp [rhoK] <;> fun_prop
    have hdistm : Measurable (fun p : Pt × Pt => dist p.1 p.2) :=
      (continuous_fst.dist continuous_snd).measurable
    apply Measurable.ite ((measurableSet_lt measurable_const hdistm).inter
      (measurableSet_lt hdistm measurable_const)) _ measurable_const
    exact (hrho.div hdistm).mul Aux.Coarea.circInt_measurable
  have hbound (p p' : Pt) (hp : p ∈ FA) (hp' : p' ∈ FB) :
      ‖K (p,p')‖ ≤ (8*π) * V (p,p') := by
    by_cases hd : 0 < dist p p' ∧ dist p p' < 1
    · let d : ℝ := dist p p'
      have hd0 : 0 < d := hd.1
      have hd1 : d < 1 := hd.2
      have hs0 : 0 < d^2 := sq_pos_of_pos hd0
      have hs1 : d^2 < 1 := by nlinarith
      have hs4 : d^2 < 4 := by linarith
      have hden : 0 < d^2 * (4-d^2) := mul_pos hs0 (by linarith)
      have hrho : |rhoK f (1-d^2/2)| * d^2 ≤ 4 := by
        rcases rho_squared_distance (d^2) hs0 hs4 with ⟨h1,hc⟩
        rw [← le_div_iff₀ hs0]
        cases f
        · rw [h1, abs_of_neg (div_neg_of_neg_of_pos (by linarith) hden), ← neg_div]
          apply (div_le_div_iff₀ hden hs0).2
          calc
            -(4*(d^2-1))*d^2 ≤ (4*(4-d^2))*d^2 :=
              mul_le_mul_of_nonneg_right (by linarith) hs0.le
            _ = 4*(d^2*(4-d^2)) := by ring
        · rw [hc, abs_of_neg (div_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos (by linarith) (by linarith)) hden), ← neg_div]
          apply (div_le_div_iff₀ hden hs0).2
          calc
            -((d^2-1)*(3-d^2))*d^2 ≤ (4*(4-d^2))*d^2 := by
              apply mul_le_mul_of_nonneg_right _ hs0.le
              nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs1.le)]
            _ = 4*(d^2*(4-d^2)) := by ring
      have hc := Aux.Coarea.circInt_bound p p' hp hp' hd.1 hd.2
      change |K (p,p')| ≤ (8*π) * d⁻¹
      simp only [K, if_pos hd, abs_mul, abs_div, abs_of_pos hd.1]
      change |rhoK f (1-d^2/2)| / d * |circInt p p'| ≤ (8*π)*d⁻¹
      calc
        |rhoK f (1-d^2/2)| / d * |circInt p p'| ≤
            |rhoK f (1-d^2/2)| / d * (2*π*d^2) := by
          exact mul_le_mul_of_nonneg_left hc (div_nonneg (abs_nonneg _) hd0.le)
        _ = (2*π) * (|rhoK f (1-d^2/2)| *d^2) / d := by ring
        _ ≤ (2*π)*4/d := by gcongr
        _ = (8*π)*d⁻¹ := by ring
    · simp only [K, if_neg hd, norm_zero, V]
      exact mul_nonneg (by positivity) (inv_nonneg.mpr dist_nonneg)
  have hdom := hVi.const_mul (8*π)
  apply hdom.mono' hKm.aestronglyMeasurable
  have hpair : ∀ᵐ p : Pt × Pt ∂μ.prod ν, p.1 ∈ FA ∧ p.2 ∈ FB := by
    apply (Measure.ae_prod_iff_ae_ae (hFA.prod hFB)).mpr
    filter_upwards [ae_restrict_mem hFA] with p hp
    filter_upwards [ae_restrict_mem hFB] with p' hp'
    exact ⟨hp,hp'⟩
  filter_upwards [hpair] with p hp
  exact hbound p.1 p.2 hp.1 hp.2
