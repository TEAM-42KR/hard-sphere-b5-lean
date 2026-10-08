import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame_period
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_circle_marginal
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 1500000
theorem proof_SphereGeom_lintegral_arcMeasure_greatCircle (A : Set E3) (hA : MeasurableSet A)
    (hAs : A ⊆ Metric.sphere (0 : E3) 1) :
    ∫⁻ p, arcMeasure (greatCircle p ∩ A) ∂dOmega = ENNReal.ofReal (2 * Real.pi) * dOmega A := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Set.Ico 0 (2 * Real.pi))
  let f : E3 → ENNReal := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hfi : (∫⁻ u, f u ∂dOmega) = dOmega A := by simp [f, lintegral_indicator hA]
  have hArc (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁,v₂,p]) :
      arcMeasure (greatCircle p ∩ A) = ∫⁻ t, f (circlePt 0 v₁ v₂ 1 t) ∂ν := by
    calc
      arcMeasure (greatCircle p ∩ A) = ∫⁻ u, f u ∂arcMeasure.restrict (greatCircle p) := by
        simp [f, lintegral_indicator hA, Measure.restrict_apply hA,
          Set.inter_comm]
      _ = _ := by
        rw [SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame_period v₁ v₂ p hv,
          lintegral_map hf (by unfold circlePt; fun_prop)]
  obtain ⟨F₁,F₂,hF₁,hF₂,hF⟩ := exists_measurable_frame
  let G : E3 → ENNReal := fun p => ∫⁻ t, f (circlePt 0 (F₁ p) (F₂ p) 1 t) ∂ν
  have hGM : Measurable G := Measurable.lintegral_prod_right
    (f := fun p t => f (circlePt 0 (F₁ p) (F₂ p) 1 t))
    (hf.comp (show Measurable (fun x : E3 × ℝ => circlePt 0 (F₁ x.1) (F₂ x.1) 1 x.2) by
      dsimp [circlePt]; fun_prop))
  have hAE : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have h : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : E3) 1 := by
      exact ae_iff.mpr dOmega_compl_sphere
    filter_upwards [h] with p hp
    simpa [Metric.mem_sphere, dist_zero_right] using hp
  have hL : (∫⁻ p, arcMeasure (greatCircle p ∩ A) ∂dOmega) = ∫⁻ p, G p ∂dOmega := by
    apply lintegral_congr_ae
    filter_upwards [hAE] with p hp
    exact hArc (F₁ p) (F₂ p) p (hF p hp)
  let C : ℝ → ℝ → E3 := fun z φ => WithLp.toLp 2
    ![Real.sqrt (1-z^2) * Real.cos φ, Real.sqrt (1-z^2) * Real.sin φ, z]
  let v₁ : ℝ → E3 := fun φ => WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0]
  let v₂ : ℝ → ℝ → E3 := fun z φ => WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)]
  have hC : Measurable (Function.uncurry C) := by dsimp [C, Function.uncurry]; fun_prop
  have he : Orthonormal ℝ (![WithLp.toLp 2 ![1,0,0], WithLp.toLp 2 ![0,1,0],
      WithLp.toLp 2 ![0,0,1]] : Fin 3 → E3) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]
  have hmap : dOmega = (μ.prod ν).map (Function.uncurry C) := by
    have h := dOmega_map_cylinder _ he
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    convert h using 1
    congr 1
    funext x
    ext i
    fin_cases i <;> simp [C, Function.uncurry]
  calc
    (∫⁻ p, arcMeasure (greatCircle p ∩ A) ∂dOmega) = ∫⁻ p, G p ∂dOmega := hL
    _ = ∫⁻ z, ∫⁻ φ, G (C z φ) ∂ν ∂μ := by
      rw [hmap, lintegral_map hGM hC]
      exact lintegral_prod _ (hGM.comp hC).aemeasurable
    _ = ∫⁻ z, ∫⁻ φ, ∫⁻ t, f (circlePt 0 (v₁ φ) (v₂ z φ) 1 t) ∂ν ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      apply lintegral_congr
      intro φ
      have hon : Orthonormal ℝ ![v₁ φ, v₂ z φ, C z φ] :=
        SphereGeom.Aux.Pair.cylinder_frame_orthonormal z φ hz
      have hp : ‖C z φ‖ = 1 := by simpa using hon.norm_eq_one (2 : Fin 3)
      exact (hArc (F₁ (C z φ)) (F₂ (C z φ)) (C z φ) (hF _ hp)).symm.trans
        (hArc (v₁ φ) (v₂ z φ) (C z φ) hon)
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, f u ∂dOmega :=
      SphereGeom.Aux.Pair.cylinder_circle_marginal f hf
    _ = _ := by rw [hfi]
