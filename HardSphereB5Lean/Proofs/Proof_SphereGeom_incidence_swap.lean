import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_incidence_swap
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame_period
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom SphereGeom.Aux.Pair
noncomputable section
set_option maxHeartbeats 1500000
theorem proof_SphereGeom_incidence_swap (F₁ F₂ : E3 → E3) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p]) (H : E3 → E3 → ENNReal)
    (hH : Measurable (Function.uncurry H)) :
    ∫⁻ p, (∫⁻ t in Set.Ioc 0 (2 * Real.pi), H p (Real.cos t • F₁ p + Real.sin t • F₂ p)) ∂dOmega =
      ∫⁻ u, (∫⁻ t in Set.Ioc 0 (2 * Real.pi), H (Real.cos t • F₁ u + Real.sin t • F₂ u) u) ∂dOmega := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Set.Ico 0 (2 * Real.pi))
  have hC : Measurable (Function.uncurry SphereGeom.Aux.Pair.cylinder) := by
    unfold SphereGeom.Aux.Pair.cylinder Function.uncurry; fun_prop
  have he : Orthonormal ℝ (![WithLp.toLp 2 ![1,0,0], WithLp.toLp 2 ![0,1,0],
      WithLp.toLp 2 ![0,0,1]] : Fin 3 → E3) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]
  have hmap : dOmega = (μ.prod ν).map (Function.uncurry SphereGeom.Aux.Pair.cylinder) := by
    have h := dOmega_map_cylinder _ he
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    convert h using 1
    congr 1
    funext x
    ext i
    fin_cases i <;> simp [SphereGeom.Aux.Pair.cylinder, Function.uncurry]
  have hEq (p a b c d : E3) (h₁ : Orthonormal ℝ ![a,b,p]) (h₂ : Orthonormal ℝ ![c,d,p])
      (f : E3 → ENNReal) (hf : Measurable f) :
      (∫⁻ t, f (circlePt 0 a b 1 t) ∂ν) = ∫⁻ t, f (circlePt 0 c d 1 t) ∂ν := by
    calc
      (∫⁻ t, f (circlePt 0 a b 1 t) ∂ν) = ∫⁻ x, f x ∂arcMeasure.restrict (greatCircle p) := by
        rw [arcMeasure_greatCircle_frame_period a b p h₁, lintegral_map hf (by unfold circlePt; fun_prop)]
      _ = _ := by
        rw [arcMeasure_greatCircle_frame_period c d p h₂, lintegral_map hf (by unfold circlePt; fun_prop)]
  have reduce (K : E3 → E3 → ENNReal) (hK : Measurable (Function.uncurry K)) :
      (∫⁻ p, ∫⁻ t, K p (circlePt 0 (F₁ p) (F₂ p) 1 t) ∂ν ∂dOmega) =
      ∫⁻ z, ∫⁻ φ, ∫⁻ t, K (SphereGeom.Aux.Pair.cylinder z φ) (fiber z φ t) ∂ν ∂ν ∂μ := by
    let G : E3 → ENNReal := fun p => ∫⁻ t, K p (circlePt 0 (F₁ p) (F₂ p) 1 t) ∂ν
    have hmG : Measurable G := Measurable.lintegral_prod_right
      (f := fun p t => K p (circlePt 0 (F₁ p) (F₂ p) 1 t))
      (hK.comp (show Measurable (fun x : E3 × ℝ => (x.1, circlePt 0 (F₁ x.1) (F₂ x.1) 1 x.2)) by
        unfold circlePt; fun_prop))
    change (∫⁻ p, G p ∂dOmega) = _
    rw [hmap, lintegral_map hmG hC]
    change (∫⁻ x : ℝ × ℝ, G (SphereGeom.Aux.Pair.cylinder x.1 x.2) ∂μ.prod ν) = _
    rw [lintegral_prod _ (show AEMeasurable (fun x : ℝ × ℝ => G (SphereGeom.Aux.Pair.cylinder x.1 x.2)) (μ.prod ν) from (hmG.comp hC).aemeasurable)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    apply lintegral_congr
    intro φ
    let p := SphereGeom.Aux.Pair.cylinder z φ
    have hon : Orthonormal ℝ ![frame1 φ,frame2 z φ,p] := cylinder_frame_orthonormal z φ hz
    have hp : ‖p‖ = 1 := by simpa using hon.norm_eq_one (2 : Fin 3)
    exact hEq p (F₁ p) (F₂ p) (frame1 φ) (frame2 z φ) (hF p hp) hon
      (K p) (hK.comp (measurable_const.prodMk measurable_id))
  rw [← restrict_Ico_eq_restrict_Ioc]
  have hcf (p : E3) (t : ℝ) : circlePt 0 (F₁ p) (F₂ p) 1 t = Real.cos t • F₁ p + Real.sin t • F₂ p := by simp [circlePt]
  simp_rw [← hcf]
  change (∫⁻ p, ∫⁻ t, H p (circlePt 0 (F₁ p) (F₂ p) 1 t) ∂ν ∂dOmega) =
    ∫⁻ p, ∫⁻ t, H (circlePt 0 (F₁ p) (F₂ p) 1 t) p ∂ν ∂dOmega
  calc
    _ = _ := reduce H hH
    _ = _ := cylinder_incidence_swap H hH
    _ = _ := (reduce (fun p u => H u p) (hH.comp measurable_swap)).symm
