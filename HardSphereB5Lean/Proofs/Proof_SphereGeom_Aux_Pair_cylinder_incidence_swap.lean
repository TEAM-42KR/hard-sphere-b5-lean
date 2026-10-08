import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_fiber_phase
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_reciprocal_point
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_reciprocal_cylinder
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_periodic_lintegral_translate
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_sineHeightMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom SphereGeom.Aux.Pair
noncomputable section
set_option maxHeartbeats 2000000
theorem proof_SphereGeom_Aux_Pair_cylinder_incidence_swap (H : E3 → E3 → ENNReal) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi), ∫⁻ t in Set.Ico 0 (2 * Real.pi),
      H (SphereGeom.Aux.Pair.cylinder z φ) (fiber z φ t)) =
    (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi), ∫⁻ t in Set.Ico 0 (2 * Real.pi),
      H (fiber z φ t) (SphereGeom.Aux.Pair.cylinder z φ)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Set.Ico 0 (2 * Real.pi))
  let C := SphereGeom.Aux.Pair.cylinder
  let M := meridian
  let w : ℝ × ℝ → ℝ := fun x => Real.sqrt (1-x.1^2) * Real.sin x.2
  let J : E3 → ℝ → ENNReal := fun x ψ => H (reciprocal x ψ) (C (x 2) ψ)
  have hC : Measurable (Function.uncurry C) := by unfold C Function.uncurry SphereGeom.Aux.Pair.cylinder; fun_prop
  have hM : Measurable (Function.uncurry M) := by unfold M Function.uncurry meridian; fun_prop
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hJ : Measurable (Function.uncurry J) := hH.comp
    (show Measurable (fun x : E3 × ℝ => (reciprocal x.1 x.2, C (x.1 2) x.2)) by
      unfold C reciprocal SphereGeom.Aux.Pair.cylinder frame1 frame2
      fun_prop)
  have hZ : ∀ᵐ z ∂μ, z^2 < 1 := by
    change ∀ᵐ z ∂volume.restrict (Set.Icc (-1 : ℝ) 1), z^2 < 1
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    nlinarith [hz.1,hz.2]
  have hW : ∀ᵐ x ∂μ.prod ν, (w x)^2 < 1 := by
    apply ae_of_ae_map (μ := μ.prod ν) (p := fun y : ℝ => y^2 < 1) hw.aemeasurable
    rw [show (μ.prod ν).map w = ENNReal.ofReal (2*Real.pi) • μ from cylinder_sineHeightMeasure]
    exact Measure.ae_smul_measure hZ _
  let e : Fin 3 → E3 := ![WithLp.toLp 2 ![1,0,0], WithLp.toLp 2 ![0,1,0], WithLp.toLp 2 ![0,0,1]]
  let e' : Fin 3 → E3 := ![WithLp.toLp 2 ![-1,0,0], WithLp.toLp 2 ![0,0,1], WithLp.toLp 2 ![0,1,0]]
  have he : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr; intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [e,Fin.sum_univ_succ]
  have he' : Orthonormal ℝ e' := by
    apply orthonormal_iff_ite.mpr; intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [e',Fin.sum_univ_succ]
  have hmapC : (μ.prod ν).map (Function.uncurry C) = dOmega := by
    have h := dOmega_map_cylinder e he
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    convert h.symm using 1
    congr 1; funext x; ext i
    fin_cases i <;> simp [C,SphereGeom.Aux.Pair.cylinder,e,Function.uncurry]
  have hmapM : (μ.prod ν).map (Function.uncurry M) = dOmega := by
    have h := dOmega_map_cylinder e' he'
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    convert h.symm using 1
    congr 1; funext x; ext i
    fin_cases i <;> simp [M,meridian,e',Function.uncurry]
  have hshift (z t : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) (ht : (w (z,t))^2 < 1) :
      (∫⁻ φ, H (C z φ) (fiber z φ t) ∂ν) = ∫⁻ ψ, J (M z t) ψ ∂ν := by
    let θ : ℝ := (⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg
    let g : ℝ → ENNReal := fun ψ => H (C z (ψ-θ)) (C (w (z,t)) ψ)
    have hg : Function.Periodic g (2 * Real.pi) := by
      intro ψ
      have hadd : ψ + 2*Real.pi - θ = (ψ-θ)+2*Real.pi := by ring
      simp [g,C,SphereGeom.Aux.Pair.cylinder,hadd,Real.cos_add_two_pi,Real.sin_add_two_pi]
    calc
      (∫⁻ φ, H (C z φ) (fiber z φ t) ∂ν) = ∫⁻ φ, g (φ+θ) ∂ν := by
        apply lintegral_congr; intro φ
        rw [cylinder_fiber_phase z φ t hz]
        simp [g,θ,C,w]
      _ = ∫⁻ ψ, g ψ ∂ν := by
        change (∫⁻ φ in Set.Ico 0 (2*Real.pi), g (φ+θ)) = ∫⁻ ψ in Set.Ico 0 (2*Real.pi), g ψ
        rw [restrict_Ico_eq_restrict_Ioc]
        simpa only [zero_add] using periodic_lintegral_translate g (2*Real.pi) (by positivity) hg 0 θ
      _ = _ := by
        apply lintegral_congr; intro ψ
        have h := cylinder_reciprocal_point z t ψ hz ht
        change H (C z (ψ-θ)) (C (w (z,t)) ψ) = H (reciprocal (M z t) ψ) (C ((M z t) 2) ψ)
        change H (SphereGeom.Aux.Pair.cylinder z (ψ-(⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg)) (C (w (z,t)) ψ) = _
        rw [h]
        rfl
  have hOrig (z : ℝ) : Measurable (fun x : ℝ × ℝ => H (C z x.1) (fiber z x.1 x.2)) := hH.comp
    (show Measurable (fun x : ℝ × ℝ => (C z x.1, fiber z x.1 x.2)) by
      unfold C SphereGeom.Aux.Pair.cylinder fiber circlePt frame1 frame2
      fun_prop)
  have hJM : Measurable (fun x : (ℝ × ℝ) × ℝ => J (M x.1.1 x.1.2) x.2) :=
    hJ.comp (hM.comp measurable_fst |>.prodMk measurable_snd)
  change (∫⁻ z, ∫⁻ φ, ∫⁻ t, H (C z φ) (fiber z φ t) ∂ν ∂ν ∂μ) = _
  calc
    _ = ∫⁻ z, ∫⁻ t, ∫⁻ φ, H (C z φ) (fiber z φ t) ∂ν ∂ν ∂μ := by
      apply lintegral_congr; intro z
      exact lintegral_lintegral_swap (hOrig z).aemeasurable
    _ = ∫⁻ z, ∫⁻ t, ∫⁻ ψ, J (M z t) ψ ∂ν ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ae_of_ae_prod hW] with z hz hzt
      apply lintegral_congr_ae
      filter_upwards [hzt] with t ht
      exact hshift z t hz ht
    _ = ∫⁻ x, ∫⁻ ψ, J (M x.1 x.2) ψ ∂ν ∂μ.prod ν :=
      (lintegral_prod _ hJM.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ ψ, ∫⁻ x, J (M x.1 x.2) ψ ∂μ.prod ν ∂ν := lintegral_lintegral_swap hJM.aemeasurable
    _ = ∫⁻ ψ, ∫⁻ x, J x ψ ∂dOmega ∂ν := by
      apply lintegral_congr; intro ψ
      have hjs : Measurable (fun x : E3 => J x ψ) := hJ.comp (measurable_id.prodMk measurable_const)
      rw [← hmapM, lintegral_map hjs hM]
      rfl
    _ = ∫⁻ ψ, ∫⁻ z, ∫⁻ α, J (C z α) ψ ∂ν ∂μ ∂ν := by
      apply lintegral_congr; intro ψ
      have hjs : Measurable (fun x : E3 => J x ψ) := hJ.comp (measurable_id.prodMk measurable_const)
      rw [← hmapC, lintegral_map hjs hC]
      exact lintegral_prod _ (hjs.comp hC).aemeasurable
    _ = ∫⁻ ψ, ∫⁻ z, ∫⁻ α, H (fiber z ψ α) (C z ψ) ∂ν ∂μ ∂ν := by
      apply lintegral_congr; intro ψ
      apply lintegral_congr_ae
      filter_upwards [hZ] with z hz
      apply lintegral_congr; intro α
      simp only [J]
      rw [reciprocal_cylinder z α ψ hz]
      rfl
    _ = _ := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      apply Measurable.lintegral_prod_right (f := fun (x : ℝ × ℝ) α => H (fiber x.2 x.1 α) (C x.2 x.1))
      exact hH.comp (show Measurable (fun x : (ℝ × ℝ) × ℝ =>
        (fiber x.1.2 x.1.1 x.2, C x.1.2 x.1.1)) by
        unfold fiber circlePt frame1 frame2 C SphereGeom.Aux.Pair.cylinder
        fun_prop)
