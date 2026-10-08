import HardSphereB5Lean.Theorems.Thm_SphereGeom_incidence_swap
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_orthogonal_frame_kernel
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_fullCircle_polar
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 2000000
private theorem unitPoint (a b p : E3) (h : Orthonormal ℝ ![a,b,p]) (t : ℝ) :
    ‖Real.cos t • a + Real.sin t • b‖ = 1 := by
  have haa : inner ℝ a a = 1 := by simpa using (orthonormal_iff_ite.mp h (0 : Fin 3) 0)
  have hbb : inner ℝ b b = 1 := by simpa using (orthonormal_iff_ite.mp h (1 : Fin 3) 1)
  have hab : inner ℝ a b = 0 := by simpa using (orthonormal_iff_ite.mp h (0 : Fin 3) 1)
  have hba : inner ℝ b a = 0 := by simpa using (orthonormal_iff_ite.mp h (1 : Fin 3) 0)
  have hs : ‖Real.cos t • a + Real.sin t • b‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      RCLike.conj_to_real, haa,hbb,hab,hba, mul_one,mul_zero,add_zero,zero_add]
    nlinarith [Real.cos_sq_add_sin_sq t]
  nlinarith [norm_nonneg (Real.cos t • a + Real.sin t • b)]
theorem proof_SphereGeom_lintegral_pair_greatCircle (F₁ F₂ : E3 → E3) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p,F₂ p,p])
    (g : E3 → E3 → ENNReal) (hg : Measurable (Function.uncurry g)) :
    ∫⁻ u, ∫⁻ v, g u v ∂dOmega ∂dOmega =
      (1/2 : ENNReal) * ∫⁻ p, ∫⁻ t₁ in Set.Ioc 0 (2*Real.pi), ∫⁻ t₂ in Set.Ioc 0 (2*Real.pi),
        g (Real.cos t₁ • F₁ p + Real.sin t₁ • F₂ p) (Real.cos t₂ • F₁ p + Real.sin t₂ • F₂ p) *
          ENNReal.ofReal |Real.sin (t₁-t₂)| ∂volume ∂volume ∂dOmega := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 (2*Real.pi))
  let P : E3 → ℝ → E3 := fun p t => Real.cos t • F₁ p + Real.sin t • F₂ p
  let Q : E3 → E3 → ENNReal := fun p u => ∫⁻ v, g u (P p v) *
    ENNReal.ofReal (Real.sqrt (1-(inner ℝ u (P p v))^2)) ∂ν
  have hQ : Measurable (Function.uncurry Q) := Measurable.lintegral_prod_right
    (f := fun x : E3 × E3 => fun t => g x.2 (P x.1 t) *
      ENNReal.ofReal (Real.sqrt (1-(inner ℝ x.2 (P x.1 t))^2)))
    (show Measurable (fun x : (E3 × E3) × ℝ => g x.1.2 (P x.1.1 x.2) *
      ENNReal.ofReal (Real.sqrt (1-(inner ℝ x.1.2 (P x.1.1 x.2))^2))) by
      have hgp : Measurable (fun x : (E3 × E3) × ℝ => g x.1.2 (P x.1.1 x.2)) :=
        hg.comp (show Measurable (fun x : (E3 × E3) × ℝ => (x.1.2,P x.1.1 x.2)) by dsimp [P]; fun_prop)
      exact hgp.mul (by dsimp [P]; fun_prop))
  have hAE : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have hm : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : E3) 1 := ae_iff.mpr dOmega_compl_sphere
    filter_upwards [hm] with p hp
    simpa [Metric.mem_sphere,dist_zero_right] using hp
  have hpair : (∫⁻ p, ∫⁻ t, Q p (P p t) ∂ν ∂dOmega) =
      ∫⁻ p, ∫⁻ t₁, ∫⁻ t₂, g (P p t₁) (P p t₂) * ENNReal.ofReal |Real.sin (t₁-t₂)| ∂ν ∂ν ∂dOmega := by
    apply lintegral_congr_ae
    filter_upwards [hAE] with p hp
    apply lintegral_congr; intro t₁
    apply lintegral_congr; intro t₂
    have h := (SphereGeom.Aux.Pair.orthogonal_frame_kernel (F₁ p) (F₂ p) p (hF p hp)).1 t₁ t₂
    change g (P p t₁) (P p t₂) * _ = _
    rw [h]
  have hpolar : (∫⁻ u, ∫⁻ t, Q (P u t) u ∂ν ∂dOmega) = 2 * ∫⁻ u, ∫⁻ v, g u v ∂dOmega ∂dOmega := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ENNReal) ≠ ⊤)]
    apply lintegral_congr_ae
    filter_upwards [hAE] with u hu
    have hgu : Measurable (g u) := hg.comp (measurable_const.prodMk measurable_id)
    calc
      (∫⁻ t, Q (P u t) u ∂ν) = ∫⁻ t, ∫⁻ s, g u (Real.cos s • u +
          Real.sin s • (-Real.sin t • F₁ u + Real.cos t • F₂ u)) * ENNReal.ofReal |Real.sin s| ∂ν ∂ν := by
        apply lintegral_congr; intro t
        have hp : ‖P u t‖ = 1 := unitPoint (F₁ u) (F₂ u) u (hF u hu) t
        exact (SphereGeom.Aux.Pair.orthogonal_frame_kernel (F₁ (P u t)) (F₂ (P u t)) (P u t)
          (hF _ hp)).2 u (F₁ u) (F₂ u) (hF u hu) t rfl (g u) hgu
      _ = _ := SphereGeom.Aux.Pair.fullCircle_polar (F₁ u) (F₂ u) u (hF u hu) (g u) hgu
  have hs := SphereGeom.incidence_swap F₁ F₂ hF₁ hF₂ hF Q hQ
  change (∫⁻ p, ∫⁻ t, Q p (P p t) ∂ν ∂dOmega) = (∫⁻ u, ∫⁻ t, Q (P u t) u ∂ν ∂dOmega) at hs
  rw [hpair,hpolar] at hs
  change (∫⁻ u, ∫⁻ v, g u v ∂dOmega ∂dOmega) = (1/2 : ENNReal) * _
  rw [hs, ← mul_assoc]
  have hhalf : (1/2 : ENNReal) * 2 = 1 := by
    simp only [div_eq_mul_inv,one_mul,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [hhalf,one_mul]
