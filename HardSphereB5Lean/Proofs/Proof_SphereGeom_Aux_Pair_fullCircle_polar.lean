import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_halfCircle_lintegral
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_periodic_lintegral_translate
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

open MeasureTheory SphereGeom
set_option maxHeartbeats 1000000

theorem proof_SphereGeom_Aux_Pair_fullCircle_polar (c d u : E3) (hcd : Orthonormal ℝ ![c,d,u])
    (f : E3 → ENNReal) (hf : Measurable f) :
    (∫⁻ t in Set.Ioc 0 (2*Real.pi), ∫⁻ s in Set.Ioc 0 (2*Real.pi),
      f (Real.cos s • u + Real.sin s • (-Real.sin t • c + Real.cos t • d)) *
        ENNReal.ofReal |Real.sin s|) = 2 * ∫⁻ v, f v ∂dOmega := by
  let K : ℝ → E3 := fun t => -Real.sin t • c + Real.cos t • d
  let J : E3 → ENNReal := fun k =>
    ∫⁻ w in Set.Icc (-1 : ℝ) 1, f (w • u + Real.sqrt (1-w^2) • k)
  let G : ℝ → ENNReal := fun t => J (K t)
  let H : ℝ → ENNReal := fun t =>
    ∫⁻ w in Set.Icc (-1 : ℝ) 1,
      f ((Real.sqrt (1-w^2) * Real.cos t) • c +
        (Real.sqrt (1-w^2) * Real.sin t) • d + w • u)
  have hKpi (t : ℝ) : K (t + Real.pi) = -K t := by
    dsimp only [K]
    rw [Real.sin_add_pi, Real.cos_add_pi]
    module
  have hGperiod : Function.Periodic G (2*Real.pi) := by
    intro t
    simp only [G, K, Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hHperiod : Function.Periodic H (2*Real.pi) := by
    intro t
    simp only [H, Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hGmeas : Measurable G := by
    change Measurable (fun t : ℝ =>
      ∫⁻ w in Set.Icc (-1 : ℝ) 1, f (w • u + Real.sqrt (1-w^2) • K t))
    apply Measurable.lintegral_prod_right
    exact hf.comp (by dsimp [Function.uncurry, K]; fun_prop)
  have hfold (k : E3) :
      (∫⁻ s in Set.Ioc 0 (2*Real.pi),
        f (Real.cos s • u + Real.sin s • k) * ENNReal.ofReal |Real.sin s|) =
        J k + J (-k) := by
    let F : ℝ → ENNReal := fun s =>
      f (Real.cos s • u + Real.sin s • k) * ENNReal.ofReal |Real.sin s|
    have hF : Measurable F := by
      exact (hf.comp (by fun_prop)).mul (by fun_prop)
    have hpre : (fun s : ℝ => 2*Real.pi-s) ⁻¹' Set.Ioc Real.pi (2*Real.pi) =
        Set.Ico 0 Real.pi := by
      ext s
      simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
      constructor <;> intro hs <;> constructor <;> linarith [hs.1, hs.2]
    have hreflect :
        (∫⁻ s in Set.Ioc Real.pi (2*Real.pi), F s) =
          ∫⁻ s in Set.Ioc 0 Real.pi, F (2*Real.pi-s) := by
      have h := ((volume : Measure ℝ).measurePreserving_sub_left (2*Real.pi)).setLIntegral_comp_preimage
        (s := Set.Ioc Real.pi (2*Real.pi)) measurableSet_Ioc hF
      rw [hpre, restrict_Ico_eq_restrict_Ioc] at h
      exact h.symm
    have hfirst : (∫⁻ s in Set.Ioc 0 Real.pi, F s) = J k := by
      dsimp only [J]
      rw [SphereGeom.Aux.Pair.halfCircle_lintegral u k f hf]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le hs.2
      simp only [F, abs_of_nonneg hsin, mul_comm]
    have hsecond : (∫⁻ s in Set.Ioc Real.pi (2*Real.pi), F s) = J (-k) := by
      rw [hreflect]
      dsimp only [J]
      rw [SphereGeom.Aux.Pair.halfCircle_lintegral u (-k) f hf]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le hs.2
      dsimp only [F]
      rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub, abs_neg, abs_of_nonneg hsin]
      simp only [neg_smul, smul_neg]
      exact mul_comm _ _
    change (∫⁻ s in Set.Ioc 0 (2*Real.pi), F s) = _
    rw [← Set.Ioc_union_Ioc_eq_Ioc Real.pi_pos.le (by linarith [Real.pi_pos]),
      lintegral_union measurableSet_Ioc
        (Set.disjoint_left.2 (fun s hs ht => (not_lt_of_ge hs.2) ht.1)), hfirst, hsecond]
  have hshift (t : ℝ) : G t = H (t + Real.pi/2) := by
    dsimp [G, J, H]
    apply lintegral_congr
    intro w
    congr 1
    simp only [K, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, smul_add, smul_smul]
    abel
  have hHintegral : (∫⁻ t in Set.Ioc 0 (2*Real.pi), H t) = ∫⁻ v, f v ∂dOmega := by
    symm
    let P : ℝ × ℝ → E3 := fun x =>
      (Real.sqrt (1-x.1^2) * Real.cos x.2) • c +
      (Real.sqrt (1-x.1^2) * Real.sin x.2) • d + x.1 • u
    have hP : Measurable P := by fun_prop
    rw [SphereGeom.dOmega_map_cylinder ![c,d,u] hcd]
    change (∫⁻ v, f v ∂(((volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico 0 (2*Real.pi))).map P)) = _
    rw [lintegral_map hf hP, Measure.volume_eq_prod,
      setLIntegral_prod_symm (fun x : ℝ × ℝ => f (P x)) (hf.comp hP).aemeasurable,
      restrict_Ico_eq_restrict_Ioc]
  have hGintegral : (∫⁻ t in Set.Ioc 0 (2*Real.pi), G t) = ∫⁻ v, f v ∂dOmega := by
    calc
      _ = ∫⁻ t in Set.Ioc 0 (2*Real.pi), H (t+Real.pi/2) :=
        lintegral_congr hshift
      _ = ∫⁻ t in Set.Ioc 0 (2*Real.pi), H t := by
        simpa only [zero_add] using
          SphereGeom.Aux.Pair.periodic_lintegral_translate H (2*Real.pi)
            (by positivity) hHperiod 0 (Real.pi/2)
      _ = _ := hHintegral
  calc
    _ = ∫⁻ t in Set.Ioc 0 (2*Real.pi), G t + G (t+Real.pi) := by
      apply lintegral_congr
      intro t
      simpa only [G, hKpi] using hfold (K t)
    _ = (∫⁻ t in Set.Ioc 0 (2*Real.pi), G t) +
        ∫⁻ t in Set.Ioc 0 (2*Real.pi), G (t+Real.pi) :=
      lintegral_add_left hGmeas _
    _ = (∫⁻ t in Set.Ioc 0 (2*Real.pi), G t) +
        ∫⁻ t in Set.Ioc 0 (2*Real.pi), G t := by
      rw [show (∫⁻ t in Set.Ioc 0 (2*Real.pi), G (t+Real.pi)) =
          ∫⁻ t in Set.Ioc 0 (2*Real.pi), G t from by
        simpa only [zero_add] using
          SphereGeom.Aux.Pair.periodic_lintegral_translate G (2*Real.pi)
            (by positivity) hGperiod 0 Real.pi]
    _ = 2 * ∫⁻ v, f v ∂dOmega := by rw [hGintegral, two_mul]
