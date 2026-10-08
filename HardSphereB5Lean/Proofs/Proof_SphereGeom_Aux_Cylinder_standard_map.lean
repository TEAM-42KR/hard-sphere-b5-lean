import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_radial_map_volume
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_dOmega_normalize
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_norm_chart
set_option autoImplicit false

open MeasureTheory SphereGeom
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem proof_SphereGeom_Aux_Cylinder_standard_map :
    dOmega =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi))).map
        (fun x : ℝ × ℝ => (WithLp.toLp 2
          ![Real.sqrt (1-x.1^2) * Real.cos x.2,
            Real.sqrt (1-x.1^2) * Real.sin x.2, x.1] : E3)) := by
  let A : Set (Fin 3 → ℝ) := {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧
    0 < x 2 ∧ x 2 < 2 * Real.pi}
  let B : Set (Fin 3 → ℝ) := {x | 0 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 1 ∧
    0 < x 2 ∧ x 2 < 2 * Real.pi}
  let J : Set (ℝ × ℝ) := Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)
  let D : Set (ℝ × (ℝ × ℝ)) := Set.Ioo (0 : ℝ) 1 ×ˢ J
  let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun x =>
    ![x 0 * Real.sqrt (1-(x 1)^2) * Real.cos (x 2),
      x 0 * Real.sqrt (1-(x 1)^2) * Real.sin (x 2), x 0 * x 1]
  let F : (Fin 3 → ℝ) → E3 := fun x => WithLp.toLp 2 (f x)
  let g : (ℝ × ℝ) → E3 := fun x => WithLp.toLp 2
    ![Real.sqrt (1-x.1^2) * Real.cos x.2,
      Real.sqrt (1-x.1^2) * Real.sin x.2, x.1]
  let N : E3 → E3 := fun u => (‖u‖⁻¹ : ℝ) • u
  let w : (Fin 3 → ℝ) → ENNReal := fun x => ENNReal.ofReal ((x 0)^2)
  let ν : Measure (Fin 3 → ℝ) := ((volume : Measure (Fin 3 → ℝ)).restrict A).withDensity w
  let μ : Measure (Fin 3 → ℝ) := ((volume : Measure (Fin 3 → ℝ)).restrict B).withDensity w
  have hF : Measurable F := by apply Continuous.measurable; fun_prop
  have hf : Measurable f := by apply Continuous.measurable; fun_prop
  have hg : Measurable g := by apply Continuous.measurable; fun_prop
  have hN : Measurable N := measurable_norm.inv.smul measurable_id
  have hν : ν.map F = (volume : Measure E3) := by
    calc
      ν.map F = (ν.map f).map (WithLp.toLp 2) :=
        (Measure.map_map (PiLp.volume_preserving_toLp (Fin 3)).measurable hf).symm
      _ = (volume : Measure (Fin 3 → ℝ)).map (WithLp.toLp 2) := by
        rw [SphereGeom.Aux.Cylinder.radial_map_volume]
      _ = volume := (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  let C : Set E3 := Metric.ball (0 : E3) 1 \ {0}
  have hC : MeasurableSet C := measurableSet_ball.diff (measurableSet_singleton 0)
  have hpre : F ⁻¹' C ∩ A = B := by
    ext x
    change (F x ∈ C ∧ x ∈ A) ↔ x ∈ B
    by_cases ha : x ∈ A
    · have hnorm : ‖F x‖ = x 0 := by
        simpa [F, f, abs_of_pos ha.1] using
          SphereGeom.Aux.Cylinder.norm_chart (x 0) (x 1) (x 2)
            ⟨ha.2.1.le, ha.2.2.1.le⟩
      have hnz : F x ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hnorm
        linarith [ha.1]
      simp only [C, Set.mem_diff, Metric.mem_ball, dist_zero_right,
        hnorm, Set.mem_singleton_iff, hnz, not_false_eq_true, and_true,
        ha, B, Set.mem_setOf_eq]
      exact ⟨fun ht => ⟨ha.1, ht, ha.2⟩, fun hx => hx.2.1⟩
    · constructor
      · exact fun h => False.elim (ha h.2)
      · intro hx
        exact False.elim (ha ⟨hx.1, hx.2.2⟩)
  have hball : μ.map F = (volume : Measure E3).restrict C := by
    rw [← hν, Measure.restrict_map hF hC]
    congr 1
    change ((volume : Measure (Fin 3 → ℝ)).restrict B).withDensity w =
      (((volume : Measure (Fin 3 → ℝ)).restrict A).withDensity w).restrict (F ⁻¹' C)
    rw [restrict_withDensity (hF hC), Measure.restrict_restrict (hF hC), hpre]
  let t : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)
  have htval (x : Fin 3 → ℝ) : t x = (x 0, (x 1, x 2)) := rfl
  have ht : MeasurePreserving t (volume : Measure (Fin 3 → ℝ))
      (volume : Measure (ℝ × (ℝ × ℝ))) := by
    exact (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
      (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  have hD : MeasurableSet D := measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hB : t ⁻¹' D = B := by ext x; simp [htval, D, B, J, and_assoc]
  have htv : ((volume : Measure (Fin 3 → ℝ)).restrict B).map t =
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict D := by
    simpa only [hB] using (ht.restrict_preimage hD).map_eq
  let νr : Measure ℝ := ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).withDensity
    (fun r => ENNReal.ofReal (r^2))
  let ang : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).restrict J
  have htdens : μ.map t = (νr.prod ang) := by
    have hw : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (p.1^2)) := by fun_prop
    calc
      μ.map t = ((volume : Measure (ℝ × (ℝ × ℝ))).restrict D).withDensity
          (fun p => ENNReal.ofReal (p.1^2)) := by
        ext s hs
        rw [Measure.map_apply t.measurable hs, withDensity_apply _ (t.measurable hs),
          withDensity_apply _ hs, ← htv, setLIntegral_map hs hw t.measurable]
        rfl
      _ = νr.prod ang := by
        dsimp only [νr]
        rw [prod_withDensity_left (by fun_prop), Measure.prod_restrict]
        rfl
  have hNF : (fun x => N (F x)) =ᵐ[μ] (fun x => g (t x).2) := by
    have hw : Measurable w := by fun_prop
    apply (ae_withDensity_iff hw).2
    filter_upwards [ae_restrict_mem (by rw [← hB]; exact t.measurable hD)] with x hx
    intro _
    have hnorm : ‖F x‖ = x 0 := by
      simpa [F, f, abs_of_pos hx.1] using
        SphereGeom.Aux.Cylinder.norm_chart (x 0) (x 1) (x 2)
          ⟨hx.2.2.1.le, hx.2.2.2.1.le⟩
    have hrad : F x = x 0 • g (t x).2 := by
      ext i
      fin_cases i <;> simp [F, f, g, htval, PiLp.smul_apply, mul_assoc]
    dsimp only [N]
    rw [hnorm, hrad, smul_smul, inv_mul_cancel₀ hx.1.ne', one_smul]
  have hnormmap : ((volume : Measure E3).restrict C).map N =
      (νr Set.univ) • ang.map g := by
    calc
      ((volume : Measure E3).restrict C).map N = (μ.map F).map N := by rw [hball]
      _ = μ.map (N ∘ F) := Measure.map_map hN hF
      _ = μ.map ((g ∘ Prod.snd) ∘ t) := Measure.map_congr hNF
      _ = (μ.map t).map (g ∘ Prod.snd) :=
        (Measure.map_map (hg.comp measurable_snd) t.measurable).symm
      _ = (νr.prod ang).map (g ∘ Prod.snd) := by rw [htdens]
      _ = ((νr.prod ang).map Prod.snd).map g :=
        (Measure.map_map hg measurable_snd).symm
      _ = (νr Set.univ) • ang.map g := by
        rw [Measure.map_snd_prod, Measure.map_smul]
  have hmass : νr Set.univ = (3 : ENNReal)⁻¹ := by
    change (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).withDensity
      (fun r => ENNReal.ofReal (r^2))) Set.univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      restrict_Ioo_eq_restrict_Icc]
    have hi : Integrable (fun r : ℝ => r^2)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) :=
      (show Continuous (fun r : ℝ => r^2) from continuous_id.pow 2).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun r => sq_nonneg r))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_pow]
    norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    simp
  have hang : ang = (volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi)) := by
    apply Measure.restrict_congr_set
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Ico
  calc
    dOmega = (3 : ENNReal) • (((volume : Measure E3).restrict C).map N) :=
      SphereGeom.Aux.Cylinder.dOmega_normalize
    _ = (3 : ENNReal) • ((νr Set.univ) • ang.map g) := by rw [hnormmap]
    _ = ang.map g := by
      rw [hmass, smul_smul, ENNReal.mul_inv_cancel (by norm_num : (3 : ENNReal) ≠ 0)
        (by simp : (3 : ENNReal) ≠ ∞), one_smul]
    _ = _ := by rw [hang]
