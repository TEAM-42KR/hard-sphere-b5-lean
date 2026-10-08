import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_parameter_volume_eq_prod (S T U : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (F : ℝ × (ℝ × ℝ) → ENNReal) (hF : Measurable F) :
    (∫⁻ x : E3 in {x | x 0 ∈ S ∧ x 1 ∈ T ∧ x 2 ∈ U}, F (x 0, (x 1, x 2))) =
      ∫⁻ p : ℝ × (ℝ × ℝ) in S ×ˢ (T ×ˢ U), F p
        ∂(volume.prod (volume.prod volume)) := by
  let e0 : E3 ≃ᵐ (Fin 3 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e1 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e2 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow
  let e : E3 ≃ᵐ (ℝ × (ℝ × ℝ)) := e0.trans (e1.trans e2)
  have hp0 : MeasurePreserving e0 volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have hp1 : MeasurePreserving e1 volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hp2 : MeasurePreserving e2 volume (volume.prod (volume.prod volume)) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  have hp : MeasurePreserving e volume (volume.prod (volume.prod volume)) :=
    hp2.comp (hp1.comp hp0)
  have he (x : E3) : e x = (x 0, (x 1, x 2)) := by rfl
  have hpre : e ⁻¹' (S ×ˢ (T ×ˢ U)) =
      {x : E3 | x 0 ∈ S ∧ x 1 ∈ T ∧ x 2 ∈ U} := by
    ext x
    simp only [Set.mem_preimage, he, Set.mem_prod, Set.mem_setOf_eq]
  simpa only [hpre, he] using hp.setLIntegral_comp_preimage (hS.prod (hT.prod hU)) hF
