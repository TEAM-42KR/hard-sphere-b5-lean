import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsJointMeasure
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 700000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_foldedEndpointIntegral (K : Pt → Pt → ℝ)
    (hq : Integrable (fun p : (ℝ × ℝ) × ℝ => K (pRep p.1.1) (pRep2 p.1.2 p.2))
      ((((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 1))).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)))) :
    (∫ p : (ℝ × ℝ) × ℝ, K (pRep p.1.1) (pRep2 p.1.2 p.2)
      ∂((((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 1))).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)))) =
      ∫ v in Dfull,
        (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
          K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) /
            Real.sqrt (Hpoly v.1 v.2.1 v.2.2)  := by
  let μXY := ((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
    ((volume : Measure ℝ).restrict (Set.Ioo 0 1))
  let E : Set ((ℝ × ℝ) × ℝ) := {p | 0 < Hpoly p.1.1 p.1.2 p.2}
  let M : Measure ((ℝ × ℝ) × ℝ) := (μXY.prod volume).restrict E
  let w : (ℝ × ℝ) × ℝ → ℝ≥0 := fun p => Real.toNNReal (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2))
  let ν := M.withDensity (fun p => (w p : ℝ≥0∞))
  let fp : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, chiPlus p.1.1 p.1.2 p.2)
  let fm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, -chiPlus p.1.1 p.1.2 p.2)
  let q : (ℝ × ℝ) × ℝ → ℝ := fun p => K (pRep p.1.1) (pRep2 p.1.2 p.2)
  let G : ℝ × ℝ × ℝ → ℝ := fun v =>
    (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
      K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) / Real.sqrt (Hpoly v.1 v.2.1 v.2.2)
  let T : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) := MeasurableEquiv.prodAssoc
  have hE : MeasurableSet E := by unfold E Hpoly; measurability
  have hD : MeasurableSet Dfull := by unfold Dfull Hpoly; measurability
  have hw : Measurable w := by unfold w Hpoly; fun_prop
  have hfp : Measurable fp := by unfold fp chiPlus a0 b0; fun_prop
  have hfm : Measurable fm := by unfold fm chiPlus a0 b0; fun_prop
  have hmaps : ν.map fp + ν.map fm = μXY.prod (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    HardSphereB5.SphericalCrofton.Aux.Flat.bothSheetsJointMeasure
  have hqν : Integrable q (ν.map fp + ν.map fm) := by rw [hmaps]; exact hq
  have hp : Integrable q (ν.map fp) := hqν.left_of_add_measure
  have hm : Integrable q (ν.map fm) := hqν.right_of_add_measure
  have hpc : Integrable (fun p => q (fp p)) ν := hp.comp_measurable hfp
  have hmc : Integrable (fun p => q (fm p)) ν := hm.comp_measurable hfm
  have hpw : Integrable (fun p => w p • q (fp p)) M :=
    (integrable_withDensity_iff_integrable_smul hw).mp hpc
  have hmw : Integrable (fun p => w p • q (fm p)) M :=
    (integrable_withDensity_iff_integrable_smul hw).mp hmc
  have heq : (fun p => w p • q (fp p) + w p • q (fm p)) = G ∘ T := by
    funext p
    change (w p : ℝ) * q (fp p) + (w p : ℝ) * q (fm p) = _
    rw [show (w p : ℝ) = 1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2) from
      Real.coe_toNNReal _ (by positivity)]
    change (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2)) *
      K (pRep p.1.1) (pRep2 p.1.2 (chiPlus p.1.1 p.1.2 p.2)) +
      (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2)) *
      K (pRep p.1.1) (pRep2 p.1.2 (-chiPlus p.1.1 p.1.2 p.2)) =
      (K (pRep p.1.1) (pRep2 p.1.2 (chiPlus p.1.1 p.1.2 p.2)) +
        K (pRep p.1.1) (pRep2 p.1.2 (-chiPlus p.1.1 p.1.2 p.2))) /
          Real.sqrt (Hpoly p.1.1 p.1.2 p.2)
    ring
  have hbase : μXY.prod (volume : Measure ℝ) =
      (volume : Measure ((ℝ × ℝ) × ℝ)).restrict
        ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ×ˢ Set.univ) := by
    unfold μXY
    rw [Measure.prod_restrict]
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ := (volume : Measure (ℝ × ℝ)))
        (ν := (volume : Measure ℝ)) (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) Set.univ)
  have hM : M.map T = (volume : Measure (ℝ × ℝ × ℝ)).restrict Dfull := by
    unfold M
    rw [hbase, Measure.restrict_restrict hE]
    have hpre : E ∩ ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ×ˢ Set.univ) = T ⁻¹' Dfull := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true,
        Set.mem_preimage, E, Dfull, Set.mem_setOf_eq]
      dsimp [T]
      tauto
    rw [hpre, ← Measure.restrict_map T.measurable hD]
    congr 1
    exact (measurePreserving_prodAssoc (volume : Measure ℝ) volume volume).map_eq
  change (∫ p, q p ∂μXY.prod (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) = ∫ v in Dfull, G v
  rw [← hmaps, integral_add_measure hp hm, integral_map hfp.aemeasurable hp.aestronglyMeasurable,
    integral_map hfm.aemeasurable hm.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_smul hw, integral_withDensity_eq_integral_smul hw,
    ← integral_add hpw hmw, heq]
  rw [← hM]
  exact (T.measurableEmbedding.integral_map G).symm
