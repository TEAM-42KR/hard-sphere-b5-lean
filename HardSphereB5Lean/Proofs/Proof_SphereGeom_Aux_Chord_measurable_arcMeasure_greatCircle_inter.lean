import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Classical
noncomputable section

theorem proof_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter (A : Set E3) (hA : MeasurableSet A) :
    Measurable (fun p : E3 => arcMeasure (greatCircle p ∩ A)) := by
  obtain ⟨F₁, F₂, hF₁, hF₂, hF⟩ := exists_measurable_frame
  let N : E3 → E3 := fun p => ‖p‖⁻¹ • p
  have hN : Measurable N := measurable_id.norm.inv.smul measurable_id
  let B : E3 × ℝ → E3 := fun z => circlePt 0 (F₁ (N z.1)) (F₂ (N z.1)) 1 z.2
  have hB : Measurable B := by
    dsimp only [B, circlePt]
    simp only [zero_add, one_smul]
    exact ((Real.continuous_cos.measurable.comp measurable_snd).smul
      (hF₁.comp (hN.comp measurable_fst))).add
      ((Real.continuous_sin.measurable.comp measurable_snd).smul
        (hF₂.comp (hN.comp measurable_fst)))
  let μ : Measure ℝ := volume.restrict (Set.Icc (-Real.pi) Real.pi)
  letI : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let g : E3 → ENNReal := fun p => μ ((fun t => B (p, t)) ⁻¹' A)
  have hg : Measurable g := by
    change Measurable (fun p : E3 => μ (Prod.mk p ⁻¹' (B ⁻¹' A)))
    exact measurable_measure_prodMk_left (ν := μ) (hB hA)
  have heq (p : E3) (hp : p ≠ 0) : arcMeasure (greatCircle p ∩ A) = g p := by
    have hnorm : ‖N p‖ = 1 := norm_smul_inv_norm hp
    have hcircle : greatCircle (N p) = greatCircle p := by
      ext u
      simp only [greatCircle, Set.mem_setOf_eq, N, real_inner_smul_left,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, hp, false_or]
    have hm : Measurable (fun t : ℝ => B (p, t)) := hB.comp measurable_prodMk_left
    calc
      arcMeasure (greatCircle p ∩ A) = (arcMeasure.restrict (greatCircle (N p))) A := by
        rw [Measure.restrict_apply hA, hcircle, Set.inter_comm]
      _ = (μ.map (fun t => B (p, t))) A :=
        congrArg (fun ν : Measure E3 => ν A)
          (Aux.Pair.arcMeasure_greatCircle_frame (F₁ (N p)) (F₂ (N p)) (N p)
            (hF (N p) hnorm))
      _ = g p := Measure.map_apply hm hA
  have hpiece : Measurable (fun p : E3 =>
      if p = 0 then arcMeasure (greatCircle 0 ∩ A) else g p) :=
    Measurable.ite (measurableSet_singleton (0 : E3)) measurable_const hg
  convert hpiece using 1
  ext p
  by_cases hp : p = 0
  · subst p
    simp
  · simp only [if_neg hp]
    exact heq p hp

#print axioms proof_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
