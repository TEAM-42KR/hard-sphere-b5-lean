import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_volume_map : MeasurePreserving
    (fun x : Chart5 => (sourceCenter x, (x 3, x 4))) volume
      (volume.prod (volume.prod volume)) := by
  let q0 : Chart5 ≃ᵐ (Fin 5 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 5 → ℝ)).symm
  let q1 : (Fin 5 → ℝ) ≃ᵐ (ℝ × (Fin 4 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) 4
  let q2 : (ℝ × (Fin 4 → ℝ)) ≃ᵐ (ℝ × (ℝ × (Fin 3 → ℝ))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 3)
  let q3 : (ℝ × (ℝ × (Fin 3 → ℝ))) ≃ᵐ (ℝ × (ℝ × Pt)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
  let q4 : (ℝ × (ℝ × Pt)) ≃ᵐ ((ℝ × Pt) × ℝ) := MeasurableEquiv.prodComm
  let q5 : ((ℝ × Pt) × ℝ) ≃ᵐ ((Pt × ℝ) × ℝ) :=
    MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)
  let q6 : ((Pt × ℝ) × ℝ) ≃ᵐ (Pt × (ℝ × ℝ)) := MeasurableEquiv.prodAssoc
  let q := q0.trans (q1.trans (q2.trans (q3.trans (q4.trans (q5.trans q6)))))
  have h0 : MeasurePreserving q0 volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 5)
  have h1 : MeasurePreserving q1 volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) 4
  have h2 : MeasurePreserving q2 volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 3)
  have h3 : MeasurePreserving q3 volume volume :=
    (MeasurePreserving.id volume).prod ((MeasurePreserving.id volume).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm)
  have h4 : MeasurePreserving q4 volume volume := Measure.measurePreserving_swap
  have h5 : MeasurePreserving q5 volume volume := Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have h6 : MeasurePreserving q6 volume volume := volume_preserving_prodAssoc
  have hq : MeasurePreserving q volume (volume.prod (volume.prod volume)) :=
    h6.comp (h5.comp (h4.comp (h3.comp (h2.comp (h1.comp h0)))))
  have he : (fun x : Chart5 => (sourceCenter x, (x 3, x 4))) = q := by
    funext x
    apply Prod.ext
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [q, q0, q1, q2, q3, q4, q5, q6, sourceCenter,
        HardSphereB5.Lean.e, e1, e2, MeasurableEquiv.piFinSuccAbove]
      all_goals rfl
    · rfl
  rw [he]
  exact hq
