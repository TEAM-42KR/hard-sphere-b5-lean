import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinates_preserving :
    MeasurePreserving (fun x : Chart5 => (sourceCenter x, x 3, x 4))
      (volume : Measure Chart5) (volume : Measure (Pt × ℝ × ℝ))  := by
  let q : (Fin 5 → ℝ) ≃ᵐ ((Fin 3 ⊕ Fin 2) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ⊕ Fin 2 => ℝ) (finSumFinEquiv.symm)
  let s : ((Fin 3 ⊕ Fin 2) → ℝ) ≃ᵐ ((Fin 3 → ℝ) × (Fin 2 → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 2 => ℝ)
  let r : ((Fin 3 → ℝ) × (Fin 2 → ℝ)) ≃ᵐ (Pt × ℝ × ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have hq : MeasurePreserving q := volume_measurePreserving_piCongrLeft _ _
  have hs : MeasurePreserving s := volume_measurePreserving_sumPiEquivProdPi _
  have hr : MeasurePreserving r :=
    (PiLp.volume_preserving_toLp (Fin 3)).prod (volume_preserving_piFinTwo _)
  have hh := hr.comp (hs.comp (hq.comp (PiLp.volume_preserving_ofLp (Fin 5))))
  have heq : (r ∘ s ∘ q ∘ WithLp.ofLp) =
      (fun x : Chart5 => (sourceCenter x, x 3, x 4)) := by
    funext x
    dsimp only [r,s,q,Function.comp_def,MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi,MeasurableEquiv.prodCongr,MeasurableEquiv.piFinTwo]
    clear hh hr hs hq r s q
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [sourceCenter,e,e1,e2,finSumFinEquiv,Equiv.piCongrLeft]
    · apply Prod.ext <;> simp [finSumFinEquiv,Equiv.piCongrLeft]
  simpa only [heq] using hh

