import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_coordinates_preserving :
    MeasurePreserving (fun y : Chart5 => (((y 0,y 1),(y 2,y 3)),y 4))
      (volume : Measure Chart5) (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)) := by
  let q : (Fin 4 → ℝ) ≃ᵐ ((Fin 2 ⊕ Fin 2) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ) (finSumFinEquiv.symm)
  let s : ((Fin 2 ⊕ Fin 2) → ℝ) ≃ᵐ ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  let r : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) ≃ᵐ ((ℝ × ℝ) × (ℝ × ℝ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have hq : MeasurePreserving q := volume_measurePreserving_piCongrLeft _ _
  have hs : MeasurePreserving s := volume_measurePreserving_sumPiEquivProdPi _
  have hr : MeasurePreserving r :=
    (volume_preserving_piFinTwo _).prod (volume_preserving_piFinTwo _)
  have hsplit := hr.comp (hs.comp hq)
  have hlast := volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) (4 : Fin 5)
  have hfirst : MeasurePreserving (WithLp.ofLp : Chart5 → (Fin 5 → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin 5)
  have hh := (hsplit.prod (MeasurePreserving.id (volume : Measure ℝ))).comp
    (Measure.measurePreserving_swap.comp (hlast.comp hfirst))
  have heq : (Prod.map (r ∘ s ∘ q) id ∘ Prod.swap ∘
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (4 : Fin 5) ∘ WithLp.ofLp) =
      (fun y : Chart5 => (((y 0,y 1),(y 2,y 3)),y 4)) := by
    funext y
    dsimp only [r,s,q,Function.comp_def,Prod.map_apply,Prod.swap,
      MeasurableEquiv.piCongrLeft,MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.prodCongr,MeasurableEquiv.piFinTwo,MeasurableEquiv.piFinSuccAbove]
    clear hh hsplit hlast hr hs hq r s q
    simp [finSumFinEquiv,Equiv.piCongrLeft,Fin.insertNthEquiv,Fin.removeNth,Fin.succAbove]
  simpa only [heq,Measure.volume_eq_prod] using hh
