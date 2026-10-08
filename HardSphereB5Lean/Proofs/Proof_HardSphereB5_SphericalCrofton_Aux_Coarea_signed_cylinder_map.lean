import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_cylinder_map : dOmega =
    ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)).map
        (fun x : ℝ × ℝ => endpointCylinder x.1 x.2)  := by
  let I : Set ℝ := Set.Icc (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ I
  let T : ℝ × ℝ → ℝ × ℝ := fun x => (x.1,x.2+Real.pi)
  let C : ℝ × ℝ → Pt := fun x =>
    (Real.sqrt (1-x.1^2)*Real.cos x.2) • (-e1) +
    (Real.sqrt (1-x.1^2)*Real.sin x.2) • (-e2) + x.1 • e
  have hf : Orthonormal ℝ ![-e1,-e2,e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [e1,e2,e,EuclideanSpace.inner_single_left]
  have hC : Measurable C := by dsimp [C]; fun_prop
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hφ : ((volume : Measure ℝ).restrict I).map (fun t => t+Real.pi) =
      volume.restrict (Set.Ico (0 : ℝ) (2*Real.pi)) := by
    rw [restrict_Ico_eq_restrict_Icc]
    have hp := measurePreserving_add_right (volume : Measure ℝ) Real.pi
    have he := (MeasurableEquiv.addRight Real.pi).measurableEmbedding
    have hh := (hp.restrict_image_emb he I).map_eq
    have himage : (fun t : ℝ => t+Real.pi) '' I = Set.Icc 0 (2*Real.pi) := by
      change (fun t : ℝ => t+Real.pi) '' Set.Icc (-Real.pi) Real.pi = _
      rw [Set.image_add_const_Icc]
      congr 1 <;> ring
    simpa only [himage] using hh
  have hm : (volume.restrict S).map T =
      (volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2*Real.pi)) := by
    change (((volume : Measure ℝ).prod volume).restrict S).map T = _
    dsimp [S]
    rw [← Measure.prod_restrict]
    rw [show T = Prod.map id (fun t : ℝ => t+Real.pi) by rfl]
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hφ,
      Measure.prod_restrict]
    rfl
  have hc : (fun x => C (T x)) = (fun x : ℝ × ℝ => endpointCylinder x.1 x.2) := by
    funext x
    simp [C,T,endpointCylinder,Real.cos_add_pi,Real.sin_add_pi]
  have h := SphereGeom.dOmega_map_cylinder ![-e1,-e2,e] hf
  have hh : dOmega = ((volume.restrict S).map T).map C := by
    rw [hm]
    exact h
  rw [Measure.map_map hC hT] at hh
  simpa only [Function.comp_def, hc] using hh

