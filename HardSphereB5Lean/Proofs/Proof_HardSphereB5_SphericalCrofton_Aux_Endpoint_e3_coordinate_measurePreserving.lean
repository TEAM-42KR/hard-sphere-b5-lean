import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_e3_coordinate_measurePreserving : MeasurePreserving (fun x : SphereGeom.E3 => ((x 0,x 1),x 2))
    (volume : Measure SphereGeom.E3) ((volume : Measure (ℝ×ℝ)).prod (volume : Measure ℝ)) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2:Fin 3)
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  have h4 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ×ℝ)))
  have h := h4.comp (h3.comp (h2.comp h1))
  convert! h using 1 <;> first | rfl | (funext x; ext <;> rfl)
