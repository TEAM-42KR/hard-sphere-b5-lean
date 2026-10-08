import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_phase_generic_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_of_generic
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_ae : ∀ᵐ x : Chart5 ∂volume,
    (offAxis (sourceCenter x) ∧ sourceCenter x ∈ LamC ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x - e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1) → sourceRegular x := by
  have hcoord (i : Fin 5) (c : ℝ) : ∀ᵐ x : Chart5 ∂volume, x i ≠ c := by
    exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 5)).quasiMeasurePreserving.ae
      (Measure.ae_eval_ne (μ := fun _ : Fin 5 => (volume : Measure ℝ)) i c)
  filter_upwards [source_phase_generic_ae, hcoord 3 (-Real.pi), hcoord 3 Real.pi,
    hcoord 4 (-Real.pi), hcoord 4 Real.pi] with x hx ha0 ha1 hb0 hb1 hAnte
  have hα : x 3 ∈ Set.Icc (-Real.pi) Real.pi := by
    have hbound : halfA (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
    exact ⟨by linarith [hAnte.2.2.2.1.1], by linarith [hAnte.2.2.2.1.2]⟩
  have hβ : x 4 ∈ Set.Icc (-Real.pi) Real.pi := by
    have hbound : halfB (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
    exact ⟨by linarith [hAnte.2.2.2.2.1.1], by linarith [hAnte.2.2.2.2.1.2]⟩
  have hgeneric := hx ⟨hAnte.2.1, hα, hβ⟩
  exact source_regular_of_generic x hAnte ha0 ha1 hb0 hb1 hgeneric.1 hgeneric.2.1 hgeneric.2.2
