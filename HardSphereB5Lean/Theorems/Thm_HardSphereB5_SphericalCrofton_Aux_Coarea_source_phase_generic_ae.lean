import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_phase_generic_ae
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_phase_generic_ae :
    ∀ᵐ x : Chart5 ∂volume,
    (sourceCenter x ∈ LamC ∧ x 3 ∈ Set.Icc (-Real.pi) Real.pi ∧ x 4 ∈ Set.Icc (-Real.pi) Real.pi) →
    (sourceEndpointA x) 2 ≠ 0 ∧ (sourceEndpointB x) 2 ≠ 0 ∧
      inner ℝ (cross (u (sourceCenter x) (x 3)) (v (sourceCenter x) (x 4))) e ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_phase_generic_ae
