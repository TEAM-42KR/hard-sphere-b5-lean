import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_test_integrable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_test_integrable :
    ∀ (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ q ∈ FB,
      dist D p = 1 → dist D q = 1 → 0 < dist p q → dist p q < 1 → |G D p q| ≤ C)
    (S : Set Chart5) (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, sourceCenter x ∈ LamC ∧
      x 3 ∈ Set.Icc (-Real.pi) Real.pi ∧ x 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      dist (sourceCenter x) (sourceEndpointA x) = 1 ∧
      dist (sourceCenter x) (sourceEndpointB x) = 1 ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1), IntegrableOn (fun x => G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
      (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) S volume :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_test_integrable
