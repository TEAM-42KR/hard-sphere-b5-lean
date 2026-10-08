import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_kernel_partition
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.boundary_kernel_partition :
    ∀ (f : Kern) (D : Pt) (hA : MeasurableSet (arcA D)) (hB : MeasurableSet (arcB D)) (hAB : arcMeasure (arcA D ∩ arcB D) = 0) (hAf : arcMeasure (arcA D) < ⊤) (hBf : arcMeasure (arcB D) < ⊤) (hInt : Integrable (pairKernel f D) (pairMu D)), (1 / 2 : ℝ) * (∫ q, pairKernel f D q ∂pairMu D) = AAf f D + BBf f D + ABf f D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_kernel_partition
