import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_regular_ae
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_regular_ae :
    ∀ᵐ y : Chart5 ∂volume,
      (y 0 ∈ Set.Icc (1/2 : ℝ) 1 ∧ y 2 ∈ Set.Icc (-1 : ℝ) (-1/2) ∧
        y 1 ∈ Set.Icc (-Real.pi) Real.pi ∧ y 3 ∈ Set.Icc (-Real.pi) Real.pi ∧
        y 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
        0 < dist (targetEndpointA y) (targetEndpointB y) ∧
        dist (targetEndpointA y) (targetEndpointB y) < 1 ∧ targetCenter y ∈ LamC) →
      targetRegular y :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_regular_ae
