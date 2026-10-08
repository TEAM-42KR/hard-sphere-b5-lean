import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_rectangle_pointwise
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_rectangle_pointwise :
    ∀ (y : Chart5)
    (h0 : y 0 ∈ Set.Ioo (1/2 : ℝ) 1) (h2 : y 2 ∈ Set.Ioo (-1 : ℝ) (-1/2))
    (h1 : y 1 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h3 : y 3 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h4 : y 4 ∈ Set.Ioo (-Real.pi) Real.pi) (h13 : y 1 ≠ y 3)
    (hz0 : 0 < dist (targetEndpointA y) (targetEndpointB y))
    (hz1 : dist (targetEndpointA y) (targetEndpointB y) < 1)
    (hD : targetCenter y ∈ LamC), targetRegular y :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_rectangle_pointwise
