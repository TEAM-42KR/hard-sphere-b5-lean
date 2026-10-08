import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_smooth
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_smooth :
    ∀ (x : Chart5)
    (hD : sourceCenter x ≠ 0) (hDe : sourceCenter x ≠ e)
    (hrA : ‖sourceCenter x‖ < 2) (hrB : ‖sourceCenter x - e‖ < 2)
    (hA : HardSphereB5.SphericalCrofton.Aux.MovingArc.rawA (sourceCenter x) ≠ 0)
    (hB : HardSphereB5.SphericalCrofton.Aux.MovingArc.rawB (sourceCenter x) ≠ 0)
    (hd : sourceEndpointB x - sourceEndpointA x ≠ 0)
    (hf : centerFrame0 (sourceEndpointB x - sourceEndpointA x) ≠ 0)
    (hphaseA : phase ((sourceEndpointA x) 1) ((sourceEndpointA x) 2) ∈ Complex.slitPlane)
    (hphaseB : phase ((sourceEndpointB x) 1) ((sourceEndpointB x) 2) ∈ Complex.slitPlane)
    (hphaseC : centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) ∈ Complex.slitPlane), ContDiffAt ℝ ⊤ Phi x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_smooth
