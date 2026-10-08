import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_arg_inverse
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.endpoint_arg_inverse :
    ∀ (p : Pt) (hp : ‖p‖ = 1) (h0 : |p 0| < 1), (Real.sqrt (1 - (p 0)^2) * Real.cos (Complex.arg ((p 1 : ℂ) + Complex.I * (p 2 : ℂ)))) • e1 +
    (Real.sqrt (1 - (p 0)^2) * Real.sin (Complex.arg ((p 1 : ℂ) + Complex.I * (p 2 : ℂ)))) • e2 +
    (p 0) • e = p :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_arg_inverse
