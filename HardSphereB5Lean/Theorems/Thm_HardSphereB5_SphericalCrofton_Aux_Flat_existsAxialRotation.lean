import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_existsAxialRotation
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Flat.existsAxialRotation :
    ∀ (t : ℝ), ∃ R : Pt ≃ₗᵢ[ℝ] Pt, IsAxialRotation R ∧
      ∀ a b c : ℝ, R (a • e1 + b • e2 + c • e) =
        (a * Real.cos t - b * Real.sin t) • e1 +
        (a * Real.sin t + b * Real.cos t) • e2 + c • e :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_existsAxialRotation
