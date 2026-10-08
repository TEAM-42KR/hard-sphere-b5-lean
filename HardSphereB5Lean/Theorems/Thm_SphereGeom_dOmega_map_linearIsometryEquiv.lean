import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_map_linearIsometryEquiv
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_map_linearIsometryEquiv :
    ∀ (R : E3 ≃ₗᵢ[ℝ] E3), dOmega.map R = dOmega :=
  @proof_SphereGeom_dOmega_map_linearIsometryEquiv
