import HardSphereB5Lean.Proofs.Proof_SolidGeom_sliceCap_integral_endpoint
import Mathlib
set_option autoImplicit false

theorem SolidGeom.sliceCap_integral_endpoint :
    ∀ (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1), (∫ z in (0 : ℝ)..Real.sqrt (1 - k ^ 2), Real.arccos (k / Real.sqrt (1 - z ^ 2))) =
    Real.pi * (1 - k) / 2 :=
  @proof_SolidGeom_sliceCap_integral_endpoint
