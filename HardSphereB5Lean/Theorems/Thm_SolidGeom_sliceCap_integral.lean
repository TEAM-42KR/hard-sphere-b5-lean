import HardSphereB5Lean.Proofs.Proof_SolidGeom_sliceCap_integral
import Mathlib
set_option autoImplicit false

theorem SolidGeom.sliceCap_integral :
    ∀ (k h : ℝ) (hk0 : 0 < k) (hk1 : k < 1) (hh0 : 0 ≤ h) (hh : h ^ 2 < 1 - k ^ 2), (∫ z in (0 : ℝ)..h, Real.arccos (k / Real.sqrt (1 - z ^ 2))) =
    h * Real.arccos (k / Real.sqrt (1 - h ^ 2)) +
      Real.arctan (k * h / Real.sqrt (1 - k ^ 2 - h ^ 2)) -
      k * Real.arcsin (h / Real.sqrt (1 - k ^ 2)) :=
  @proof_SolidGeom_sliceCap_integral
