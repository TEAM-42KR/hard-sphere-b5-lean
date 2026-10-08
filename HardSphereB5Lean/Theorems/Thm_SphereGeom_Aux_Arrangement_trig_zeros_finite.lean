import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_trig_zeros_finite
import Mathlib
set_option autoImplicit false

theorem SphereGeom.Aux.Arrangement.trig_zeros_finite :
    ∀ (α β γ p q : ℝ) (hnonzero : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0), {t ∈ Set.Icc p q | α * Real.cos t + β * Real.sin t - γ = 0}.Finite :=
  @proof_SphereGeom_Aux_Arrangement_trig_zeros_finite
