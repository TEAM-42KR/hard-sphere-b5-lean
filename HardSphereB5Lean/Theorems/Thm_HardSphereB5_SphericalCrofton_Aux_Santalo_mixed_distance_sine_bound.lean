import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_sine_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.mixed_distance_sine_bound :
    ∀ (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hC : IsChart D C) (t s : ℝ)
    (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), |deriv (fun z => deriv (delta D C z) s) t| ≤
      (Real.sin (delta D C t s))⁻¹ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_sine_bound
