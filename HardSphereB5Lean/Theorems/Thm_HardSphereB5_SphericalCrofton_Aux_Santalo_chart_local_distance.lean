import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_distance
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.chart_local_distance :
    ∀ (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hC : IsChart D C) (a b : ℝ)
    (heq : u D C a = v D C b) (hv : u D C a ∈ vertsD D), ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
      c * ‖z - (a, b)‖ ≤ ‖u D C z.1 - v D C z.2‖ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_distance
