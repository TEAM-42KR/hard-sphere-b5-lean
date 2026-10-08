import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_Bf_uniform_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.Bf_uniform_bound :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC), ‖Bf f D‖ ≤ 16 * Real.pi ^ 2 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_Bf_uniform_bound
