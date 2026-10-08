import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_bKernel_uniform_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.bKernel_uniform_bound :
    ∀ (f : Kern) (D p q : Pt) (hD : D ∈ LamC) (hp : p ∈ arcA D) (hq : q ∈ arcB D), ‖bKernel f D p q‖ ≤ 4 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_bKernel_uniform_bound
