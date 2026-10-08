import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_sigma_subsingleton
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.inactive_sigma_subsingleton :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) (hr : 1 ≤ Rc ‖D‖ ‖D - e‖), (SigmaD D).Subsingleton :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_sigma_subsingleton
