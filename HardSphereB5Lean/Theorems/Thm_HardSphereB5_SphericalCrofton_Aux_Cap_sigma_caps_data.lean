import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Cap.sigma_caps_data :
    ∀ (D : Pt) (hD0 : D ≠ 0) (hDe : D ≠ e), ‖nAv D‖ = 1 ∧ ‖nBv D‖ = 1 ∧ SigmaD D = cap (nAv D) (‖D‖ / 2) ∩ cap (nBv D) (‖D - e‖ / 2) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
