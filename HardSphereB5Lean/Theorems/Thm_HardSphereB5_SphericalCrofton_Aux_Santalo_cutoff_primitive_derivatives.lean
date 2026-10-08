import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.cutoff_primitive_derivatives :
    ∀ (f : Kern) (d : ℝ), HasDerivAt (fun x : ℝ => Pprim f (min x (π / 3))) (cutKern f d) d ∧
      HasDerivAt (cutKern f) (if d < π / 3 then deriv (phiK f) d else 0) d :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives
