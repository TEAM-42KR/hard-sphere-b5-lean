import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_cross_arc_by_parts
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.cross_arc_by_parts :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1), ABf f D = 2 * Pprim f (min (deltaV D) (π / 3)) + Bf f D :=
  @proof_HardSphereB5_SphericalCrofton_cross_arc_by_parts
