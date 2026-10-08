import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_primitive_explicit
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.primitive_explicit :
    ∀ (d : ℝ), Pprim .one d = d ^ 2 / 2 + 2 * Real.cos d - 2 + (√3 - π / 3) * d ∧
      Pprim .cos d = (π / 12 + √3 / 8) * d - d ^ 2 / 8 + Real.cos (2 * d) / 8 - 1 / 8 :=
  @proof_HardSphereB5_SphericalCrofton_primitive_explicit
