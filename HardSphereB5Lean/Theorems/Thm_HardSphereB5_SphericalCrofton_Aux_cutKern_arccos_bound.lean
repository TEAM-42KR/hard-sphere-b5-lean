import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.cutKern_arccos_bound :
    ∀ (f : Kern) (x : ℝ), 0 ≤ cutKern f (Real.arccos x) ∧ cutKern f (Real.arccos x) ≤ 6 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound
