import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_flat_measure_target
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.flat_measure_target :
    ∀ (f : Kern), frakB f = π * ∫ v in Dnear,
      (1 / √(Hpoly v.1 v.2.1 v.2.2)) * (rhoK f (1 - v.2.2 / 2) / √v.2.2) *
        circInt (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) :=
  @proof_HardSphereB5_SphericalCrofton_flat_measure_target
