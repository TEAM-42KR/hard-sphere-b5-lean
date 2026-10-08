import HardSphereB5Lean.Proofs.Proof_Gnomonic_planarRadialMeasure
import HardSphereB5Lean.Definitions.Def_Gnomonic_unitDisk
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.planarRadialMeasure :
    planarMeasure.map radialPair = ((volume : Measure (ℝ × ℝ)).restrict unitDisk).withDensity graphDensity :=
  @proof_Gnomonic_planarRadialMeasure
