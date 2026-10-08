import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsJointMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton
open scoped ENNReal

theorem HardSphereB5.SphericalCrofton.Aux.Flat.bothSheetsJointMeasure :
    let μXY := ((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
      ((volume : Measure ℝ).restrict (Set.Ioo 0 1))
    let ν := ((μXY.prod (volume : Measure ℝ)).restrict
      {p : (ℝ × ℝ) × ℝ | 0 < Hpoly p.1.1 p.1.2 p.2}).withDensity
      (fun p => ENNReal.ofReal (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2)))
    ν.map (fun p => (p.1, chiPlus p.1.1 p.1.2 p.2)) +
      ν.map (fun p => (p.1, -chiPlus p.1.1 p.1.2 p.2)) =
      μXY.prod ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsJointMeasure
