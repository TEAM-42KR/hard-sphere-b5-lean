import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_endpointCylinderMeasures
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped ENNReal

theorem HardSphereB5.SphericalCrofton.Aux.Flat.endpointCylinderMeasures :
    ((sphereMeasure 0).restrict FA =
      (1 / 2 : ℝ≥0∞) • (((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.cos x.2) • e1 +
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.sin x.2) • e2 + (1 - x.1 / 2) • e)) ∧
    ((sphereMeasure e).restrict FB =
      (1 / 2 : ℝ≥0∞) • (((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.cos x.2) • e1 +
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.sin x.2) • e2 + (x.1 / 2) • e)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_endpointCylinderMeasures
