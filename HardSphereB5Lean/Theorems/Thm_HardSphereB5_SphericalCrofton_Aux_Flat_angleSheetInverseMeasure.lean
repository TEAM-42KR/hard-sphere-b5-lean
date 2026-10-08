import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_angleSheetInverseMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem HardSphereB5.SphericalCrofton.Aux.Flat.angleSheetInverseMeasure :
    ∀ (a b : ℝ) (hb : 0 < b), ((volume.restrict (Set.Ioo (a - b) (a + b))).withDensity
      (fun s => ENNReal.ofReal (1 / Real.sqrt (b ^ 2 - (s - a) ^ 2)))).map
        (fun s => Real.arccos ((a - s) / b)) =
    volume.restrict (Set.Ioo (0 : ℝ) Real.pi) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_angleSheetInverseMeasure
