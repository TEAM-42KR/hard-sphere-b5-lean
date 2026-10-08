import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsCroftonMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton

theorem HardSphereB5.SphericalCrofton.Aux.Flat.bothSheetsCroftonMeasure :
    ∀ (X Y : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1),
    let μ := (volume.restrict {s : ℝ | 0 < Hpoly X Y s}).withDensity
      (fun s => ENNReal.ofReal (1 / Real.sqrt (Hpoly X Y s)))
    μ.map (fun s => chiPlus X Y s) + μ.map (fun s => -chiPlus X Y s) =
      volume.restrict (Set.Ioo (-Real.pi) Real.pi) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsCroftonMeasure
