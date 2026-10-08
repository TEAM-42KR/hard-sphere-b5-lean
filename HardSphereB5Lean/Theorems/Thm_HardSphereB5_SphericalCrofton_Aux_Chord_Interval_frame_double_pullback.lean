import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_double_pullback
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.frame_double_pullback :
    ∀ (E1 E2 p : Pt) (hE : Orthonormal ℝ ![E1,E2,p])
    (H : Pt → Pt → ENNReal) (hH : Measurable (Function.uncurry H)), (∫⁻ s in Set.Ioc 0 (2 * π), ∫⁻ t in Set.Ioc 0 (2 * π),
      H (circlePt 0 E1 E2 1 s) (circlePt 0 E1 E2 1 t)) =
    ∫⁻ u in greatCircle p, ∫⁻ v in greatCircle p, H u v ∂arcMeasure ∂arcMeasure :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_double_pullback
