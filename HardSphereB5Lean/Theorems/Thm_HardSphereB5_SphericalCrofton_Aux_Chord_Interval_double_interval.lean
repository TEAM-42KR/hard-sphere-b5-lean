import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_double_interval
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.double_interval :
    ∀ (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (hπ : L ≤ π), (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, (if (1 / 2 : ℝ) ≤ Real.cos (s - t) then ENNReal.ofReal (wK f (Real.cos (s - t))) else 0) * ENNReal.ofReal |Real.sin (s - t)|) = ENNReal.ofReal (kK f L) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_double_interval
